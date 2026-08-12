from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import pwd
import select
import signal
import stat
import sys
import tempfile
import time
import unittest
import urllib.error
import urllib.request
from pathlib import Path


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_answer_blind_model_broker.py"
)
SPEC = importlib.util.spec_from_file_location("answer_blind_model_broker", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

LAUNCHER_SCRIPT = SCRIPT.with_name("run_answer_blind_iteration.py")
LAUNCHER_SPEC = importlib.util.spec_from_file_location(
    "answer_blind_iteration_for_broker_tests", LAUNCHER_SCRIPT
)
assert LAUNCHER_SPEC and LAUNCHER_SPEC.loader
LAUNCHER = importlib.util.module_from_spec(LAUNCHER_SPEC)
sys.modules[LAUNCHER_SPEC.name] = LAUNCHER
LAUNCHER_SPEC.loader.exec_module(LAUNCHER)


class AnswerBlindModelBrokerTests(unittest.TestCase):
    def test_protocol_is_exactly_shared_with_launcher(self):
        self.assertEqual(MODULE.PROTOCOL, LAUNCHER.PROTOCOL)

    def test_upstreams_and_paths_are_closed(self):
        gpt = MODULE._validate_upstream(
            "gpt", "https://chatgpt.com/backend-api/codex/responses"
        )
        kimi = MODULE._validate_upstream(
            "kimi-k3", "https://api.kimi.com/coding/"
        )
        self.assertEqual(
            MODULE._target_path("gpt", gpt, "/v1/responses"),
            "/backend-api/codex/responses",
        )
        self.assertEqual(
            MODULE._target_path("kimi-k3", kimi, "/v1/messages"),
            "/coding/v1/messages",
        )
        for bad in (
            "http://chatgpt.com/backend-api/codex/responses",
            "https://example.com/v1/responses",
            "https://user:secret@chatgpt.com/backend-api/codex/responses",
        ):
            with self.assertRaises(MODULE.BrokerError):
                MODULE._validate_upstream("gpt", bad)

    def test_token_loader_never_accepts_public_dummy_or_loose_permissions(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            credential = root / "token"
            credential.write_text("real-test-token\n", encoding="utf-8")
            credential.chmod(0o600)
            self.assertEqual(
                MODULE._load_token(
                    credential, token_format="raw", token_name=None
                ),
                "real-test-token",
            )
            credential.write_text(MODULE.PUBLIC_DUMMY_TOKEN, encoding="utf-8")
            with self.assertRaises(MODULE.BrokerError):
                MODULE._load_token(
                    credential, token_format="raw", token_name=None
                )
            credential.write_text("real-test-token", encoding="utf-8")
            credential.chmod(0o644)
            with self.assertRaises(MODULE.BrokerError):
                MODULE._load_token(
                    credential, token_format="raw", token_name=None
                )

    def test_provider_side_retrieval_and_remote_references_fail_closed(self):
        accepted = {
            "model": "gpt-5.6-sol",
            "input": "derive the result",
            "tools": [
                {
                    "type": "function",
                    "name": "local_lean_check",
                    "parameters": {"type": "object", "properties": {}},
                }
            ],
            "store": False,
        }
        MODULE._validate_provider_request(accepted, variant="gpt")
        MODULE._validate_provider_request(
            {**accepted, "tools": [{"type": "local_shell"}]}, variant="gpt"
        )
        rejected = (
            {**accepted, "tools": [{"type": "web_search_preview"}]},
            {**accepted, "tools": [{"type": "tool_search", "name": "search"}]},
            {**accepted, "tools": [{"type": "web_fetch_20260812", "name": "fetch"}]},
            {**accepted, "tools": [{"type": "code_execution_20260812", "name": "exec"}]},
            {**accepted, "input": [{"type": "input_image", "image_url": "https://example.test/a.png"}]},
            {**accepted, "previous_response_id": "resp_old"},
            {**accepted, "input": "https://example.test/answer"},
            {**accepted, "tools": [{"type": "mcp", "server_url": "https://example.test"}]},
        )
        for document in rejected:
            with self.subTest(document=document), self.assertRaises(MODULE.BrokerError):
                MODULE._validate_provider_request(document, variant="gpt")

        kimi_local = {
            "model": "kimi-k3[1m]",
            "messages": [{"role": "user", "content": "derive"}],
            "tools": [
                {
                    "name": "local_read",
                    "description": "read a problem-only file",
                    "input_schema": {"type": "object", "properties": {}},
                }
            ],
        }
        MODULE._validate_provider_request(kimi_local, variant="kimi-k3")
        for hosted_type in (
            "web_search_20250305",
            "web_fetch_20260812",
            "code_execution_20250825",
            "computer_20250124",
        ):
            with self.subTest(hosted_type=hosted_type), self.assertRaises(
                MODULE.BrokerError
            ):
                MODULE._validate_provider_request(
                    {
                        **kimi_local,
                        "tools": [
                            {
                                "type": hosted_type,
                                "name": "hosted",
                                "input_schema": {"type": "object"},
                            }
                        ],
                    },
                    variant="kimi-k3",
                )

    def test_strict_json_rejects_duplicate_keys_and_canonicalizes_forwarding(self):
        duplicate = b'{"model":"good","model":"bad","tools":[]}'
        with self.assertRaises(MODULE.BrokerError):
            MODULE._parse_provider_json(duplicate)
        with self.assertRaises(MODULE.BrokerError):
            MODULE._parse_provider_json(b'{"model":"gpt-5.6-sol","x":NaN}')

        document, canonical = MODULE._parse_provider_json(
            b'{ "tools" : [], "model" : "gpt-5.6-sol", "store" : false }'
        )
        self.assertEqual(document["model"], "gpt-5.6-sol")
        self.assertEqual(
            canonical,
            b'{"model":"gpt-5.6-sol","store":false,"tools":[]}',
        )

    def test_structured_profile_requires_no_tools_state_and_strict_schema(self):
        schema = {
            "type": "object",
            "properties": {"lean_source": {"type": "string"}},
            "required": ["lean_source"],
            "additionalProperties": False,
        }
        gpt = {
            "model": "gpt-5.6-sol",
            "store": False,
            "tools": [],
            "input": [
                {
                    "role": "user",
                    "content": [
                        {"type": "input_text", "text": "derive"},
                        {
                            "type": "input_image",
                            "image_url": "data:image/png;base64,aGVsbG8=",
                        },
                    ],
                }
            ],
            "text": {
                "format": {
                    "type": "json_schema",
                    "name": "answer_blind_submission",
                    "strict": True,
                    "schema": schema,
                }
            },
        }
        MODULE._validate_provider_request(
            gpt,
            variant="gpt",
            request_profile="tool_free_structured_solver_v1",
        )
        MODULE._validate_provider_request(
            gpt,
            variant="gpt",
            request_profile="tool_free_structured_independent_review_v1",
        )
        for invalid in (
            {**gpt, "tools": [{"type": "local_shell"}]},
            {**gpt, "previous_response_id": "resp-contaminated"},
            {**gpt, "store": True},
            {**gpt, "text": {}},
            {
                **gpt,
                "input": [
                    {
                        "role": "user",
                        "content": [
                            {
                                "type": "input_image",
                                "image_url": "https://example.test/answer.png",
                            }
                        ],
                    }
                ],
            },
        ):
            with self.subTest(invalid=invalid), self.assertRaises(MODULE.BrokerError):
                MODULE._validate_provider_request(
                    invalid,
                    variant="gpt",
                    request_profile="tool_free_structured_solver_v1",
                )

        kimi = {
            "model": "kimi-k3[1m]",
            "tools": [],
            "messages": [
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": "derive"},
                        {
                            "type": "image",
                            "source": {
                                "type": "base64",
                                "media_type": "image/png",
                                "data": "aGVsbG8=",
                            },
                        },
                    ],
                }
            ],
        }
        MODULE._validate_provider_request(
            kimi,
            variant="kimi-k3",
            request_profile="tool_free_structured_solver_v1",
        )
        MODULE._validate_provider_request(
            kimi,
            variant="kimi-k3",
            request_profile="tool_free_structured_independent_review_v1",
        )
        with self.assertRaises(MODULE.BrokerError):
            MODULE._validate_provider_request(
                {**kimi, "tools": [{"name": "local", "input_schema": {}}]},
                variant="kimi-k3",
                request_profile="tool_free_structured_solver_v1",
            )

    @unittest.skipUnless(os.geteuid() == 0, "controller lifecycle requires root")
    def test_root_supervisor_nonroot_worker_health_and_stopped_transcript(self):
        broker_user = "nobody"
        broker_uid = pwd.getpwnam(broker_user).pw_uid
        with tempfile.TemporaryDirectory(prefix="blind-broker-test.") as raw:
            root = Path(raw)
            controller = root / "controller"
            controller.mkdir(mode=0o700)
            controller.chmod(0o700)
            credential = root / "credential"
            credential.write_text("test-only-not-a-provider-key\n", encoding="utf-8")
            credential.chmod(0o600)
            result = MODULE.start_broker(
                controller_dir=controller,
                variant="gpt",
                run_id="unit-test-run",
                model="gpt-5.6-sol",
                upstream="https://chatgpt.com/backend-api/codex/responses",
                credential_file=credential,
                credential_format="raw",
                token_name=None,
                broker_user=broker_user,
                port=0,
            )
            ready_path = Path(result["ready"])
            try:
                ready = json.loads(ready_path.read_text(encoding="utf-8"))
                self.assertEqual(set(ready), MODULE.READY_FIELDS)
                self.assertEqual(ready["broker_uid"], broker_uid)
                self.assertEqual(stat.S_IMODE(ready_path.stat().st_mode), 0o400)
                request = urllib.request.Request(
                    ready["listen_url"].removesuffix("/v1")
                    + "/__answer_blind_health",
                    headers={
                        "Authorization": f"Bearer {MODULE.PUBLIC_DUMMY_TOKEN}"
                    },
                )
                with urllib.request.urlopen(request, timeout=5) as response:
                    health = json.loads(response.read())
                self.assertEqual(health["allowed_model"], "gpt-5.6-sol")
                self.assertEqual(health["run_id"], "unit-test-run")

                state = json.loads(
                    (controller / "gpt-model-broker-state.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertGreater(state["supervisor_start_ticks"], 0)
                self.assertEqual(state["lease_parent_pid"], os.getpid())
                self.assertGreater(state["lease_parent_start_ticks"], 0)
                # stop_broker pins this exact process with pidfd before
                # signalling; the recorded identity must still be live here.
                supervisor_pidfd = os.pidfd_open(state["supervisor_pid"])
                os.close(supervisor_pidfd)
                worker_status = Path(f"/proc/{state['worker_pid']}/status").read_text()
                self.assertIn("NoNewPrivs:\t0", worker_status)
                # Dumpable=0 makes a different process unable to inspect the
                # credential-holding worker environment.
                with self.assertRaises(PermissionError):
                    Path(f"/proc/{state['worker_pid']}/environ").read_bytes()

                wrong = urllib.request.Request(
                    ready["listen_url"].removesuffix("/v1")
                    + "/__answer_blind_health"
                )
                with self.assertRaises(urllib.error.HTTPError) as caught:
                    urllib.request.urlopen(wrong, timeout=5)
                self.assertEqual(caught.exception.code, 404)
            finally:
                transcript_path = MODULE.stop_broker(
                    controller_dir=controller, variant="gpt", timeout_s=10
                )
            transcript = json.loads(transcript_path.read_text(encoding="utf-8"))
            self.assertEqual(set(transcript), MODULE.TRANSCRIPT_FIELDS)
            self.assertTrue(transcript["broker_stopped"])
            self.assertEqual(transcript["request_count"], 0)
            self.assertEqual(transcript["request_response_chain_sha256"], "0" * 64)
            self.assertEqual(
                transcript["ready_receipt_sha256"],
                hashlib.sha256(ready_path.read_bytes()).hexdigest(),
            )

            state = json.loads(
                (controller / "gpt-model-broker-state.json").read_text(
                    encoding="utf-8"
                )
            )
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline and Path(
                f"/proc/{state['supervisor_pid']}"
            ).exists():
                time.sleep(0.05)
            # The supervisor can briefly remain as an adopted zombie, but the
            # worker carrying the credential must be gone.
            self.assertFalse(Path(f"/proc/{state['worker_pid']}").exists())

    @unittest.skipUnless(os.geteuid() == 0, "controller lifecycle requires root")
    def test_launcher_sigkill_cascades_to_credential_broker(self):
        """A crashed invocation may not leave the token proxy alive."""

        with tempfile.TemporaryDirectory(prefix="blind-broker-crash.") as raw:
            root = Path(raw)
            controller = root / "controller"
            controller.mkdir(mode=0o700)
            credential = root / "credential"
            credential.write_text("test-only-not-a-provider-key\n", encoding="utf-8")
            credential.chmod(0o600)
            read_fd, write_fd = os.pipe()
            launcher_pid = os.fork()
            if launcher_pid == 0:
                os.close(read_fd)
                try:
                    result = MODULE.start_broker(
                        controller_dir=controller,
                        variant="gpt",
                        run_id="crash-test-run",
                        model="gpt-5.6-sol",
                        upstream="https://chatgpt.com/backend-api/codex/responses",
                        credential_file=credential,
                        credential_format="raw",
                        token_name=None,
                        broker_user="nobody",
                        port=0,
                    )
                    os.write(write_fd, (json.dumps(result) + "\n").encode())
                    while True:
                        signal.pause()
                finally:
                    os._exit(0)
            os.close(write_fd)
            payload = b""
            deadline = time.monotonic() + 10
            while b"\n" not in payload and time.monotonic() < deadline:
                readable, _, _ = select.select([read_fd], [], [], 0.25)
                if readable:
                    payload += os.read(read_fd, 8192)
            os.close(read_fd)
            self.assertIn(b"\n", payload)
            state = json.loads(
                (controller / "gpt-model-broker-state.json").read_text(
                    encoding="utf-8"
                )
            )
            os.kill(launcher_pid, signal.SIGKILL)
            os.waitpid(launcher_pid, 0)
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                worker_status = Path(f"/proc/{state['worker_pid']}/status")
                worker_alive = worker_status.exists() and "State:\tZ" not in worker_status.read_text()
                supervisor_status = Path(
                    f"/proc/{state['supervisor_pid']}/status"
                )
                supervisor_alive = supervisor_status.exists() and "State:\tZ" not in supervisor_status.read_text()
                if not worker_alive and not supervisor_alive:
                    break
                time.sleep(0.05)
            worker_status = Path(f"/proc/{state['worker_pid']}/status")
            if worker_status.exists():
                self.assertIn("State:\tZ", worker_status.read_text())
            supervisor_status = Path(f"/proc/{state['supervisor_pid']}/status")
            if supervisor_status.exists():
                self.assertIn("State:\tZ", supervisor_status.read_text())


if __name__ == "__main__":
    unittest.main()
