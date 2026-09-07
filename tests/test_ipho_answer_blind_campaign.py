from __future__ import annotations

import argparse
import importlib.util
import json
import stat
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_ipho_answer_blind_campaign.py"
)
SPEC = importlib.util.spec_from_file_location("ipho_campaign", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IphoCampaignControllerTests(unittest.TestCase):
    def _args(self, root: Path, **updates: object) -> argparse.Namespace:
        values: dict[str, object] = {
            "credential_file": root / "provider-token",
            "credential_format": "raw",
            "token_name": None,
            "controller_dir": root / "controller",
            "workspace": root / "workspace",
            "dependency_root": root / "dependencies",
            "runtime_root": root / "runtime",
            "solver_user": "solver-user",
            "private_home": root / "private-home",
            "private_tmp": root / "private-tmp",
            "run_id": "ipho-run-1",
            "lean_explore_cache": root / "lean-explore",
            "lean_explore_hf_cache": root / "lean-explore-hf",
            "lean_explore_site_packages": None,
            "max_iterations": 3,
            "max_parallel": 2,
            "max_objectives": 7,
            "timeout_s": 60,
            "smoke_request": False,
            "smoke_timeout_s": 5,
            "broker_stop_timeout_s": 9,
        }
        values.update(updates)
        controller = Path(values["controller_dir"])
        controller.mkdir(mode=0o700)
        return argparse.Namespace(**values)

    def _ready(self, args: argparse.Namespace, *, listen_url: str) -> Path:
        path = args.controller_dir / f"{MODULE.VARIANT}-model-broker-ready.json"
        path.write_text(
            json.dumps(
                {
                    "phase": "model_broker_ready",
                    "variant": MODULE.VARIANT,
                    "run_id": args.run_id,
                    "allowed_model": MODULE.MODEL,
                    "upstream_origin": MODULE.UPSTREAM,
                    "request_profile": MODULE.REQUEST_PROFILE,
                    "listen_url": listen_url,
                }
            ),
            encoding="utf-8",
        )
        return path

    def test_one_parent_starts_runs_with_public_env_and_stops(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = self._args(root, smoke_request=True)
            events: list[object] = []

            def start_broker(**kwargs: object) -> dict[str, object]:
                events.append(("start", kwargs))
                ready = self._ready(args, listen_url="http://127.0.0.1:39421")
                return {"ok": True, "ready": str(ready), "sha256": "unused"}

            def loop_run(loop_args: argparse.Namespace):
                events.append("run")
                self.assertEqual(loop_args.broker_ready.name, "kimi-k3-model-broker-ready.json")
                self.assertEqual(stat.S_IMODE(loop_args.broker_env.stat().st_mode), 0o600)
                self.assertEqual(
                    loop_args.lean_explore_hf_cache, args.lean_explore_hf_cache
                )
                self.assertEqual(
                    loop_args.broker_env.read_text(encoding="utf-8").splitlines(),
                    [
                        "ANTHROPIC_BASE_URL=http://127.0.0.1:39421",
                        f"ANTHROPIC_AUTH_TOKEN={MODULE.DUMMY_TOKEN}",
                    ],
                )
                self.assertNotIn("real", loop_args.broker_env.read_text(encoding="utf-8"))
                return {"run_id": loop_args.run_id}, 0

            broker = SimpleNamespace(
                http=SimpleNamespace(
                    client=SimpleNamespace(HTTPSConnection=object)
                ),
                start_broker=start_broker,
                stop_broker=lambda **kwargs: events.append(("stop", kwargs)),
            )
            loop = SimpleNamespace(run=loop_run)
            with (
                mock.patch.object(MODULE, "_load_pinned_modules", return_value=(broker, loop)),
                mock.patch.object(
                    MODULE,
                    "_smoke_request",
                    side_effect=lambda url, **kwargs: events.append(("smoke", url, kwargs)),
                ),
            ):
                result, exit_code = MODULE.run(args)

            self.assertEqual(exit_code, 0)
            self.assertTrue(result["broker_smoke_request"])
            self.assertEqual([item if isinstance(item, str) else item[0] for item in events], ["start", "smoke", "run", "stop"])
            start_kwargs = events[0][1]
            self.assertEqual(start_kwargs["credential_file"], args.credential_file)
            self.assertEqual(start_kwargs["upstream"], MODULE.UPSTREAM)
            self.assertEqual(start_kwargs["model"], MODULE.MODEL)
            self.assertEqual(start_kwargs["variant"], MODULE.VARIANT)
            self.assertEqual(start_kwargs["broker_user"], MODULE.BROKER_USER)
            self.assertEqual(start_kwargs["port"], 0)

    def test_finally_stops_broker_when_confined_loop_raises(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = self._args(root)
            stopped: list[dict[str, object]] = []
            ready = self._ready(args, listen_url="http://127.0.0.1:40123")
            broker = SimpleNamespace(
                http=SimpleNamespace(
                    client=SimpleNamespace(HTTPSConnection=object)
                ),
                start_broker=lambda **kwargs: {"ok": True, "ready": str(ready)},
                stop_broker=lambda **kwargs: stopped.append(kwargs),
            )
            loop = SimpleNamespace(run=mock.Mock(side_effect=RuntimeError("loop failed")))
            with mock.patch.object(
                MODULE, "_load_pinned_modules", return_value=(broker, loop)
            ):
                with self.assertRaisesRegex(RuntimeError, "loop failed"):
                    MODULE.run(args)
            self.assertEqual(
                stopped,
                [
                    {
                        "controller_dir": args.controller_dir,
                        "variant": MODULE.VARIANT,
                        "timeout_s": args.broker_stop_timeout_s,
                    }
                ],
            )

    def test_non_loopback_receipt_fails_closed_and_stops(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = self._args(root)
            stopped: list[bool] = []
            ready = self._ready(args, listen_url="https://api.unipatai.com")
            broker = SimpleNamespace(
                http=SimpleNamespace(
                    client=SimpleNamespace(HTTPSConnection=object)
                ),
                start_broker=lambda **kwargs: {"ok": True, "ready": str(ready)},
                stop_broker=lambda **kwargs: stopped.append(True),
            )
            loop = SimpleNamespace(run=mock.Mock())
            with mock.patch.object(
                MODULE, "_load_pinned_modules", return_value=(broker, loop)
            ):
                with self.assertRaisesRegex(MODULE.CampaignError, "loopback"):
                    MODULE.run(args)
            loop.run.assert_not_called()
            self.assertEqual(stopped, [True])

    def test_broker_import_is_pinned_to_requested_overlay(self):
        self.assertEqual(
            MODULE.BROKER_SCRIPT,
            Path(
                "/root/icho-answer-blind-overlay-49360f26-univ-kimi-k3/"
                "scripts/run_answer_blind_model_broker.py"
            ),
        )

    def test_broker_retries_only_429_with_same_body(self):
        responses = [
            SimpleNamespace(
                status=429,
                getheader=lambda name: "2" if name == "Retry-After" else None,
                read=mock.Mock(return_value=b"limited"),
                close=mock.Mock(),
            ),
            SimpleNamespace(
                status=429,
                getheader=lambda _name: None,
                read=mock.Mock(return_value=b"limited"),
                close=mock.Mock(),
            ),
            SimpleNamespace(status=200),
        ]
        requests: list[tuple[object, ...]] = []

        class FakeHTTPSConnection:
            def __init__(self, *args: object, **kwargs: object) -> None:
                self.args = args
                self.kwargs = kwargs

            def request(self, *args: object, **kwargs: object) -> None:
                requests.append((self.args, self.kwargs, args, kwargs))

            def getresponse(self):
                return responses.pop(0)

            def close(self) -> None:
                pass

        client = SimpleNamespace(HTTPSConnection=FakeHTTPSConnection)
        broker = SimpleNamespace(http=SimpleNamespace(client=client))
        with (
            mock.patch.object(MODULE.time, "sleep") as sleep,
            mock.patch.object(MODULE.random, "random", return_value=0.0),
        ):
            restore = MODULE._install_broker_429_retry(broker)
            connection = broker.http.client.HTTPSConnection(
                "api.example", port=443, timeout=9
            )
            connection.request(
                "POST",
                "/v1/messages",
                body=b"same-body",
                headers={"x": "y"},
            )
            response = connection.getresponse()
            restore()

        self.assertEqual(response.status, 200)
        self.assertIs(broker.http.client, client)
        self.assertIs(client.HTTPSConnection, FakeHTTPSConnection)
        self.assertEqual(len(requests), 3)
        self.assertEqual(
            [entry[2][0:2] for entry in requests],
            [("POST", "/v1/messages")] * 3,
        )
        self.assertEqual(
            [entry[3]["body"] for entry in requests],
            [b"same-body"] * 3,
        )
        self.assertEqual(
            [call.args[0] for call in sleep.call_args_list],
            [2.0, 15.0],
        )

    def test_retry_proxy_does_not_replace_python_http_global(self):
        original = MODULE.http.client.HTTPSConnection
        broker = SimpleNamespace(http=MODULE.http)
        restore = MODULE._install_broker_429_retry(broker)
        self.assertIs(MODULE.http.client.HTTPSConnection, original)
        connection = broker.http.client.HTTPSConnection(
            "api.example", port=443, timeout=1
        )
        self.assertIsInstance(connection._connection, original)
        connection.close()
        restore()
        self.assertIs(broker.http, MODULE.http)


if __name__ == "__main__":
    unittest.main()
