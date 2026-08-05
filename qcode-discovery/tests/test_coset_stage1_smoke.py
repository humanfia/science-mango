"""One-iteration process smoke test for the whitelisted coset evaluator route."""

from __future__ import annotations

import json
import fcntl
import os
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import yaml

from evolve import coset_policy_dsl as policy_dsl


PROJECT = Path(__file__).resolve().parents[1]


def _policy_text() -> str:
    canonical = policy_dsl.canonical_policy_json(
        policy_dsl.default_policy()
    )
    policy = policy_dsl.parse_policy(canonical)
    assert len(policy_dsl.render_candidates(policy)) == 384
    return json.dumps(
        policy_dsl.policy_document(policy),
        sort_keys=True,
        indent=2,
    ) + "\n"


def _diff_block(search: str, replacement: str) -> str:
    return (
        "<<<<<<< SEARCH\n"
        f"{search}\n"
        "=======\n"
        f"{replacement}\n"
        ">>>>>>> REPLACE"
    )


def _walk_offset(delta: int = 0) -> int:
    document = policy_dsl.policy_document(policy_dsl.default_policy())
    return int(document["actions"][0]["walk"]["offset"]) + delta


def _walk_offset_replacement(old_delta: int, new_delta: int) -> str:
    return _diff_block(
        f'        "offset": {_walk_offset(old_delta)},',
        f'        "offset": {_walk_offset(new_delta)},',
    )


def _write_smoke_inputs(tmp_path: Path) -> tuple[Path, Path]:
    seed = tmp_path / "coset_smoke_seed.json"
    seed.write_text(_policy_text())
    config_value = yaml.safe_load(
        (PROJECT / "evolve/coset_config.yaml").read_text()
    )
    config_value.pop("qcode_coset_search_portfolio", None)
    config_value["max_iterations"] = 2
    config_value["checkpoint_interval"] = 1
    config_value["llm"]["models"] = [{
        "name": "coset-smoke-model",
        "weight": 1.0,
        "temperature": 0.0,
    }]
    config_value["llm"]["timeout"] = 10
    config_value["llm"]["retries"] = 0
    config_value["evaluator"]["parallel_evaluations"] = 1
    config_value["evaluator"]["timeout"] = 300
    config_value["database"]["population_size"] = 16
    config_value["database"]["archive_size"] = 8
    config_value["database"]["num_islands"] = 2
    config = tmp_path / "coset_smoke_config.yaml"
    config.write_text(yaml.safe_dump(config_value, sort_keys=False))
    return seed, config


def test_coset_launcher_completes_one_real_openevolve_iteration(tmp_path):
    requests = []
    replacement = _walk_offset_replacement(0, 1)

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):  # noqa: N802 - BaseHTTPRequestHandler API
            length = int(self.headers.get("Content-Length", "0"))
            requests.append(json.loads(self.rfile.read(length)))
            payload = json.dumps({
                "id": "coset-smoke",
                "object": "chat.completion",
                "created": int(time.time()),
                "model": "coset-smoke-model",
                "choices": [{
                    "index": 0,
                    "message": {"role": "assistant", "content": replacement},
                    "finish_reason": "stop",
                }],
                "usage": {
                    "prompt_tokens": 1,
                    "completion_tokens": 1,
                    "total_tokens": 2,
                },
            }).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def log_message(self, _format, *_args):
            return

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        seed, config = _write_smoke_inputs(tmp_path)
        output = tmp_path / "output"
        environment = dict(os.environ)
        environment["OPENAI_API_KEY"] = "coset-smoke-key"
        completed = subprocess.run(
            [
                sys.executable,
                str(PROJECT / "evolve/run_evolution.py"),
                "--evaluator",
                "coset-two-block",
                "--config",
                str(config),
                "--seed",
                str(seed),
                "--output",
                str(output),
                "--iterations",
                "1",
                "--models",
                "coset-smoke-model",
                "--api-base",
                f"http://127.0.0.1:{server.server_port}/v1",
                "--max-parallel-evaluations",
                "1",
                "--no-temperature",
            ],
            cwd=PROJECT,
            env=environment,
            capture_output=True,
            text=True,
            timeout=300,
        )
        wrong_resume = subprocess.run(
            [
                sys.executable,
                str(PROJECT / "evolve/run_evolution.py"),
                "--evaluator",
                "default",
                "--config",
                str(config),
                "--seed",
                str(seed),
                "--output",
                str(tmp_path / "wrong-evaluator-output"),
                "--resume",
                str(output / "checkpoints/checkpoint_1"),
                "--iterations",
                "1",
                "--models",
                "coset-smoke-model",
                "--api-base",
                f"http://127.0.0.1:{server.server_port}/v1",
                "--max-parallel-evaluations",
                "1",
                "--no-temperature",
            ],
            cwd=PROJECT,
            env=environment,
            capture_output=True,
            text=True,
            timeout=60,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)

    assert completed.returncode == 0, completed.stdout + "\n" + completed.stderr
    assert requests
    assert "Coset mode: using coset_openevolve_evaluator.py" in completed.stdout
    assert "Evolution complete!" in completed.stdout
    assert (output / "checkpoints/checkpoint_1/metadata.json").is_file()
    assert (output / "all_codes.jsonl").is_file()
    rows = [
        json.loads(line)
        for line in (output / "all_codes.jsonl").read_text().splitlines()
    ]
    assert rows
    assert all(row["construction"]["kind"] == "coset-two-block-v1" for row in rows)
    assert wrong_resume.returncode != 0
    assert "not default" in (wrong_resume.stdout + wrong_resume.stderr)


def test_managed_coset_fresh_and_resume_bind_action_preflight(tmp_path):
    requests = []

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):  # noqa: N802 - BaseHTTPRequestHandler API
            length = int(self.headers.get("Content-Length", "0"))
            requests.append(json.loads(self.rfile.read(length)))
            if len(requests) == 1:
                # Exercise the production failure lane with a diff that
                # applies cleanly but violates the strict data-only schema.
                replacement = _diff_block(
                    '  "candidate_limit": 384,',
                    '  "candidate_limit": "seeded_anchors",',
                )
            else:
                if len(requests) == 2:
                    replacements = ((0, 1),)
                else:
                    # Resume may select either the seed or the successful
                    # child. Both alternatives produce a new program.
                    replacements = ((0, 2), (1, 2))
                replacement = "\n".join(
                    _walk_offset_replacement(old_delta, new_delta)
                    for old_delta, new_delta in replacements
                )
            payload = json.dumps({
                "id": f"coset-managed-smoke-{len(requests)}",
                "object": "chat.completion",
                "created": int(time.time()),
                "model": "coset-smoke-model",
                "choices": [{
                    "index": 0,
                    "message": {"role": "assistant", "content": replacement},
                    "finish_reason": "stop",
                }],
                "usage": {
                    "prompt_tokens": 1,
                    "completion_tokens": 1,
                    "total_tokens": 2,
                },
            }).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def log_message(self, _format, *_args):
            return

    seed, config = _write_smoke_inputs(tmp_path)
    context = tmp_path / "humanize-context.md"
    context.write_text("coset managed smoke\n")
    lease_path = (tmp_path / "lifecycle.lock").resolve()
    lease_fd = os.open(lease_path, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(lease_fd, fcntl.LOCK_EX)
    os.set_inheritable(lease_fd, True)
    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    output = tmp_path / "managed-output"
    environment = dict(os.environ)
    environment["OPENAI_API_KEY"] = "coset-smoke-key"
    environment["ENABLE_ARTIFACTS"] = "false"

    def managed_command(
        *,
        iteration: int,
        iterations: int,
        offset: int,
        resume: Path | None,
    ):
        command = [
            sys.executable,
            str(PROJECT / "evolve/run_evolution.py"),
            "--evaluator",
            "coset-two-block",
            "--config",
            str(config),
            "--seed",
            str(seed),
            "--output",
            str(output),
            "--iterations",
            str(iterations),
            "--models",
            "coset-smoke-model",
            "--api-base",
            f"http://127.0.0.1:{server.server_port}/v1",
            "--max-parallel-evaluations",
            "1",
            "--no-temperature",
            "--humanize-context",
            str(context),
            "--completion-marker",
            str(tmp_path / f"completion-{iteration}.json"),
            "--slice-witness",
            str(tmp_path / f"witness-{iteration}.json"),
            "--candidate-start-offset",
            str(offset),
            "--lifecycle-lease-fd",
            str(lease_fd),
            "--lifecycle-lease-path",
            str(lease_path),
        ]
        if resume is not None:
            command.extend(["--resume", str(resume)])
        return command

    try:
        fresh = subprocess.run(
            managed_command(
                iteration=1,
                iterations=2,
                offset=0,
                resume=None,
            ),
            cwd=PROJECT,
            env=environment,
            pass_fds=(lease_fd,),
            capture_output=True,
            text=True,
            timeout=300,
        )
        assert fresh.returncode == 0, fresh.stdout + "\n" + fresh.stderr
        witness_one = json.loads((tmp_path / "witness-1.json").read_text())
        resume = subprocess.run(
            managed_command(
                iteration=2,
                iterations=1,
                offset=witness_one["candidate_end_offset"],
                resume=output / "checkpoints/checkpoint_2",
            ),
            cwd=PROJECT,
            env=environment,
            pass_fds=(lease_fd,),
            capture_output=True,
            text=True,
            timeout=300,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)
        os.close(lease_fd)

    assert resume.returncode == 0, resume.stdout + "\n" + resume.stderr
    assert len(requests) == 3
    witness_two = json.loads((tmp_path / "witness-2.json").read_text())
    assert witness_one["base_last_iteration"] == 0
    assert witness_one["result_last_iteration"] == 2
    assert witness_one["successful_evaluations"] == 1
    assert witness_one["worker_errors"] == 1
    assert [item["status"] for item in witness_one["outcomes"]] == [
        "worker_error",
        "program_added",
    ]
    for witness in (witness_one, witness_two):
        assert witness["qcode_evaluator_kind"] == "coset-two-block"
        assert len(witness["qcode_action_catalog_sha256"]) == 64
        assert "coset_action_catalog_parser_sha256" in witness
        assert "coset_action_catalog_sha256" in witness
    assert witness_two["base_last_iteration"] == 2
    assert witness_two["result_last_iteration"] == 3
    combined_output = (
        fresh.stdout + fresh.stderr + resume.stdout + resume.stderr
    )
    assert "Feature dimension" not in combined_output
    assert "was not integrated" not in combined_output

    checkpoint_programs = output / "checkpoints/checkpoint_3/programs"
    for path in sorted(checkpoint_programs.glob("*.json")):
        metrics = json.loads(path.read_text())["metrics"]
        assert "winner_preflight_lattices" not in metrics
        assert metrics["winner_preflight_unit_kind_id"] == 1.0
        assert metrics["winner_preflight_units"] == 2.0
        assert metrics["winner_preflight_action_strata"] == 2.0
