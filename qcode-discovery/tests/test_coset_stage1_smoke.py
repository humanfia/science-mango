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


PROJECT = Path(__file__).resolve().parents[1]


def _write_smoke_inputs(tmp_path: Path) -> tuple[Path, Path]:
    seed = tmp_path / "coset_smoke_seed.py"
    seed.write_text(
        "from evolve.coset_seed_solution import "
        "generate_candidates as _base_generate\n\n"
        "# EVOLVE-BLOCK-START\n"
        "def _candidate_limit():\n"
        "    return 2\n"
        "# EVOLVE-BLOCK-END\n\n"
        "def generate_candidates():\n"
        "    return _base_generate(_candidate_limit())\n"
    )
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
    config_value["evaluator"]["timeout"] = 120
    config_value["database"]["population_size"] = 16
    config_value["database"]["archive_size"] = 8
    config_value["database"]["num_islands"] = 2
    config = tmp_path / "coset_smoke_config.yaml"
    config.write_text(yaml.safe_dump(config_value, sort_keys=False))
    return seed, config


def test_coset_launcher_completes_one_real_openevolve_iteration(tmp_path):
    requests = []
    replacement = "\n".join((
        "<" * 7 + " SEARCH",
        "def _candidate_limit():",
        "    return 2",
        "=" * 7,
        "def _candidate_limit():",
        "    return 3",
        ">" * 7 + " REPLACE",
    ))

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
            timeout=120,
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
                # Exercise the production round-6 failure lane plus normal
                # exception chaining: the diff applies cleanly, but the
                # resulting mutation raises only when the evaluator calls it.
                replacement = (
                    "<<<<<<< SEARCH\n"
                    "def _candidate_limit():\n"
                    "    return 2\n"
                    "=======\n"
                    "def _candidate_limit():\n"
                    "    try:\n"
                    "        raise ValueError('inner mutation failure')\n"
                    "    except ValueError as exc:\n"
                    "        raise NameError(\"name 'seeded_anchors' is not "
                    "defined\") from exc\n"
                    ">>>>>>> REPLACE"
                )
            else:
                if len(requests) == 2:
                    replacements = ((2, 3),)
                else:
                    # Resume may select either the seed or the successful
                    # child. Both alternatives produce a new program.
                    replacements = ((2, 4), (3, 4))
                replacement = "\n".join(
                    "<<<<<<< SEARCH\n"
                    "def _candidate_limit():\n"
                    f"    return {old_limit}\n"
                    "=======\n"
                    "def _candidate_limit():\n"
                    f"    return {new_limit}\n"
                    ">>>>>>> REPLACE"
                    for old_limit, new_limit in replacements
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
            timeout=120,
        )
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
            timeout=120,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)
        os.close(lease_fd)

    assert fresh.returncode == 0, fresh.stdout + "\n" + fresh.stderr
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
