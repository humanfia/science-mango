"""One-iteration process smoke test for the whitelisted coset evaluator route."""

from __future__ import annotations

import copy
import json
import hashlib
import fcntl
import os
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import yaml
import pytest

from evolve import coset_policy_dsl as policy_dsl
from evolve import coset_policy_dsl_v3 as policy_dsl_v3
from evolve import run_evolution as launcher
from evolve.coset_negative_archive import materialize_feedback_snapshot
from evolve.coset_policy_dispatch import parse_and_render_registered_policy


PROJECT = Path(__file__).resolve().parents[1]
PRODUCTION_EVALUATOR_TIMEOUT_S = 1200
REAL_PROOF_SMOKE_TIMEOUT_S = 2 * PRODUCTION_EVALUATOR_TIMEOUT_S + 300


def test_coset_literal_diff_changes_the_typed_policy_and_candidate_pool():
    parent = _policy_text()
    old_offset = _walk_offset()
    response = _diff_block(
        f'        "offset": {old_offset},',
        f'        "offset": {old_offset + 1},',
    )

    child = launcher._apply_coset_literal_diff(parent, response)
    parent_policy = policy_dsl.parse_policy(parent)
    child_policy = policy_dsl.parse_policy(child)

    assert child != parent
    assert policy_dsl.policy_digest(child_policy) != (
        policy_dsl.policy_digest(parent_policy)
    )
    assert {
        policy_dsl.candidate_digest(candidate)
        for candidate in policy_dsl.render_candidates(child_policy)
    } != {
        policy_dsl.candidate_digest(candidate)
        for candidate in policy_dsl.render_candidates(parent_policy)
    }


@pytest.mark.parametrize(
    ("search", "replacement", "expected_kind"),
    [
        ('"missing": 1', '"missing": 2', "no_effect_mutation"),
        ('"enabled": true', '"enabled": false', "invalid_mutation"),
        (
            '"candidate_limit": 384',
            '"candidate_limit": 384',
            "no_effect_mutation",
        ),
    ],
)
def test_coset_literal_diff_rejects_unapplied_ambiguous_and_noop_blocks(
    search: str,
    replacement: str,
    expected_kind: str,
):
    parent = _policy_text()
    with pytest.raises(ValueError) as captured:
        launcher._apply_coset_literal_diff(
            parent,
            _diff_block(search, replacement),
        )
    assert launcher._recognized_coset_mutation_rejection(
        str(captured.value),
        expected_parent_code_sha256=hashlib.sha256(
            parent.encode("utf-8")
        ).hexdigest(),
    ) == expected_kind
    assert launcher._recognized_coset_mutation_rejection(
        str(captured.value),
        expected_parent_code_sha256="0" * 64,
    ) is None


def test_coset_mutation_prompt_has_source_bound_integer_ranges():
    prompt = launcher._coset_mutation_bounds_prompt()

    assert (
        "action_id=coset2bga-l120-m32-s3-degree60-v2: "
        "left indices 0..118; right indices 0..28; walk offset "
        "0..2850525; walk stride 1..2850525, "
        "gcd(stride,2850526)=1."
    ) in prompt
    assert "left indices 0..222; right indices 0..26" in prompt
    assert "gcd(stride,8688303)=1" in prompt
    assert "left indices 0..70; right indices 0..70" in prompt
    assert "gcd(stride,6175225)=1" in prompt
    assert "keep actions in ascending action_id order" in prompt
    assert "left and right indices must be strictly increasing" in prompt
    assert "strictly lexicographically increasing by (left,right)" in prompt
    assert "rejects noncanonical ordering instead of repairing it" in prompt


def _compact_json(value) -> str:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )


def _v3_three_plus_two_parent() -> str:
    return policy_dsl_v3.canonical_policy_json(
        policy_dsl_v3.default_policy(support_split=(3, 2))
    ) + "\n"


def _replace_v3_action(parent: str, action_index: int, replacement: dict) -> str:
    document = json.loads(parent)
    return _diff_block(
        _compact_json(document["actions"][action_index]),
        _compact_json(replacement),
    )


def _mutation_rejection_payload(error: ValueError) -> dict:
    encoded = str(error)
    assert encoded.startswith(launcher.COSET_MUTATION_REJECTION_PREFIX)
    return json.loads(
        encoded[len(launcher.COSET_MUTATION_REJECTION_PREFIX):]
    )


def test_v3_three_plus_two_unsorted_supports_fail_closed_but_sorted_accepts():
    parent = _v3_three_plus_two_parent()
    assert hashlib.sha256(parent.encode()).hexdigest() == (
        "60e5d61b3b201ff6ac0386bc00661b5c35aca1423c6bf8392eabf921902cbd46"
    )
    action = json.loads(parent)["actions"][0]
    rejection_payloads = []
    for left in ([1, 0], [2, 0]):
        replacement = copy.deepcopy(action)
        replacement["supports"] = [{"left": left, "right": [0]}]
        with pytest.raises(ValueError) as captured:
            launcher._apply_coset_literal_diff(
                parent,
                _replace_v3_action(parent, 0, replacement),
            )
        assert launcher._recognized_coset_mutation_rejection(
            str(captured.value),
            expected_parent_code_sha256=hashlib.sha256(
                parent.encode()
            ).hexdigest(),
        ) == "invalid_mutation"
        payload = _mutation_rejection_payload(captured.value)
        assert payload["reason"] == "dsl_noncanonical"
        rejection_payloads.append(payload)
    # The raw responses are deliberately not persisted, but their bounded
    # identities now make distinct invalid outputs distinguishable.
    assert rejection_payloads[0]["detail_sha256"] != (
        rejection_payloads[1]["detail_sha256"]
    )

    replacement = copy.deepcopy(action)
    replacement["supports"] = [{"left": [0, 1], "right": [0]}]
    child = launcher._apply_coset_literal_diff(
        parent,
        _replace_v3_action(parent, 0, replacement),
    )
    rendered = parse_and_render_registered_policy(child)
    assert rendered.document["actions"][0]["supports"] == [
        {"left": [0, 1], "right": [0]}
    ]


def test_v3_noncanonical_support_action_lists_and_nonroot_parent_reject():
    parent = _v3_three_plus_two_parent()
    document = json.loads(parent)
    first_action = document["actions"][0]

    reversed_supports = copy.deepcopy(first_action)
    reversed_supports["supports"] = [
        {"left": [0, 2], "right": [0]},
        {"left": [0, 1], "right": [0]},
    ]
    responses = [_replace_v3_action(parent, 0, reversed_supports)]

    first = _compact_json(document["actions"][0])
    second = _compact_json(document["actions"][1])
    responses.append(_diff_block(
        f'"actions":[{first},{second},',
        f'"actions":[{second},{first},',
    ))
    for response in responses:
        with pytest.raises(ValueError) as captured:
            launcher._apply_coset_literal_diff(parent, response)
        assert _mutation_rejection_payload(captured.value)["reason"] == (
            "dsl_noncanonical"
        )

    # The same invariant applies to a non-root parent that already contains a
    # valid explicit support, matching the later-round failure mode.
    canonical_action = copy.deepcopy(first_action)
    canonical_action["supports"] = [{"left": [0, 1], "right": [0]}]
    nonroot = launcher._apply_coset_literal_diff(
        parent,
        _replace_v3_action(parent, 0, canonical_action),
    )
    with pytest.raises(ValueError) as captured:
        launcher._apply_coset_literal_diff(
            nonroot,
            _diff_block('"left":[0,1]', '"left":[1,0]'),
        )
    payload = _mutation_rejection_payload(captured.value)
    assert payload["reason"] == "dsl_noncanonical"
    assert payload["parent_code_sha256"] == hashlib.sha256(
        nonroot.encode()
    ).hexdigest()


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


def _current_program_from_request(request: dict) -> str:
    prompt = "\n".join(
        str(message.get("content", ""))
        for message in request.get("messages", [])
    )
    marker = "# Current Program\n```json\n"
    assert marker in prompt
    return prompt.split(marker, 1)[1].split("\n```\n", 1)[0]


def _write_smoke_inputs(
    tmp_path: Path,
    *,
    fixed_coset_portfolio: bool = False,
) -> tuple[Path, Path]:
    seed = tmp_path / "coset_smoke_seed.json"
    seed.write_text(_policy_text())
    config_value = yaml.safe_load(
        (PROJECT / "evolve/coset_config_v2.yaml").read_text()
    )
    if not fixed_coset_portfolio:
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
    # The production proof ladder has a 720-second batch wall.  Keep the
    # evaluator and its outer smoke-process bound strictly above that wall;
    # a 300-second test-only cap can kill healthy, actively progressing proof
    # work before the production contract has a chance to finish it.
    config_value["evaluator"]["timeout"] = PRODUCTION_EVALUATOR_TIMEOUT_S
    config_value["database"]["population_size"] = 16
    config_value["database"]["archive_size"] = 8
    config_value["database"]["num_islands"] = (
        4 if fixed_coset_portfolio else 2
    )
    config = tmp_path / "coset_smoke_config.yaml"
    config.write_text(yaml.safe_dump(config_value, sort_keys=False))
    return seed, config


def _negative_feedback_args(tmp_path: Path) -> list[str]:
    live = (tmp_path / "negative-feedback-live.json").resolve()
    snapshot = (tmp_path / "negative-feedback-snapshot.json").resolve()
    manifest_path = (
        tmp_path / "negative-feedback-snapshot-manifest.json"
    ).resolve()
    manifest = materialize_feedback_snapshot(
        live,
        snapshot,
        manifest_path,
        run_id="coset-stage1-smoke",
        round_number=1,
        feedback_epoch=1,
    )
    return [
        "--negative-feedback-live-archive",
        str(live),
        "--negative-feedback-snapshot",
        str(snapshot),
        "--negative-feedback-snapshot-sha256",
        manifest["snapshot_sha256"],
        "--negative-feedback-archive-sha256",
        manifest["archive_sha256"],
        "--negative-feedback-manifest",
        str(manifest_path),
        "--negative-feedback-manifest-sha256",
        hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
        "--negative-feedback-epoch",
        "1",
    ]


def test_coset_launcher_completes_one_real_openevolve_iteration(tmp_path):
    requests = []
    replacement = _walk_offset_replacement(0, 1)

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):  # noqa: N802 - BaseHTTPRequestHandler API
            length = int(self.headers.get("Content-Length", "0"))
            request = json.loads(self.rfile.read(length))
            requests.append(request)
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
            timeout=REAL_PROOF_SMOKE_TIMEOUT_S,
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
    assert all(row["construction"]["kind"] == "coset-two-block-v2" for row in rows)
    assert wrong_resume.returncode != 0
    assert "not default" in (wrong_resume.stdout + wrong_resume.stderr)


def test_managed_all_no_effect_mutations_save_unchanged_checkpoint(tmp_path):
    requests = []

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):  # noqa: N802 - BaseHTTPRequestHandler API
            length = int(self.headers.get("Content-Length", "0"))
            requests.append(json.loads(self.rfile.read(length)))
            response = _diff_block('"missing": 1', '"missing": 2')
            payload = json.dumps({
                "id": "coset-no-effect-smoke",
                "object": "chat.completion",
                "created": int(time.time()),
                "model": "coset-smoke-model",
                "choices": [{
                    "index": 0,
                    "message": {"role": "assistant", "content": response},
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

    seed, config = _write_smoke_inputs(
        tmp_path,
        fixed_coset_portfolio=True,
    )
    context = tmp_path / "humanize-context.md"
    context.write_text("coset no-effect smoke\n")
    lease_path = (tmp_path / "lifecycle.lock").resolve()
    lease_fd = os.open(lease_path, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(lease_fd, fcntl.LOCK_EX)
    os.set_inheritable(lease_fd, True)
    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    output = tmp_path / "no-effect-output"
    witness = tmp_path / "no-effect-witness.json"
    feedback_args = _negative_feedback_args(tmp_path)
    environment = dict(os.environ)
    environment["OPENAI_API_KEY"] = "coset-smoke-key"
    try:
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
                "--humanize-context",
                str(context),
                "--completion-marker",
                str(tmp_path / "no-effect-completion.json"),
                "--slice-witness",
                str(witness),
                "--candidate-start-offset",
                "0",
                "--lifecycle-lease-fd",
                str(lease_fd),
                "--lifecycle-lease-path",
                str(lease_path),
                *feedback_args,
            ],
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

    assert completed.returncode == 0, completed.stdout + "\n" + completed.stderr
    assert len(requests) == 1
    payload = json.loads(witness.read_text())
    assert payload["successful_evaluations"] == 0
    assert payload["worker_errors"] == 1
    assert payload["outcomes"] == [{
        "iteration": 1,
        "status": "worker_error",
        "error_sha256": payload["outcomes"][0]["error_sha256"],
        "error_bytes": payload["outcomes"][0]["error_bytes"],
        "error_kind": "no_effect_mutation",
    }]
    checkpoint_programs = list(
        (output / "checkpoints/checkpoint_1/programs").glob("*.json")
    )
    assert len(checkpoint_programs) == 1


def test_managed_coset_fresh_and_resume_bind_action_preflight(tmp_path):
    requests = []

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):  # noqa: N802 - BaseHTTPRequestHandler API
            length = int(self.headers.get("Content-Length", "0"))
            request = json.loads(self.rfile.read(length))
            requests.append(request)
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
                    replacement = "\n".join(
                        _walk_offset_replacement(old_delta, new_delta)
                        for old_delta, new_delta in replacements
                    )
                else:
                    current = json.loads(_current_program_from_request(request))
                    old_offset = int(current["actions"][0]["walk"]["offset"])
                    target_delta = len(requests) - 1
                    replacement = _diff_block(
                        f'        "offset": {old_offset},',
                        f'        "offset": {_walk_offset(target_delta)},',
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

    seed, config = _write_smoke_inputs(
        tmp_path,
        fixed_coset_portfolio=True,
    )
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
    feedback_args = _negative_feedback_args(tmp_path)

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
            *feedback_args,
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
            timeout=REAL_PROOF_SMOKE_TIMEOUT_S,
        )
        assert fresh.returncode == 0, fresh.stdout + "\n" + fresh.stderr
        witness_one = json.loads((tmp_path / "witness-1.json").read_text())
        resume = subprocess.run(
            managed_command(
                iteration=2,
                iterations=2,
                offset=witness_one["candidate_end_offset"],
                resume=output / "checkpoints/checkpoint_2",
            ),
            cwd=PROJECT,
            env=environment,
            pass_fds=(lease_fd,),
            capture_output=True,
            text=True,
            timeout=REAL_PROOF_SMOKE_TIMEOUT_S,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)
        os.close(lease_fd)

    assert resume.returncode == 0, resume.stdout + "\n" + resume.stderr
    assert len(requests) == 4
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
    assert witness_two["result_last_iteration"] == 4
    combined_output = (
        fresh.stdout + fresh.stderr + resume.stdout + resume.stderr
    )
    assert "Feature dimension" not in combined_output
    assert "was not integrated" not in combined_output

    checkpoint_programs = output / "checkpoints/checkpoint_4/programs"
    policy_digests = set()
    for path in sorted(checkpoint_programs.glob("*.json")):
        program = json.loads(path.read_text())
        metrics = program["metrics"]
        policy_digests.add(
            policy_dsl.policy_digest(policy_dsl.parse_policy(program["code"]))
        )
        assert "winner_preflight_lattices" not in metrics
        assert metrics["winner_preflight_unit_kind_id"] == 1.0
        assert metrics["winner_preflight_units"] == 46.0
        assert metrics["winner_preflight_action_strata"] == 46.0
    assert len(policy_digests) >= 4
    metadata = json.loads(
        (output / "checkpoints/checkpoint_4/metadata.json").read_text()
    )
    occupied_cells = {
        key
        for feature_map in metadata["island_feature_maps"]
        for key in feature_map
    }
    assert len(occupied_cells) >= 2
    assert all(metadata["island_feature_maps"])
