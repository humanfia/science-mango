from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path

import pytest

from scripts import paper400_native_lrat_future_v1 as native


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _json(path: Path, value: object) -> None:
    path.write_bytes(native.canonical_bytes(value) + b"\n")
    path.chmod(0o600)


@pytest.fixture
def world(tmp_path: Path) -> dict[str, object]:
    tools = tmp_path / "tools"
    inputs = tmp_path / "inputs"
    outputs = tmp_path / "outputs"
    records = tmp_path / "records"
    for directory in (tools, inputs, outputs, records):
        directory.mkdir(mode=0o700)
        directory.chmod(0o700)

    solver = tools / "cadical"
    solver.write_bytes(b"#!/bin/sh\necho fake-cadical\n")
    solver.chmod(0o700)
    checker = tools / "lrat-check"
    checker.write_bytes(b"#!/bin/sh\necho VERIFIED\n")
    checker.chmod(0o700)

    semantic_stdout_sha = hashlib.sha256(b"VERIFIED\n").hexdigest()
    audit_value = {
        "schema_version": 1,
        "kind": "cadical-rel-1.9.5-standalone-audit-v1",
        "status": "PASS",
        "build": {
            "generated_files": {
                "build/cadical": {
                    "bytes": solver.stat().st_size,
                    "sha256": _sha(solver),
                }
            }
        },
        "scope": {"n400_solver_invoked": False},
        "cli_audit": {
            "default_proof_format": "binary DRAT",
            "exit_codes": {"sat": 10, "unsat": 20, "unknown": 0},
            "version": {"returncode": 0, "stdout": "1.9.5"},
        },
        "upstream": {"commit_git_sha1": "1" * 40},
    }
    audit = tools / "standalone-audit-manifest.json"
    _json(audit, audit_value)
    policy_value = native.seal({
        "schema_version": 1,
        "kind": "paper400-trusted-checker-policy-v1",
        "checkers": {
            "lrat-check-v05.22.2023-gcc11.4.0-x86_64": {
                "argv_roles": ["binary", "dimacs", "proof"],
                "binary_sha256": _sha(checker),
                "checker_role": "lrat-check",
                "max_proof_bytes": 1 << 30,
                "proof_format": "lrat",
                "semantic_stdout_sha256": semantic_stdout_sha,
                "source_commit": "2" * 40,
                "timeout_s": 1234,
            }
        },
    }, "policy_sha256")
    internal_policy_sha = policy_value["policy_sha256"]
    policy = tools / "trusted-checker-policy.json"
    _json(policy, policy_value)
    pins = native.ToolchainPins(
        solver_path=solver,
        solver_sha256=_sha(solver),
        solver_version="1.9.5",
        solver_upstream_commit="1" * 40,
        audit_path=audit,
        audit_sha256=_sha(audit),
        lrat_checker_path=checker,
        lrat_checker_sha256=_sha(checker),
        lrat_checker_source_commit="2" * 40,
        trusted_policy_path=policy,
        trusted_policy_file_sha256=_sha(policy),
        trusted_policy_internal_sha256=internal_policy_sha,
        lrat_checker_semantic_stdout_sha256=semantic_stdout_sha,
        lrat_checker_timeout_seconds=1234,
        lrat_checker_max_proof_bytes=1 << 30,
    )

    cnf_a = inputs / "a.cnf"
    cnf_a.write_bytes(b"c leaf a\np cnf 2 2\n1 0\n-1 0\n")
    cnf_a.chmod(0o600)
    cnf_b = inputs / "b.cnf"
    cnf_b.write_bytes(b"p cnf 3 2\n1 2 0\n-1 0\n")
    cnf_b.chmod(0o600)

    spec = {
        "schema_version": 1,
        "kind": native.SPEC_KIND,
        "campaign_id": "paper400-future-test",
        "launch_id": "launch-001",
        "generation": 0,
        "fresh_leaf_generation": True,
        "resume": False,
        "checkpoint_source": None,
        "existing_proof_path": None,
        "existing_proof_format": None,
        "all_start_barrier": {
            "barrier_id": "barrier-001",
            "timeout_seconds": 90,
            "require_every_leaf": True,
        },
        "leaves": [
            {
                "leaf_id": "leaf-00",
                "cnf_path": str(cnf_a),
                "proof_output_path": str(outputs / "leaf-00.lrat"),
                "cpu_lease": {
                    "kind": native.CPU_LEASE_KIND,
                    "lease_id": "lease-00",
                    "lease_token_sha256": "a" * 64,
                    "catalog_record_sha256": "b" * 64,
                    "cpu": 7,
                    "generation": 0,
                    "exclusive": True,
                    "state": "RESERVED",
                },
            },
            {
                "leaf_id": "leaf-01",
                "cnf_path": str(cnf_b),
                "proof_output_path": str(outputs / "leaf-01.lrat"),
                "cpu_lease": {
                    "kind": native.CPU_LEASE_KIND,
                    "lease_id": "lease-01",
                    "lease_token_sha256": "c" * 64,
                    "catalog_record_sha256": "d" * 64,
                    "cpu": 8,
                    "generation": 0,
                    "exclusive": True,
                    "state": "RESERVED",
                },
            },
        ],
    }
    return {
        "tmp": tmp_path,
        "pins": pins,
        "spec": spec,
        "solver": solver,
        "checker": checker,
        "cnf_a": cnf_a,
        "outputs": outputs,
        "records": records,
    }


def _plan(world: dict[str, object]) -> dict[str, object]:
    return native.build_plan(
        world["spec"],  # type: ignore[arg-type]
        pins=world["pins"],  # type: ignore[arg-type]
    )


def _observation(plan: dict[str, object], leaf_id: str, pid: int) -> dict[str, object]:
    participant = next(
        item for item in plan["participants"]  # type: ignore[union-attr]
        if item["leaf_id"] == leaf_id
    )
    lease = participant["cpu_lease"]
    proof_path = Path(participant["proof_output"]["path"])
    if not proof_path.exists():
        descriptor = os.open(
            proof_path,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        os.close(descriptor)
    proof_binding, _ = native._bind_file(
        proof_path, role="exclusive-native-lrat-output", cap=0, executable=False,
    )
    return {
        "schema_version": 1,
        "kind": native.PREEXEC_OBSERVATION_KIND,
        "plan_sha256": plan["plan_sha256"],
        "leaf_id": leaf_id,
        "generation": 0,
        "pid": pid,
        "proc_start_ticks": 900000 + pid,
        "cpu": lease["cpu"],
        "lease_id": lease["lease_id"],
        "lease_token_sha256": lease["lease_token_sha256"],
        "planned_argv_sha256": participant["solver_invocation"]["argv_sha256"],
        "preexec_gate_held": True,
        "proof_fd": native.SOLVER_PROOF_FD,
        "proof_output_binding": proof_binding,
        "proof_fd_o_excl_anchor_held": True,
    }


def test_plan_pins_ascii_native_lrat_and_two_replays(world: dict[str, object]) -> None:
    plan = _plan(world)
    assert native.selfhash_valid(plan, "plan_sha256")
    assert plan["compatibility_gate"] == {
        "new_leaf_only": True,
        "generation": 0,
        "native_proof_format": "lrat",
        "solver_options": ["--lrat", "--no-binary"],
        "resume_permitted": False,
        "dmtcp_checkpoint_input": None,
        "existing_proof_adoption_permitted": False,
        "proof_format_switch_mid_generation_permitted": False,
        "proof_append_permitted": False,
        "literal_cnf_or_proof_path_in_solver_argv_permitted": False,
        "exclusive_proof_inode_anchor_required": True,
    }
    for participant in plan["participants"]:
        argv = participant["solver_invocation"]["argv"]
        assert argv[1:3] == ["--lrat", "--no-binary"]
        assert "--binary" not in argv
        assert "--binary=true" not in argv
        assert argv[-2:] == [
            f"/proc/self/fd/{native.SOLVER_CNF_FD}",
            f"/proc/self/fd/{native.SOLVER_PROOF_FD}",
        ]
        assert participant["cnf"]["path"] not in argv
        assert participant["proof_output"]["path"] not in argv
        assert participant["solver_invocation"]["fd_bindings"]["proof"][
            "hold_inode_anchor_through_solver_exit"
        ] is True
        handoff = participant["certification_handoff_contract"]
        assert handoff["initial_lrat_check"]["argv"] == handoff["fresh_lrat_replay"]["argv"]
        assert handoff["fresh_lrat_replay"][
            "distinct_process_identity_from_initial_check_required"
        ] is True
        assert handoff["existing_certification_layer_must_revalidate_all_bindings"] is True
    assert plan["publication_boundaries"]["starts_solver"] is False
    assert plan["publication_boundaries"]["publishes_terminal"] is False
    assert plan["publication_boundaries"]["deletes_or_cleans_data"] is False
    assert plan["deployment_gate"]["launch_eligible"] is False
    assert plan["deployment_gate"]["production_eligible"] is False
    assert "native-lrat-certification-adapter-with-two-real-checker-runs" in plan[
        "deployment_gate"
    ]["remaining_required_components"]
    assert (
        "isolated-fresh-root-marker-and-legacy-dmtcp-session-checkpoint-denial"
        in plan["deployment_gate"]["remaining_required_components"]
    )
    assert "sealed-elf-loader-and-dynamic-runtime-closure" in plan[
        "deployment_gate"
    ]["remaining_required_components"]
    native.verify_plan(plan, pins=world["pins"])  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("generation", 1, "generation-zero"),
        ("fresh_leaf_generation", False, "generation-zero"),
        ("resume", True, "generation-zero"),
        ("checkpoint_source", "/tmp/ckpt.dmtcp", "generation-zero"),
        ("existing_proof_path", "/tmp/old.drat", "generation-zero"),
        ("existing_proof_format", "binary-drat", "generation-zero"),
    ],
)
def test_plan_rejects_resume_checkpoint_or_midstream_format_switch(
    world: dict[str, object], field: str, value: object, message: str,
) -> None:
    spec = copy.deepcopy(world["spec"])
    spec[field] = value
    with pytest.raises(native.NativeLratPlanError, match=message):
        native.build_plan(spec, pins=world["pins"])  # type: ignore[arg-type]


def test_default_binary_lrat_regression_is_not_expressible(world: dict[str, object]) -> None:
    """Pinned lrat-check requires ASCII; CaDiCaL's default binary LRAT is invalid."""

    plan = _plan(world)
    participant = plan["participants"][0]
    attacked = copy.deepcopy(plan)
    attacked["participants"][0]["solver_invocation"]["argv"].remove("--no-binary")
    attacked["participants"][0]["solver_invocation"]["argv_sha256"] = native._digest(
        attacked["participants"][0]["solver_invocation"]["argv"]
    )
    attacked["plan_sha256"] = native._digest(
        {key: value for key, value in attacked.items() if key != "plan_sha256"}
    )
    assert participant["solver_invocation"]["argv"][1:3] == ["--lrat", "--no-binary"]
    with pytest.raises(native.NativeLratPlanError, match="does not match"):
        native.verify_plan(attacked, pins=world["pins"])  # type: ignore[arg-type]


def test_existing_proof_output_and_aliasing_are_refused(world: dict[str, object]) -> None:
    spec = copy.deepcopy(world["spec"])
    output = Path(spec["leaves"][0]["proof_output_path"])
    output.write_bytes(b"old proof")
    with pytest.raises(native.NativeLratPlanError, match="already exists"):
        native.build_plan(spec, pins=world["pins"])  # type: ignore[arg-type]
    assert output.read_bytes() == b"old proof"
    output.unlink()
    spec["leaves"][1]["proof_output_path"] = spec["leaves"][0]["proof_output_path"]
    with pytest.raises(native.NativeLratPlanError, match="exclusive"):
        native.build_plan(spec, pins=world["pins"])  # type: ignore[arg-type]


def test_symlink_cnf_and_mutated_cnf_fail_closed(world: dict[str, object]) -> None:
    real = world["cnf_a"]
    alias = Path(world["tmp"]) / "alias.cnf"
    alias.symlink_to(real)
    spec = copy.deepcopy(world["spec"])
    spec["leaves"][0]["cnf_path"] = str(alias)
    with pytest.raises(native.NativeLratPlanError, match="canonical or is a symlink"):
        native.build_plan(spec, pins=world["pins"])  # type: ignore[arg-type]

    plan = _plan(world)
    real.write_bytes(real.read_bytes() + b"c changed\n")
    with pytest.raises(native.NativeLratPlanError, match="does not match"):
        native.verify_plan(plan, pins=world["pins"])  # type: ignore[arg-type]


def test_preexec_race_never_truncates_or_adopts_existing_bytes(
    world: dict[str, object],
) -> None:
    plan = _plan(world)
    observation = _observation(plan, "leaf-00", 1900)
    proof = Path(plan["participants"][0]["proof_output"]["path"])
    proof.write_bytes(b"do-not-overwrite")
    with pytest.raises(native.NativeLratPlanError, match="unsafe exclusive-native-lrat-output"):
        native.build_start_receipt(
            plan, observation, pins=world["pins"],  # type: ignore[arg-type]
        )
    assert proof.read_bytes() == b"do-not-overwrite"


def test_toolchain_hash_and_source_audit_are_both_enforced(world: dict[str, object]) -> None:
    pins = world["pins"]
    bad_source = native.ToolchainPins(
        **{**pins.__dict__, "solver_upstream_commit": "9" * 40}  # type: ignore[union-attr]
    )
    with pytest.raises(native.NativeLratPlanError, match="source audit identity"):
        native.build_plan(world["spec"], pins=bad_source)  # type: ignore[arg-type]

    checker = world["checker"]
    checker.write_bytes(checker.read_bytes() + b"# changed\n")
    with pytest.raises(native.NativeLratPlanError, match="LRAT checker SHA-256"):
        native.build_plan(world["spec"], pins=pins)  # type: ignore[arg-type]


def test_start_receipts_bind_pid_start_generation_cpu_and_lease(
    world: dict[str, object],
) -> None:
    plan = _plan(world)
    observation = _observation(plan, "leaf-00", 2001)
    receipt = native.build_start_receipt(
        plan, observation, pins=world["pins"],  # type: ignore[arg-type]
    )
    assert receipt["pid"] == 2001
    assert receipt["proc_start_ticks"] == 902001
    assert receipt["generation"] == 0
    assert receipt["cpu"] == 7
    assert receipt["preexec_gate_held"] is True
    assert receipt["proof_fd"] == native.SOLVER_PROOF_FD
    assert receipt["proof_output_binding"]["bytes"] == 0
    assert receipt["releases_process"] is False
    native.verify_start_receipt(
        plan, receipt, pins=world["pins"],  # type: ignore[arg-type]
    )

    bad = copy.deepcopy(observation)
    bad["proc_start_ticks"] = 0
    with pytest.raises(native.NativeLratPlanError, match="start ticks"):
        native.build_start_receipt(
            plan, bad, pins=world["pins"],  # type: ignore[arg-type]
        )
    bad = copy.deepcopy(observation)
    bad["preexec_gate_held"] = False
    with pytest.raises(native.NativeLratPlanError, match="generation-zero gate"):
        native.build_start_receipt(
            plan, bad, pins=world["pins"],  # type: ignore[arg-type]
        )


def test_all_start_barrier_refuses_partial_or_reused_process_identity(
    world: dict[str, object],
) -> None:
    plan = _plan(world)
    first = native.build_start_receipt(
        plan, _observation(plan, "leaf-00", 2100), pins=world["pins"],  # type: ignore[arg-type]
    )
    second = native.build_start_receipt(
        plan, _observation(plan, "leaf-01", 2101), pins=world["pins"],  # type: ignore[arg-type]
    )
    with pytest.raises(native.NativeLratPlanError, match="incomplete"):
        native.build_barrier_receipt(
            plan, [first], pins=world["pins"],  # type: ignore[arg-type]
        )
    barrier = native.build_barrier_receipt(
        plan, [second, first], pins=world["pins"],  # type: ignore[arg-type]
    )
    assert barrier["all_start_receipts_complete"] is True
    assert barrier["releases_processes"] is False
    assert barrier["membership"] == ["leaf-00", "leaf-01"]
    native.verify_barrier_receipt(
        plan, [first, second], barrier,
        pins=world["pins"],  # type: ignore[arg-type]
    )

    duplicate_identity_observation = _observation(plan, "leaf-01", 2100)
    duplicate_identity_observation["proc_start_ticks"] = first["proc_start_ticks"]
    duplicate = native.build_start_receipt(
        plan, duplicate_identity_observation, pins=world["pins"],  # type: ignore[arg-type]
    )
    with pytest.raises(native.NativeLratPlanError, match="reuse"):
        native.build_barrier_receipt(
            plan, [first, duplicate], pins=world["pins"],  # type: ignore[arg-type]
        )


def test_publish_is_create_only_and_dry_run_does_not_write(
    world: dict[str, object], capsys: pytest.CaptureFixture[str],
) -> None:
    plan = _plan(world)
    output = Path(world["records"]) / "plan.json"
    native.publish_record(output, plan)
    assert json.loads(output.read_text(encoding="ascii")) == plan
    with pytest.raises(native.NativeLratPlanError, match="refusing to replace"):
        native.publish_record(output, plan)
    assert json.loads(output.read_text(encoding="ascii")) == plan

    nowhere = Path(world["records"]) / "dry-run.json"
    native._emit_or_publish(plan, nowhere, True)
    captured = capsys.readouterr()
    assert json.loads(captured.out) == plan
    assert not nowhere.exists()
