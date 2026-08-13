"""Contracts for the full-support published-volume ansatz v3."""

from __future__ import annotations

import json
import os
from collections import Counter
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest

import evaluation.ansatz_v3_dual_track as dual_track_module
import evolve.run_evolution as launcher_module
import humanize.escalation as escalation_module
import humanize.flow as flow_module
from evolve.ansatz_v3_codex_view import (
    AnsatzV3CodexViewError,
    FORBIDDEN_READABLE_PATHS,
    VIEW_MANIFEST_NAME,
    VIEW_SOURCE_ALLOWLIST,
    materialize_sanitized_codex_view,
    validate_sanitized_codex_view,
)
from evaluation.ansatz_v3_contract import (
    FAMILY_SWITCH_EVIDENCE_KIND,
    family_switch_decision,
    load_finite_domain_contract,
)
from evaluation.ansatz_witness_fingerprint import (
    negative_witness_algebraic_fingerprint,
)
from evaluation.ansatz_v3_dual_track import (
    build_dual_track_plan,
    load_dual_track_contract,
)
from evaluation.ansatz_v3_program_guard import (
    AnsatzV3ProgramGuardError,
    validate_ansatz_v3_program,
    validate_ansatz_v3_program_source,
)
from evaluation.formal_audit_quota import (
    ASSIGNMENT_FIELD,
    load_quota_contract,
    quota_slot_schedule,
    round_quota_slots,
    selection_report,
    validate_selection_report,
)
from evaluation.search_contract import (
    PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
    PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_REPRESENTATION_ID,
    geometry_contract_for_representation,
)
from evolve.seed_solution_twisted_torus_ansatz_v3 import (
    PREREGISTERED_SUPPORT_SPLITS,
    _expand_twist_quota,
    _generate_support_proposals,
    _proposal_supports,
    generate_candidates,
)
from humanize.flow import select_for_milp
from humanize.escalation import (
    EscalationPlan,
    load_template_registry,
    materialize_child_pipeline,
    verify_materialized_child_pipeline,
)
from humanize.pipeline import PipelineConfig
from humanize.state import code_key
from scripts.verify_blind_ansatz_v3_calibration import build_report


PROJECT = Path(__file__).resolve().parents[1]
PIPELINE = (
    PROJECT
    / "configs/five_stage_campaign.twisted_torus_ansatz_v3_preregistered.json"
)
QUOTA = (
    PROJECT
    / "configs/twisted_torus_ansatz_v3.formal_audit_quota.v1.json"
)
FINITE = PROJECT / "configs/twisted_torus_ansatz_v3.finite_domain.v1.json"
REGISTRY = PROJECT / "configs/campaign_templates.ansatz_v3.json"
DUAL_TRACK = PROJECT / "configs/twisted_torus_ansatz_v3.dual_track.v1.json"
ANCHORS = PROJECT / "evaluation/twisted_torus_published_anchors.v1.json"


def _candidate(
    tag: int,
    *,
    volume: int,
    split: tuple[int, int],
    twist: int,
    mechanism: str,
) -> dict:
    published_lattices = {
        36: (6, 6),
        45: (5, 9),
        54: (6, 9),
        105: (5, 21),
        124: (2, 62),
        126: (6, 21),
        127: (1, 127),
        132: (6, 22),
        144: (12, 12),
        147: (7, 21),
        170: (10, 17),
    }
    ell, m = published_lattices[volume]
    a_count, b_count = split
    return {
        "ell": ell,
        "m": m,
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": twist % m,
        },
        "A_terms": [[offset % ell, (tag + offset * 3) % m] for offset in range(a_count)],
        "B_terms": [[offset % ell, (tag + 1 + offset * 5) % m] for offset in range(b_count)],
        "n": 2 * volume,
        "k": 8,
        "d": 0,
        "fom": 0.0,
        "stage": "quick",
        "relation_type": mechanism,
        "static_eligibility": {"eligible": True},
        "structural_novelty": {"novel": True},
        "search_representation_id": PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
    }


def test_v3_is_a_fresh_geometry_and_checkpoint_representation():
    assert PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID != (
        PUBLISHED_VOLUME_REPRESENTATION_ID
    )
    assert PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT != (
        PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    )
    assert geometry_contract_for_representation(
        PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    ) == PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT


def test_full_support_generator_realizes_every_preregistered_split_without_anchors():
    proposals = _generate_support_proposals(5, 21)
    observed = Counter(
        (len(a_terms), len(b_terms))
        for proposal in proposals
        for a_terms, b_terms in [_proposal_supports(proposal)]
    )
    assert set(observed) == set(PREREGISTERED_SUPPORT_SPLITS)
    assert all(count > 0 for count in observed.values())
    assert any(
        (0, 0) not in a_terms and (1, 0) not in a_terms
        for a_terms, _b_terms in map(_proposal_supports, proposals)
    )
    assert any(
        (0, 0) not in b_terms and (0, 1) not in b_terms
        for _a_terms, b_terms in map(_proposal_supports, proposals)
    )
    source = (
        PROJECT / "evolve/seed_solution_twisted_torus_ansatz_v3.py"
    ).read_text(encoding="utf-8")
    assert "PUBLISHED_CALIBRATION_ANCHORS" not in source
    assert "twisted_torus_published_anchors" not in source


def test_mutable_program_guard_blocks_anchor_io_and_imports():
    seed = PROJECT / "evolve/seed_solution_twisted_torus_ansatz_v3.py"
    report = validate_ansatz_v3_program(seed)
    assert report["anchor_manifest_readable"] is False
    source = seed.read_text(encoding="utf-8")
    io_source = source.replace(
        '    """Propose complete sparse supports without privileged monomials."""',
        '    """invalid"""\n    open("evaluation/twisted_torus_published_anchors.v1.json")',
    )
    with pytest.raises(AnsatzV3ProgramGuardError, match="forbidden"):
        validate_ansatz_v3_program_source(io_source)
    import_source = source.replace(
        '    """Propose complete sparse supports without privileged monomials."""',
        '    """invalid"""\n    import pathlib',
    )
    with pytest.raises(AnsatzV3ProgramGuardError, match="forbidden syntax"):
        validate_ansatz_v3_program_source(import_source)


def test_mutable_program_guard_rejects_nested_helpers_and_wrapper_changes():
    seed = PROJECT / "evolve/seed_solution_twisted_torus_ansatz_v3.py"
    source = seed.read_text(encoding="utf-8")
    helper_source = source.replace(
        '    """Propose complete sparse supports without privileged monomials."""',
        '    """helper-based deterministic proposal"""\n'
        '    def shifted(point, dx, dy):\n'
        '        return (point[0] + dx, point[1] + dy)',
    ).replace(
        "    x_radius = max(1, min(ell, 8))",
        "    x_radius = max(1, min(ell, 8))\n"
        "    _probe = shifted((0, 0), x_radius, 0)",
    )
    with pytest.raises(AnsatzV3ProgramGuardError, match="nested functions"):
        validate_ansatz_v3_program_source(helper_source)

    wrapper_source = source.replace(
        "MAX_TWISTED_POOL = 420",
        'LEAK = open("evaluation/twisted_torus_published_anchors.v1.json")\n'
        "MAX_TWISTED_POOL = 420",
    )
    with pytest.raises(AnsatzV3ProgramGuardError, match="immutable wrapper"):
        validate_ansatz_v3_program_source(wrapper_source)

    suffix_source = source.replace(
        "def generate_candidates(ell: int, m: int) -> list[dict[str, Any]]:",
        "WRAPPER_MUTATION = 1\n\n"
        "def generate_candidates(ell: int, m: int) -> list[dict[str, Any]]:",
    )
    with pytest.raises(AnsatzV3ProgramGuardError, match="immutable wrapper"):
        validate_ansatz_v3_program_source(suffix_source)


@pytest.mark.parametrize(
    "statement",
    [
        'print("leak")',
        "dir()",
        "type(ell)",
        "license()",
        "unknown_callable(ell)",
    ],
)
def test_mutable_program_guard_rejects_unregistered_direct_calls(statement):
    seed = PROJECT / "evolve/seed_solution_twisted_torus_ansatz_v3.py"
    source = seed.read_text(encoding="utf-8").replace(
        '    """Propose complete sparse supports without privileged monomials."""',
        f'    """invalid direct call"""\n    {statement}',
    )
    with pytest.raises(AnsatzV3ProgramGuardError, match="forbidden function"):
        validate_ansatz_v3_program_source(source)


def test_v3_evaluator_applies_program_guard_before_import(tmp_path, monkeypatch):
    import evolve.openevolve_evaluator as evaluator_module

    seed = PROJECT / "evolve/seed_solution_twisted_torus_ansatz_v3.py"
    source = seed.read_text(encoding="utf-8").replace(
        '    """Propose complete sparse supports without privileged monomials."""',
        '    """invalid"""\n    open("evaluation/twisted_torus_published_anchors.v1.json")',
    )
    candidate = tmp_path / "candidate.py"
    candidate.write_text(source, encoding="utf-8")
    monkeypatch.setattr(
        evaluator_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    with pytest.raises(AnsatzV3ProgramGuardError, match="forbidden"):
        evaluator_module._load_generate_candidates(str(candidate))


def test_v3_production_prompt_states_mutable_syntax_contract():
    import yaml

    config = yaml.safe_load((
        PROJECT / "evolve/config_twisted_torus_ansatz_v3.yaml"
    ).read_text(encoding="utf-8"))
    prompt = config["prompt"]["system_message"]
    assert "nested `def` or `async def` helpers" in prompt
    assert "outside `_generate_support_proposals`" in prompt


def test_v3_codex_view_is_exact_allowlist_without_anchor_or_calibration(tmp_path):
    view_path = tmp_path / "sanitized-view"
    view = materialize_sanitized_codex_view(PROJECT, view_path)
    assert set(view["allowlist"]) == set(VIEW_SOURCE_ALLOWLIST)
    assert view["filesystem_boundary"] == "os-chroot-no-main-repository-mount"
    assert (view_path / VIEW_MANIFEST_NAME).is_file()
    for relative in VIEW_SOURCE_ALLOWLIST:
        assert (view_path / relative).is_file()
        assert not (view_path / relative).is_symlink()
    for relative in FORBIDDEN_READABLE_PATHS:
        assert not (view_path / relative).exists()
        assert not (view_path / relative).is_symlink()


def test_v3_codex_view_tamper_and_symlink_fail_closed(tmp_path):
    tampered = tmp_path / "tampered"
    materialize_sanitized_codex_view(PROJECT, tampered)
    copied_seed = tampered / "evolve/seed_solution_twisted_torus_ansatz_v3.py"
    copied_seed.chmod(0o644)
    copied_seed.write_text("tampered\n", encoding="utf-8")
    with pytest.raises(AnsatzV3CodexViewError, match="writable|changed"):
        validate_sanitized_codex_view(PROJECT, tampered)

    escaped = tmp_path / "escaped"
    materialize_sanitized_codex_view(PROJECT, escaped)
    os.symlink(PROJECT / "evaluation", escaped / "anchor-escape")
    with pytest.raises(AnsatzV3CodexViewError, match="unsafe"):
        validate_sanitized_codex_view(PROJECT, escaped)


def test_only_v3_codex_binding_changes_cwd(tmp_path, monkeypatch):
    executable = tmp_path / "codex"
    executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    executable.chmod(0o755)
    monkeypatch.setattr(
        flow_module,
        "_resolve_native_codex_path",
        lambda _requested: executable,
    )
    monkeypatch.setattr(flow_module, "_codex_version", lambda _path: "test")
    v3 = SimpleNamespace(
        repo_dir=PROJECT,
        search_representation_id=PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
    )
    _identity, _version, v3_cwd = flow_module._fresh_codex_binding(
        v3,
        round_dir=tmp_path / "round-001",
    )
    assert Path(v3_cwd).parent == tmp_path / "round-001"
    assert Path(v3_cwd) != PROJECT

    for representation in (
        PUBLISHED_VOLUME_REPRESENTATION_ID,
        "css-bb-twisted-torus-generator-v1",
    ):
        legacy = SimpleNamespace(
            repo_dir=PROJECT,
            search_representation_id=representation,
        )
        _identity, _version, cwd = flow_module._fresh_codex_binding(
            legacy,
            round_dir=tmp_path / f"round-{representation}",
        )
        assert Path(cwd) == PROJECT


def test_run_evolution_replays_and_emits_v3_codex_view_binding(
    tmp_path, monkeypatch
):
    executable = tmp_path / "codex"
    executable.write_text(
        "#!/bin/sh\nprintf 'codex-test 1.0\\n'\n",
        encoding="utf-8",
    )
    executable.chmod(0o755)
    view = materialize_sanitized_codex_view(PROJECT, tmp_path / "view")
    monkeypatch.setattr(
        launcher_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    monkeypatch.setattr(
        launcher_module,
        "_resolve_native_codex_path",
        lambda _requested: executable,
    )
    monkeypatch.setenv("QCODE_CODEX_CWD", view["view_path"])
    environment = {
        "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST": view["manifest_path"],
        "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST_SHA256": view[
            "manifest_file_sha256"
        ],
        "QCODE_ANSATZ_V3_CODEX_VIEW_SOURCE_FINGERPRINT_SHA256": view[
            "source_fingerprint_sha256"
        ],
        "QCODE_ANSATZ_V3_CODEX_FILESYSTEM_BOUNDARY": view[
            "filesystem_boundary"
        ],
    }
    for name, value in environment.items():
        monkeypatch.setenv(name, value)

    identity, version, cwd, binding, manifest_identity = (
        launcher_module._resolve_codex_execution_binding()
    )
    assert version == "codex-test 1.0"
    assert cwd == view["view_path"]
    assert binding == {
        "ansatz_v3_codex_view_manifest_path": view["manifest_path"],
        "ansatz_v3_codex_view_manifest_sha256": view[
            "manifest_file_sha256"
        ],
        "ansatz_v3_codex_view_source_fingerprint_sha256": view[
            "source_fingerprint_sha256"
        ],
        "ansatz_v3_codex_filesystem_boundary": view[
            "filesystem_boundary"
        ],
    }
    assert manifest_identity == launcher_module._file_identity(
        view["manifest_path"],
        "test ansatz-v3 sanitized Codex view manifest",
    )
    backend = tmp_path / "backend.py"
    backend.write_text("backend\n", encoding="utf-8")
    invocation = {
        "model_names": ["fake-model"],
        "reasoning_effort": "xhigh",
        "codex_cli": True,
        "max_parallel_evaluations": 1,
        "api_base": "http://localhost:4000/v1",
        "temperature_disabled": True,
        "codex_version": version,
        "codex_cwd": cwd,
        "codex_executable_mode": identity["mode"],
        "search_geometry_contract": (
            PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT
        ),
        **binding,
    }
    assert launcher_module._validated_invocation_binding(
        invocation,
        backend,
        identity,
    ) == invocation

    monkeypatch.setenv(
        "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST_SHA256", "0" * 64
    )
    with pytest.raises(RuntimeError, match="environment changed"):
        launcher_module._ansatz_v3_codex_view_invocation_binding(cwd)


def _v3_child_launch_inputs(tmp_path, monkeypatch):
    view = materialize_sanitized_codex_view(PROJECT, tmp_path / "child-view")
    monkeypatch.setattr(
        launcher_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    paths = {
        name: tmp_path / name
        for name in ("config.yaml", "seed.py", "evaluator.py", "context.md")
    }
    for name, path in paths.items():
        path.write_text(name + "\n", encoding="utf-8")
    backend = tmp_path / "codex_cli_llm.py"
    backend.write_text("backend\n", encoding="utf-8")
    executable = tmp_path / "codex-native"
    executable.write_bytes(b"\x7fELFfake")
    executable.chmod(0o700)
    executable_identity = launcher_module._file_identity(
        executable, "test Codex executable"
    )
    executable_identity["mode"] = 0o700
    manifest_identity = launcher_module._file_identity(
        view["manifest_path"], "test ansatz-v3 Codex view manifest"
    )
    invocation = {
        "codex_cwd": view["view_path"],
        "ansatz_v3_codex_view_manifest_path": view["manifest_path"],
        "ansatz_v3_codex_view_manifest_sha256": view[
            "manifest_file_sha256"
        ],
        "ansatz_v3_codex_view_source_fingerprint_sha256": view[
            "source_fingerprint_sha256"
        ],
        "ansatz_v3_codex_filesystem_boundary": view[
            "filesystem_boundary"
        ],
    }
    dependencies = launcher_module._evaluator_dependency_identities()
    return {
        "config_path": paths["config.yaml"],
        "seed_path": paths["seed.py"],
        "evaluator_path": paths["evaluator.py"],
        "context_path": paths["context.md"],
        "context_identity": launcher_module._file_identity(
            paths["context.md"], "test context"
        ),
        "dependency_identities": dependencies,
        "backend_path": backend,
        "codex_executable_identity": executable_identity,
        "ansatz_v3_codex_view_manifest_identity": manifest_identity,
        "invocation": invocation,
    }


def test_child_launch_binding_includes_exact_v3_view_manifest_identity(
    tmp_path, monkeypatch
):
    launch = _v3_child_launch_inputs(tmp_path, monkeypatch)

    identities = launcher_module._launch_input_identities(**launch)

    assert identities["ansatz_v3_codex_view_manifest"] == launch[
        "ansatz_v3_codex_view_manifest_identity"
    ]
    assert set(identities["ansatz_v3_codex_view_manifest"]) == {
        "path",
        "sha256",
        "bytes",
    }


@pytest.mark.parametrize("tamper", ["missing_bytes", "hash", "path"])
def test_child_launch_binding_rejects_v3_view_manifest_identity_tamper(
    tmp_path, monkeypatch, tamper
):
    launch = _v3_child_launch_inputs(tmp_path, monkeypatch)
    frozen = dict(launch["ansatz_v3_codex_view_manifest_identity"])
    if tamper == "missing_bytes":
        frozen.pop("bytes")
    elif tamper == "hash":
        frozen["sha256"] = "0" * 64
    else:
        frozen["path"] = str((tmp_path / "wrong-manifest.json").resolve())
    launch["ansatz_v3_codex_view_manifest_identity"] = frozen

    with pytest.raises(RuntimeError, match="manifest identity changed"):
        launcher_module._launch_input_identities(**launch)


def test_wrapper_interleaves_splits_across_q_and_never_injects_malformed_defaults():
    rows = _expand_twist_quota(
        5,
        21,
        _generate_support_proposals(5, 21),
        limit=63,
    )
    assert len(rows) == 63
    assert {row["geometry"]["twist"] for row in rows} == set(range(21))
    observed = Counter((len(row["A_terms"]), len(row["B_terms"])) for row in rows)
    assert {(2, 4), (4, 2), (2, 3), (3, 2)}.issubset(observed)
    assert all(set(row) == {"A_terms", "B_terms", "geometry"} for row in rows)
    with pytest.raises(RuntimeError, match="failed immutable q coverage"):
        _expand_twist_quota(5, 21, [], limit=63)


def test_production_quick_evaluator_accepts_v3_at_127_and_132(
    tmp_path, monkeypatch
):
    import evolve.openevolve_evaluator as evaluator_module

    monkeypatch.setattr(
        evaluator_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    metrics = evaluator_module._run_evaluation(
        generate_candidates,
        [(1, 127), (2, 66)],
        quick=True,
        candidate_limit=420,
        candidate_log_path=tmp_path / "production-quick.jsonl",
    )
    assert metrics["lattices_completed"] == 2
    assert metrics["lattice_failures"] == 0
    assert metrics["malformed_candidate_definitions"] == 0
    assert metrics["unique_candidates"] > 0
    assert metrics["geometry_twists_required"] == 67
    assert metrics["geometry_twists_observed"] == 67
    assert metrics["geometry_twist_coverage_complete"] == 1
    assert set(metrics["support_split_counts"]) == {
        "2+4", "4+2", "2+3", "3+2", "2+2", "3+3"
    }
    assert all(metrics["support_split_counts"].values())


def test_quota_contract_is_deterministic_and_makes_127_132_mandatory():
    contract = load_quota_contract(
        QUOTA,
        representation_id=PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
        rounds=12,
        slots_per_round=6,
    )
    schedule = quota_slot_schedule(contract)
    assert len(schedule) == 72
    counts = Counter(schedule)
    assert counts[127] == counts[132] == 8
    assert set(round_quota_slots(contract, 1)[0]) == {"slot_index", "volume"}
    assert contract["mandatory_audited_volumes"] == [127, 132]
    assert "bp_osd" in contract["positive_promotion_forbidden_sources"]


def test_quota_selector_uses_exact_assigned_volumes_and_never_backfills_missing_slot():
    slots = [
        {"slot_index": 0, "volume": 127},
        {"slot_index": 1, "volume": 132},
        {"slot_index": 2, "volume": 105},
    ]
    pool = [
        _candidate(1, volume=127, split=(2, 4), twist=25, mechanism="shared_coset"),
        _candidate(2, volume=105, split=(4, 2), twist=3, mechanism="affine_orbit"),
        _candidate(3, volume=105, split=(2, 3), twist=4, mechanism="unstructured"),
    ]
    selected = select_for_milp(
        pool,
        None,
        set(),
        3,
        formal_audit_slots=slots,
        prior_audit_rows=[],
    )
    assert [row[ASSIGNMENT_FIELD]["slot_index"] for row in selected] == [0, 2]
    assert [row[ASSIGNMENT_FIELD]["volume"] for row in selected] == [127, 105]
    assert all(row.get("fom") == 0.0 for row in selected)

    contract = load_quota_contract(QUOTA)
    round_selected = select_for_milp(
        pool,
        None,
        set(),
        6,
        formal_audit_slots=list(round_quota_slots(contract, 1)),
        prior_audit_rows=[],
    )
    report = selection_report(
        contract=contract,
        round_number=1,
        selected_fresh=round_selected,
        retry_candidate_keys=[],
        candidate_key_fn=code_key,
    )
    validate_selection_report(report, contract=contract, round_number=1)
    tampered = json.loads(json.dumps(report))
    tampered["filled_fresh_slots"] += 1
    unsigned = dict(tampered)
    unsigned.pop("report_sha256")
    tampered["report_sha256"] = dual_track_module._canonical_sha256(unsigned)
    with pytest.raises(ValueError, match="counts"):
        validate_selection_report(tampered, contract=contract, round_number=1)


def test_negative_witness_fingerprint_is_algebraic_and_explicitly_negative_only():
    row = _candidate(
        5,
        volume=105,
        split=(2, 4),
        twist=10,
        mechanism="shared_coset",
    )
    report = negative_witness_algebraic_fingerprint(
        row,
        sector="X",
        weight=3,
        support=[0, 1, 106],
        witness_sha256="a" * 64,
    )
    assert report["quotient"]["volume"] == 105
    assert report["quotient"]["smith_invariants"][0] >= 1
    assert report["support_mechanism"]["support_split_type"] == "2+4"
    assert "negative feedback only" in report["semantics"]
    assert len(report["fingerprint_sha256"]) == 64


def test_pipeline_loads_preregistered_v3_contracts_and_six_audits_per_round():
    pipeline = PipelineConfig.from_json(
        PIPELINE,
        repo_dir=PROJECT,
        run_id="ansatz-v3-contract-test",
    )
    flow = pipeline.flow_config
    assert flow is not None
    assert flow.search_representation_id == PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    assert flow.milp_top == 6
    assert flow.max_rounds == 12
    assert flow.formal_audit_quota_contract == QUOTA
    assert flow.finite_search_domain_contract == FINITE
    assert flow.dual_track_contract == DUAL_TRACK


def test_reviewer_template_is_installed_compatible_and_hash_binds_all_contracts():
    registry = load_template_registry(
        repo_dir=PROJECT,
        registry_path=REGISTRY.relative_to(PROJECT),
    )
    template = registry.template(
        "css-bb-twisted-torus-published-volume-ansatz-v3"
    )
    assert template.representation_id == PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    assert template.proof_compatible is template.launch_compatible is True
    assert template.allowed_machine_regimes == ("representation_change_required",)
    assert {item.path for item in template.representation_contracts} == {
        QUOTA.relative_to(PROJECT).as_posix(),
        FINITE.relative_to(PROJECT).as_posix(),
        DUAL_TRACK.relative_to(PROJECT).as_posix(),
    }


def test_materialized_v3_child_rechecks_all_representation_contracts(
    tmp_path, monkeypatch
):
    registry = load_template_registry(
        repo_dir=PROJECT,
        registry_path=REGISTRY.relative_to(PROJECT),
    )
    template = registry.template(
        "css-bb-twisted-torus-published-volume-ansatz-v3"
    )
    plan = EscalationPlan(
        repo_dir=PROJECT,
        registry_path=registry.registry_path,
        registry_sha256=registry.registry_sha256,
        template_id=template.template_id,
        template_version=template.template_version,
        template_entry_sha256=template.entry_sha256,
        parent_state_path="results/fixture-parent/state.json",
        parent_run_id="fixture-parent",
        machine_evidence_sha256="1" * 64,
        parent_representation_id=PUBLISHED_VOLUME_REPRESENTATION_ID,
        machine_regime="representation_change_required",
        transition_kind="representation_change",
        target_representation_id=template.representation_id,
        child_run_id="fixture-ansatz-v3-child",
        idempotency_key="2" * 64,
        proof_compatible=True,
        launch_compatible=True,
        materializable=True,
        block_reasons=(),
    )
    monkeypatch.setattr(
        escalation_module, "plan_campaign_escalation", lambda **_kwargs: plan
    )
    relative = Path("results") / tmp_path.name / "ansatz-v3-child.json"
    materialized = materialize_child_pipeline(plan, destination=relative)
    value = json.loads(materialized.path.read_text(encoding="utf-8"))
    provenance = value["campaign_escalation"]
    assert provenance["schema_version"] == 2
    assert provenance["representation_contracts"] == [
        item.serializable() for item in template.representation_contracts
    ]
    verified = verify_materialized_child_pipeline(
        repo_dir=PROJECT,
        config_path=relative,
        expected_pipeline_sha256=materialized.pipeline_sha256,
    )
    assert verified is not None
    materialized.path.unlink()
    materialized.path.parent.rmdir()


def test_blind_calibration_is_post_seal_and_gives_zero_search_credit(tmp_path):
    manifest = json.loads(ANCHORS.read_text(encoding="utf-8"))
    anchor = manifest["anchors"][0]
    candidate = {
        "ell": anchor["ell"],
        "m": anchor["m"],
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": anchor["twist"],
        },
        "A_terms": [[0, 0], [1, 0], anchor["third_a"]],
        "B_terms": [[0, 0], [0, 1], anchor["third_b"]],
    }
    candidate_path = tmp_path / "sealed.jsonl"
    candidate_path.write_text(json.dumps(candidate) + "\n", encoding="utf-8")
    report = build_report(candidate_path, ANCHORS)
    assert report["blind_reconstructions"] == 1
    assert report["anchor_manifest"]["loaded_after_candidate_log_seal"] is True
    assert report["fitness_credit"] == report["novelty_credit"] == 0
    assert report["search_coverage_credit"] == report["discovery_credit"] == 0


def _switch_evidence(finite: dict, quota: dict) -> dict:
    counts = {str(row["volume"]): row["quota"] for row in quota["volume_quotas"]}
    candidates = [
        {
            "canonical_digest": f"candidate-{index}",
            "n": 100,
            "k": 1,
            "fom_gt_12_excluded": True,
            "trusted_upper_bound": {
                "kind": "replayed-low-weight-sat",
                "replayed": True,
                "weight": 8,
            },
        }
        for index in range(3)
    ]
    return {
        "schema_version": 1,
        "kind": FAMILY_SWITCH_EVIDENCE_KIND,
        "representation_id": finite["representation_id"],
        "finite_domain_contract_sha256": finite["contract_sha256"],
        "formal_audit_quota_sha256": quota["contract_sha256"],
        "campaign": {
            "sealed": True,
            "rounds_completed": 12,
            "pending_round": None,
        },
        "realized_domain": {
            "manifest_complete": True,
            "total_unique_candidates": 3,
            "audited_unique_candidates": 3,
        },
        "stage2": {
            "ranked_snapshot_exhausted": True,
            "selection_ledger_pending": None,
            "unresolved_candidates": 0,
            "unknown_candidates": 0,
        },
        "candidates": candidates,
        "formal_audit": {
            "unfilled_slots": 0,
            "volume_counts": counts,
        },
        "trusted_novel_wins": 0,
        "unresolved_items": [],
    }


def test_family_switch_gate_is_fail_closed_and_never_auto_launches():
    finite = load_finite_domain_contract(FINITE)
    quota = load_quota_contract(QUOTA)
    evidence = _switch_evidence(finite, quota)
    allowed = family_switch_decision(evidence, contract=finite, quota_contract=quota)
    assert allowed["eligible_for_manual_family_transition"] is False
    assert "bound_artifact_replay_missing" in allowed["block_reasons"]
    assert allowed["automatic_family_switch"] is False

    evidence["stage2"]["unknown_candidates"] = 1
    blocked = family_switch_decision(evidence, contract=finite, quota_contract=quota)
    assert blocked["eligible_for_manual_family_transition"] is False
    assert "stage2_unresolved_or_unexhausted" in blocked["block_reasons"]
    assert blocked["allowed_next_family_examples"] == []

    evidence = _switch_evidence(finite, quota)
    evidence["candidates"][0].update(n=10, k=10)
    inconsistent = family_switch_decision(
        evidence, contract=finite, quota_contract=quota
    )
    assert inconsistent["eligible_for_manual_family_transition"] is False
    assert "not_every_candidate_has_trusted_excluding_upper_bound" in (
        inconsistent["block_reasons"]
    )


def test_candidate_key_ignores_quota_scheduling_metadata():
    row = _candidate(9, volume=105, split=(2, 3), twist=1, mechanism="unstructured")
    decorated = dict(row)
    decorated[ASSIGNMENT_FIELD] = {
        "schema_version": 1,
        "slot_index": 0,
        "volume": 105,
        "strata": {},
        "semantics": "audit-scheduling-only-no-distance-credit",
    }
    assert code_key(row) == code_key(decorated)


def _seal(value: dict, field: str) -> dict:
    unsigned = dict(value)
    unsigned.pop(field, None)
    return {**unsigned, field: dual_track_module._canonical_sha256(unsigned)}


def test_dual_track_replays_lb9_target_witness_and_plans_exactification(monkeypatch):
    class FakeCode:
        num_qudits = 24
        dimension = 4

    monkeypatch.setattr(
        dual_track_module, "build_css_code_from_claim", lambda _claim: FakeCode()
    )
    matrices = tuple(np.zeros((2, 24), dtype=np.uint8) for _ in range(4))
    monkeypatch.setattr(dual_track_module, "get_code_matrices", lambda _code: matrices)
    monkeypatch.setattr(
        dual_track_module, "verify_css_low_weight_oracle", lambda *_a, **_k: []
    )
    monkeypatch.setattr(
        dual_track_module,
        "verify_low_weight_sector_evidence",
        lambda *_a, **_k: [],
    )
    monkeypatch.setattr(
        dual_track_module, "css_sector_matrices", lambda *_a, **_k: (None, None)
    )
    monkeypatch.setattr(
        dual_track_module, "authoritative_candidate_digest", lambda _claim: "digest"
    )
    selected = {
        "candidate_key": "candidate-lb9",
        "structural_digest": "digest",
        "claim": {"ell": 3, "m": 4, "A_terms": [], "B_terms": []},
        "n": 24,
        "k": 4,
        "target": {"required_distance": 13},
        "strata": {"published_volume": 12},
        "initial_low_weight_oracle": {"outcome": "UNSAT", "max_weight": 4},
    }

    def rung(threshold: int, x: str, z: str, lower: int, upper=None):
        def evidence(outcome: str):
            value = {"outcome": outcome}
            if outcome == "SAT":
                value["witness"] = {"weight": 10}
            return {"evidence": value, "hard_wall": None}

        return {
            "threshold": threshold,
            "outcome": "SAT" if "SAT" in {x, z} else "UNSAT",
            "sectors": {"X": evidence(x), "Z": evidence(z)},
            "distance_lower_bound_after_rung": lower,
            "distance_upper_bound_after_rung": upper,
        }

    result = _seal({
        "schema_version": 1,
        "kind": "qcode-stratified-target-aware-ladder-v1",
        "candidate_key": "candidate-lb9",
        "contract_sha256": "c" * 64,
        "selected_sha256": dual_track_module._canonical_sha256(selected),
        "structural_digest": "digest",
        "n": 24,
        "k": 4,
        "target": selected["target"],
        "strata": selected["strata"],
        "initial_distance_lower_bound": 5,
        "final_distance_lower_bound": 9,
        "trusted_distance_upper_bound": 10,
        "target_gap": 4,
        "rejected_by_w8": False,
        "survived_w8": True,
        "unknown_fail_open": False,
        "stopped_reason": "trusted_negative_at_w12",
        "rungs": [
            rung(6, "UNSAT", "UNSAT", 7),
            rung(8, "UNSAT", "UNSAT", 9),
            rung(12, "SAT", "UNSAT", 9, 10),
        ],
        "elapsed_s": 1.0,
    }, "result_sha256")
    replayed = dual_track_module._replay_bound_result(
        result,
        selected,
        contract_sha256="c" * 64,
    )
    assert replayed["final_distance_lower_bound"] == 9
    assert dual_track_module._deep_thresholds(replayed, 13) == [9]


def test_dual_track_plan_prepares_both_tracks_without_launch(monkeypatch):
    contract = load_dual_track_contract(DUAL_TRACK, repo_dir=PROJECT)
    assert contract["joint_semantics"]["automatic_launch"] is False

    def selected_row(
        key: str, *, n: int, k: int, required: int, volume: int
    ) -> dict:
        return {
            "candidate_key": key,
            "structural_digest": f"structural-{key}",
            "triage_digest": f"triage-{key}",
            "claim": {
                "ell": 1,
                "m": volume,
                "A_terms": [[0, 0]],
                "B_terms": [[0, 1]],
            },
            "n": n,
            "k": k,
            "target": {"required_distance": required},
            "strata": {"published_volume": volume},
        }

    def open_result(
        key: str, *, lower: int, required: int, unknown_at: int, tag: int
    ) -> dict:
        thresholds = [6, 8]
        if required - 1 > 8:
            thresholds.append(required - 1)
        one_sector_unknown = {
            "810b191afaa80be65d6c": "X",
            "23c3554dbc3b6be07d91": "Z",
            "53a8c544f62e6947314d": "Z",
            "9acdbdda97a7d21bf6ac": "Z",
            "7479577865feac85b946": "Z",
            "83ab58ab65f747391c75": "Z",
        }.get(key)
        rungs = []
        for threshold in thresholds:
            if threshold > unknown_at:
                continue
            outcome = "UNKNOWN" if threshold == unknown_at else "UNSAT"
            sector_outcomes = {
                sector: (
                    "UNKNOWN"
                    if outcome == "UNKNOWN"
                    and (one_sector_unknown is None or sector == one_sector_unknown)
                    else "UNSAT"
                )
                for sector in ("X", "Z")
            }
            rungs.append({
                "threshold": threshold,
                "outcome": outcome,
                "sectors": {
                    sector: {"evidence": {"outcome": sector_outcome}}
                    for sector, sector_outcome in sector_outcomes.items()
                },
            })
        return {
            "candidate_key": key,
            "final_distance_lower_bound": lower,
            "trusted_distance_upper_bound": None,
            "target_gap": required - lower,
            "unknown_fail_open": True,
            "stopped_reason": f"fail_open_unknown_at_w{unknown_at}",
            "rungs": rungs,
            "result_sha256": f"{tag:064x}",
        }

    specs = [
        ("5c5ef6ca2ab6dfe179c0", 288, 12, 17, 144, 9, 16),
        ("7479577865feac85b946", 294, 12, 18, 147, 5, 6),
        ("53a8c544f62e6947314d", 252, 4, 28, 126, 7, 8),
        ("23c3554dbc3b6be07d91", 264, 4, 29, 132, 7, 8),
        ("9acdbdda97a7d21bf6ac", 90, 4, 17, 45, 5, 6),
        ("83ab58ab65f747391c75", 288, 4, 30, 144, 5, 6),
        ("810b191afaa80be65d6c", 248, 10, 18, 124, 7, 8),
        ("a7d34ec6316ee502929c", 90, 4, 17, 45, 5, 6),
        ("f403cce601f57461b568", 288, 4, 30, 144, 5, 6),
    ]
    selected = [
        selected_row(key, n=n, k=k, required=required, volume=volume)
        for key, n, k, required, volume, _lower, _unknown_at in specs
    ]
    results = [
        open_result(
            key,
            lower=lower,
            required=required,
            unknown_at=unknown_at,
            tag=index + 1,
        )
        for index, (
            key,
            _n,
            _k,
            required,
            _volume,
            lower,
            unknown_at,
        ) in enumerate(specs)
    ]
    # Meaningful LB rows with a trusted upper bound are already closed and
    # must not displace any of the nine fail-open candidates.
    closed = selected_row(
        "closed-lb9", n=210, k=8, required=13, volume=105
    )
    selected.append(closed)
    results.append({
        "candidate_key": "closed-lb9",
        "final_distance_lower_bound": 9,
        "trusted_distance_upper_bound": 10,
        "target_gap": 4,
        "unknown_fail_open": False,
        "rungs": [],
        "result_sha256": "f" * 64,
    })
    fake_diagnostic = {
        "root": Path("/tmp/sealed-diagnostic"),
        "contract": {"contract_sha256": "1" * 64},
        "contract_identity": {"path": "/tmp/contract", "bytes": 1, "sha256": "a" * 64},
        "selected": selected,
        "selected_identity": {"path": "/tmp/selected", "bytes": 1, "sha256": "b" * 64},
        "results": results,
        "results_identity": {"path": "/tmp/results", "bytes": 1, "sha256": "c" * 64},
        "decision": {
            "decision_sha256": "2" * 64,
            "action": "retain_generalized_toric_family_and_targeted_deep_proof",
            "reason": "survivor_or_lower_bound_signal",
            "meaningful_lb_ge_9": [
                "5c5ef6ca2ab6dfe179c0",
                "closed-lb9",
            ],
            "near_target_gap_le_3": [],
        },
        "decision_identity": {"path": "/tmp/decision", "bytes": 1, "sha256": "d" * 64},
    }
    monkeypatch.setattr(
        dual_track_module,
        "_load_replayed_diagnostic",
        lambda *_a, **_k: fake_diagnostic,
    )
    plan = build_dual_track_plan(
        Path("/tmp/sealed-diagnostic"),
        repo_dir=PROJECT,
        preregistration_path=DUAL_TRACK,
    )
    assert plan["fresh_ansatz_track"]["status"] == "READY_NOT_LAUNCHED"
    assert plan["fresh_ansatz_track"]["diagnostic_candidates_imported"] == 0
    assert plan["targeted_deep_proof_track"]["status"] == (
        "PLAN_READY_DRIVER_REQUIRED_NOT_LAUNCHED"
    )
    deep = plan["targeted_deep_proof_track"]
    assert deep["candidate_count"] == 9
    assert deep["active_candidate_count"] == 8
    assert deep["queued_candidate_count"] == 1
    assert deep["diagnostic_checkpoint_retry_candidate_count"] == 9
    assert deep["independent_certificate_candidate_count"] == 0
    assert "closed-lb9" not in {
        row["candidate_key"] for row in deep["candidates"]
    }
    first = deep["candidates"][0]
    assert first["candidate_key"] == "5c5ef6ca2ab6dfe179c0"
    assert first["resume_thresholds"] == [16]
    assert first["resume_ladder"][0]["retry_sectors"] == ["X", "Z"]
    assert first["next_route"] == "diagnostic_checkpoint_retry"
    assert first["scheduling_status"] == "ACTIVE_FIRST_BATCH"
    queued = [
        row for row in deep["candidates"]
        if row["scheduling_status"] == "QUEUED_DURABLE"
    ]
    assert len(queued) == 1
    assert queued[0]["candidate_key"] == "f403cce601f57461b568"
    assert queued[0]["resume_thresholds"] == [6, 8, 29]
    planned = {row["candidate_key"]: row for row in deep["candidates"]}
    assert planned["810b191afaa80be65d6c"]["resume_ladder"][0] == {
        "threshold": 8,
        "retry_sectors": ["X"],
        "replayed_unsat_sectors": ["Z"],
    }
    assert deep["stage3_ranked_schema_directly_consumable"] is False
    assert deep["dedicated_resumable_sector_driver_required"] is True
    assert plan["joint_decision"]["automatic_launch"] is False
    assert plan["joint_decision"][
        "retain_family_does_not_mean_reuse_fixed_ansatz"
    ] is True
    assert plan["joint_decision"]["action"] == (
        "prepare_fresh_richer_ansatz_and_separate_targeted_deep_proof"
    )


def test_dual_track_actual_threshold_survivor_routes_to_certificate(monkeypatch):
    selected = {
        "candidate_key": "threshold-survivor",
        "structural_digest": "threshold-structural",
        "triage_digest": "threshold-triage",
        "claim": {"ell": 1, "m": 144, "A_terms": [[0, 0]], "B_terms": [[0, 1]]},
        "n": 288,
        "k": 12,
        "target": {"required_distance": 17},
        "strata": {"published_volume": 144},
    }
    result = {
        "candidate_key": "threshold-survivor",
        "final_distance_lower_bound": 17,
        "trusted_distance_upper_bound": None,
        "target_gap": 0,
        "unknown_fail_open": False,
        "rungs": [],
        "result_sha256": "e" * 64,
    }
    fake_diagnostic = {
        "root": Path("/tmp/sealed-threshold-diagnostic"),
        "contract": {"contract_sha256": "1" * 64},
        "contract_identity": {"path": "/tmp/contract", "bytes": 1, "sha256": "a" * 64},
        "selected": [selected],
        "selected_identity": {"path": "/tmp/selected", "bytes": 1, "sha256": "b" * 64},
        "results": [result],
        "results_identity": {"path": "/tmp/results", "bytes": 1, "sha256": "c" * 64},
        "decision": {
            "decision_sha256": "2" * 64,
            "action": "retain_generalized_toric_family_and_targeted_deep_proof",
            "reason": "survivor_or_lower_bound_signal",
            "meaningful_lb_ge_9": ["threshold-survivor"],
            "near_target_gap_le_3": ["threshold-survivor"],
        },
        "decision_identity": {"path": "/tmp/decision", "bytes": 1, "sha256": "d" * 64},
    }
    monkeypatch.setattr(
        dual_track_module,
        "_load_replayed_diagnostic",
        lambda *_a, **_k: fake_diagnostic,
    )
    plan = build_dual_track_plan(
        Path("/tmp/sealed-threshold-diagnostic"),
        repo_dir=PROJECT,
        preregistration_path=DUAL_TRACK,
    )
    assert plan["fresh_ansatz_track"]["status"] == (
        "PREPARED_HELD_FOR_CERTIFICATE_DECISION"
    )
    candidate = plan["targeted_deep_proof_track"]["candidates"][0]
    assert candidate["threshold_survivor"] is True
    assert candidate["next_route"] == "independent_exact_certificate"
