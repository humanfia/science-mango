import copy
import hashlib
import json
from pathlib import Path

import pytest

import evaluation.evaluator as candidate_evaluator
import evolve.run_evolution as evolution_launcher
import humanize.flow as flow_module
from humanize.flow import (
    FlowConfig,
    HumanizeFlow,
    RoundTransactionError,
)
from humanize.reviewer import validate_review
from humanize.state import atomic_write_json


def candidate(tag: int) -> dict:
    return {
        "ell": 6 + tag,
        "m": 6,
        "n": 12 * (6 + tag),
        "k": 8,
        "d": 6,
        "fom": float(6 + tag),
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
    }


def sealed_lower_bound_candidate(
    lower_bound: int,
    *,
    complete: bool,
) -> dict:
    row = candidate(0)
    row.pop("d")
    row["candidate_sha256"] = "a" * 64
    threshold = lower_bound - 1
    evidence = {
        "schema_version": 1,
        "kind": "qcode-css-low-weight-oracle",
        "outcome": "UNSAT",
        "decision_complete": True,
        "retryable": False,
        "max_weight": threshold,
        "distance_lower_bound": lower_bound,
        "witness": None,
    }
    evidence["evidence_sha256"] = flow_module._canonical_payload_sha256(
        evidence
    )
    ledger = {
        "kind": "qcode-coset-stage1-proof-ledger-v1",
        "schema_version": 1,
        "proof_ladder_version": 2,
        "candidate_sha256": row["candidate_sha256"],
        "entries": [{
            "threshold": threshold,
            "outcome": "UNSAT",
            "evidence_sha256": evidence["evidence_sha256"],
            "cache_sha256": "b" * 64,
        }],
    }
    ledger["root_sha256"] = flow_module._canonical_payload_sha256(ledger)
    row.update({
        "distance_lower_bound": lower_bound,
        "distance_lower_bound_proven": True,
        "distance_lower_bound_status": "search_oracle_proven",
        "distance_lower_bound_evidence": evidence,
        "distance_lower_bound_evidence_sha256": evidence[
            "evidence_sha256"
        ],
        "proof_ledger": ledger,
        "oracle_ladder_complete": complete,
        "challenge_target_lower_bound_proven": complete,
        "search_status": (
            "challenge_threshold_survivor"
            if complete else "partial_lower_bound_retry"
        ),
    })
    return row


def jsonl(*rows: dict) -> bytes:
    return b"".join(
        (json.dumps(row) + "\n").encode("utf-8") for row in rows
    )


def write_launch_inputs(
    repo: Path,
    *,
    portfolio: bool = False,
    legacy_portfolio: bool = False,
    geometry_portfolio: bool = False,
    coset_portfolio: bool = False,
) -> None:
    assert sum((
        portfolio,
        legacy_portfolio,
        geometry_portfolio,
        coset_portfolio,
    )) <= 1
    evolve = repo / "evolve"
    evolve.mkdir(parents=True, exist_ok=True)
    config_text = "evaluator:\n  parallel_evaluations: 1\n"
    if portfolio:
        config_text += (
            "database:\n"
            "  num_islands: 5\n"
            "  feature_dimensions:\n"
            "    - algebraic_relation_type\n"
            "    - support_split_type\n"
            "    - orbit_span_bin\n"
            "  feature_bins:\n"
            "    algebraic_relation_type: 5\n"
            "    support_split_type: 6\n"
            "    orbit_span_bin: 3\n"
            "qcode_search_portfolio:\n"
            "  enabled: true\n"
            "  schema_version: 2\n"
        )
    elif geometry_portfolio:
        config_text += (
            "database:\n"
            "  num_islands: 5\n"
            "  feature_dimensions:\n"
            "    - algebraic_relation_type\n"
            "    - support_split_type\n"
            "    - geometry_twist_class\n"
            "  feature_bins:\n"
            "    algebraic_relation_type: 5\n"
            "    support_split_type: 6\n"
            "    geometry_twist_class: 3\n"
            "qcode_search_portfolio:\n"
            "  enabled: true\n"
            "  schema_version: 3\n"
        )
    elif legacy_portfolio:
        config_text += (
            "database:\n"
            "  num_islands: 5\n"
            "  feature_dimensions:\n"
            "    - pattern_type\n"
            "    - support_split_type\n"
            "    - search_structural_entropy\n"
            "  feature_bins:\n"
            "    pattern_type: 6\n"
            "    support_split_type: 6\n"
            "    search_structural_entropy: 5\n"
            "qcode_search_portfolio:\n"
            "  enabled: true\n"
            "  schema_version: 1\n"
        )
    elif coset_portfolio:
        config_text += (
            "database:\n"
            "  num_islands: 4\n"
            "  feature_dimensions:\n"
            "    - coset_nonnormal_lane_bucket\n"
            "    - coset_normal_lane_bucket\n"
            "    - coset_batch_orbit_profile_bucket\n"
            "  feature_bins:\n"
            "    coset_nonnormal_lane_bucket: 16\n"
            "    coset_normal_lane_bucket: 16\n"
            "    coset_batch_orbit_profile_bucket: 8\n"
            "qcode_coset_search_portfolio:\n"
            "  enabled: true\n"
            "  schema_version: 3\n"
            "  representation_id: css-coset-two-block-actions-v2\n"
            "  checkpoint_compatibility_group: "
            "coset-two-block-catalog-v2-dsl-map-v3-proof-ladder-v3\n"
            "qcode_coset_stage1_proof_ladder:\n"
            "  enabled: true\n"
            "  schema_version: 3\n"
            "  target_mode: scalar-fom-strict-v1\n"
            "  start_weight: 4\n"
            "  weight_step: 2\n"
            "  max_candidates_per_batch: 24\n"
            "  max_new_steps_per_batch: 24\n"
            "  batch_wall_timeout_s: 720.0\n"
            "  step_hard_timeout_s: 120.0\n"
            "  retry_timeouts_s: [7.5, 15.0, 30.0, 120.0]\n"
            "  global_frontier_injections: 4\n"
            "  cache_directory: .coset-stage1-proof-cache-v3\n"
        )
    (evolve / "config.yaml").write_text(config_text)
    (evolve / "seed_solution.py").write_text(
        "def generate_candidates(): return []\n"
    )
    (evolve / "run_evolution.py").write_text("# launcher\n")
    (evolve / "openevolve_evaluator.py").write_text("# evaluator\n")
    (evolve / "codex_cli_llm.py").write_text("# codex backend\n")
    for relative_path in flow_module.LOCAL_EVOLUTION_DEPENDENCIES.values():
        dependency = repo / relative_path
        dependency.parent.mkdir(parents=True, exist_ok=True)
        dependency.write_text(f"# dependency {relative_path}\n")
    sources = repo / "fake-openevolve"
    sources.mkdir(exist_ok=True)
    for name in ("controller", "process_parallel", "database", "api", "evaluator"):
        (sources / f"{name}.py").write_text(f"# fake {name}\n")


def write_coset_launch_inputs(repo: Path) -> None:
    write_launch_inputs(repo, coset_portfolio=True)
    project = Path(flow_module.__file__).resolve().parents[1]
    for relative_path in flow_module.COSET_EVALUATOR_DEPENDENCIES.values():
        destination = repo / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((project / relative_path).read_bytes())
    (repo / "evolve/coset_openevolve_evaluator.py").write_text(
        "# fake coset evaluator\n"
    )


def test_v2_coset_managed_launch_binds_v2_catalog(tmp_path):
    project = Path(flow_module.__file__).resolve().parents[1]
    round_dir = tmp_path / "round-001"
    round_dir.mkdir()
    context = round_dir / "context.md"
    context.write_text("v2 launch context\n")
    config = FlowConfig(
        repo_dir=project,
        run_id="coset-v2-catalog-binding",
        evolution_config=project / "evolve/coset_config_v2.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v2.py",
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )

    launch = flow_module._evolution_launch_binding(
        config,
        context_path=context,
    )
    invocation = flow_module._fresh_invocation_binding(
        config,
        codex_identity=None,
        codex_version=None,
        codex_cwd=None,
        launch_binding=launch,
    )
    validated = flow_module._validate_invocation_binding(
        config,
        invocation,
        launch,
    )
    portfolio = flow_module._coset_search_portfolio_contract_from_config(
        project / "evolve/coset_config_v2.yaml"
    )

    assert portfolio is not None
    assert portfolio[0] == 3
    assert flow_module._coset_action_catalog_dependency_key(config) == (
        "coset_action_catalog_v2"
    )
    assert validated["qcode_action_catalog_sha256"] == (
        launch["coset_action_catalog_v2"]["sha256"]
    )
    assert validated["qcode_action_catalog_sha256"] != (
        launch["coset_action_catalog"]["sha256"]
    )


def write_checkpoint(
    repo: Path,
    run_id: str,
    iteration: int,
    *,
    coset_policy: bool = False,
    child_iteration: int = 1,
) -> Path:
    checkpoint = (
        repo
        / "results/evolution"
        / f"humanize_{run_id}"
        / "checkpoints"
        / f"checkpoint_{iteration}"
    )
    programs = checkpoint / "programs"
    programs.mkdir(parents=True, exist_ok=True)
    program_id = "program"
    if coset_policy:
        from evolve.coset_policy_dsl import (
            canonical_policy_json,
            default_policy,
        )

        code = canonical_policy_json(default_policy())
    else:
        code = "def generate_candidates():\n    return []\n"
    archive = [program_id]
    best_program_id = program_id
    if coset_policy:
        archive.append("evicted-child")
        best_program_id = "evicted-child"
    atomic_write_json(checkpoint / "metadata.json", {
        "last_iteration": iteration,
        "archive": archive,
        "best_program_id": best_program_id,
        "islands": [archive],
        "island_best_programs": [best_program_id],
        "island_feature_maps": [{"cell": best_program_id}],
    })
    atomic_write_json(checkpoint / "best_program_info.json", {
        "id": best_program_id,
        "current_iteration": iteration,
    })
    atomic_write_json(programs / f"{program_id}.json", {
        "id": program_id,
        "code": code,
        "metrics": {},
        "iteration_found": 0 if coset_policy else iteration,
        **(
            {"language": "json", "parent_id": None}
            if coset_policy
            else {}
        ),
    })
    if coset_policy:
        atomic_write_json(programs / "evicted-child.json", {
            "id": "evicted-child",
            "code": code,
            "metrics": {},
            "iteration_found": child_iteration,
            "language": "json",
            "parent_id": program_id,
        })
    (checkpoint / "best_program.py").write_text(code)
    return checkpoint


def _activation_bridge_replay_fixture(
    tmp_path: Path,
    *,
    support_splits: tuple[tuple[int, int], ...] = ((2, 4),),
) -> tuple[dict, dict]:
    from evolve.coset_policy_dsl_v3 import (
        canonical_policy_json,
        default_policy,
        policy_digest,
    )
    from evolve.coset_search_contract import (
        activate_coset_renderer_proposal,
        coset_renderer_activation_document,
        coset_renderer_proposal_document,
    )

    split = list(support_splits[0])
    multi_split = len(support_splits) > 1
    activation = coset_renderer_activation_document(
        activate_coset_renderer_proposal(
            coset_renderer_proposal_document(
                support_splits=support_splits
            )
        )
    )
    activation_path = tmp_path / "coset-renderer-activation.json"
    atomic_write_json(activation_path, activation)

    source_policy = default_policy(support_split=(3, 3))
    source_code = canonical_policy_json(source_policy) + "\n"
    base_path = tmp_path / "checkpoint_25"
    (base_path / "programs").mkdir(parents=True)
    atomic_write_json(base_path / "programs/source.json", {
        "id": "source",
        "code": source_code,
        "metrics": {},
    })
    base_checkpoint = {
        "path": str(base_path.resolve()),
        "last_iteration": 25,
        "sha256": "a" * 64,
        "programs": 1,
    }
    source_program_set_sha256 = (
        flow_module._checkpoint_program_set_sha256(base_checkpoint)
    )

    root_policy = default_policy(support_split=tuple(split))
    root_code = canonical_policy_json(root_policy) + "\n"
    root_policy_sha256 = policy_digest(root_policy)
    root_code_sha256 = hashlib.sha256(root_code.encode("utf-8")).hexdigest()
    contract_id = 17
    root_binding = {
        "schema_version": 2 if multi_split else 1,
        "kind": "qcode-coset-activation-bridge-root",
        "source_checkpoint_sha256": base_checkpoint["sha256"],
        "source_program_set_sha256": source_program_set_sha256,
        "source_last_iteration": base_checkpoint["last_iteration"],
        "activation_sha256": activation["activation_sha256"],
        "policy_sha256": root_policy_sha256,
        "code_sha256": root_code_sha256,
        "contract_id": contract_id,
    }
    if multi_split:
        root_binding["approved_support_splits"] = [
            list(value) for value in support_splits
        ]
        root_binding["root_support_split"] = split
    else:
        root_binding["approved_support_split"] = split
    root_id = "coset-activation-root-" + hashlib.sha256(
        json.dumps(
            root_binding,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("utf-8")
    ).hexdigest()[:32]
    result_path = tmp_path / "checkpoint_50"
    (result_path / "programs").mkdir(parents=True)
    atomic_write_json(result_path / "programs" / f"{root_id}.json", {
        "id": root_id,
        "code": root_code,
        "metrics": {"combined_score": 0.25},
        "parent_id": None,
        "iteration_found": base_checkpoint["last_iteration"],
        "language": "json",
        "metadata": {
            "island": 0,
            "checkpoint_activation_bridge": root_binding,
        },
    })
    result_checkpoint = {
        "path": str(result_path.resolve()),
        "last_iteration": 50,
        "sha256": "b" * 64,
        "programs": 1,
    }

    candidate_log = tmp_path / "all_codes.jsonl"
    candidate_log.write_bytes(b'{"bridge":true}\n')
    bridge_range = flow_module._candidate_log_range_identity(
        candidate_log,
        start_offset=0,
    )
    bridge_range = {
        name: bridge_range[name]
        for name in (
            "path",
            "start_offset",
            "end_offset",
            "sha256",
            "bytes",
            "wal_clean",
        )
    }
    report = {
        "schema_version": 4 if multi_split else 3,
        "status": "completed",
        "contract_version": 2,
        "contract_id": contract_id,
        "mode": "typed-json-dsl-activation-bridge-root",
        "source_checkpoint": base_checkpoint,
        "source_programs": base_checkpoint["programs"],
        "source_program_set_sha256": source_program_set_sha256,
        "target_programs": 1,
        "root_program_id": root_id,
        "root_policy_sha256": root_policy_sha256,
        "root_code_sha256": root_code_sha256,
        "activation_sha256": activation["activation_sha256"],
        "bridge_candidate_range": bridge_range,
    }
    if multi_split:
        report["approved_support_splits"] = [
            list(value) for value in support_splits
        ]
        report["root_support_split"] = split
    else:
        report["approved_support_split"] = split
    arguments = {
        "base_checkpoint": base_checkpoint,
        "result_checkpoint": result_checkpoint,
        "launch_binding": {
            "coset_renderer_activation": flow_module._file_descriptor(
                activation_path, "test renderer activation"
            )
        },
        "invocation_binding": {
            "qcode_action_catalog_sha256": (
                root_policy.action_catalog_sha256
            ),
            "qcode_coset_renderer_activation_sha256": activation[
                "activation_sha256"
            ],
        },
        "candidate_log": candidate_log,
        "candidate_start_offset": 0,
        "candidate_end_offset": bridge_range["end_offset"],
        "expected_representation_id": (
            flow_module.COSET_REPRESENTATION_ID_V3
        ),
    }
    return report, arguments


def test_checkpoint_activation_bridge_preflight_replays_exactly(tmp_path):
    report, arguments = _activation_bridge_replay_fixture(tmp_path)

    flow_module._validate_checkpoint_activation_bridge_preflight(
        report, **arguments
    )


def test_multisplit_checkpoint_activation_bridge_preflight_replays_exactly(
    tmp_path,
):
    report, arguments = _activation_bridge_replay_fixture(
        tmp_path,
        support_splits=((2, 4), (2, 3), (3, 2), (3, 3)),
    )

    assert report["schema_version"] == 4
    assert report["root_support_split"] == [2, 4]
    flow_module._validate_checkpoint_activation_bridge_preflight(
        report, **arguments
    )


def test_checkpoint_activation_bridge_schema_v4_requires_multiple_splits(
    tmp_path,
):
    report, arguments = _activation_bridge_replay_fixture(tmp_path)
    split = report.pop("approved_support_split")
    report["schema_version"] = 4
    report["approved_support_splits"] = [split]
    report["root_support_split"] = split

    with pytest.raises(
        RoundTransactionError,
        match="checkpoint activation bridge support split is invalid",
    ):
        flow_module._validate_checkpoint_activation_bridge_preflight(
            report, **arguments
        )


@pytest.mark.parametrize(
    "tamper",
    ("approved_splits", "root_split", "root_metadata"),
)
def test_multisplit_checkpoint_activation_bridge_rejects_tampering(
    tmp_path,
    tamper,
):
    report, arguments = _activation_bridge_replay_fixture(
        tmp_path,
        support_splits=((2, 4), (2, 3), (3, 2), (3, 3)),
    )
    report = copy.deepcopy(report)
    if tamper == "approved_splits":
        report["approved_support_splits"] = [[2, 4], [3, 2]]
    elif tamper == "root_split":
        report["root_support_split"] = [3, 2]
    else:
        root_path = (
            Path(arguments["result_checkpoint"]["path"])
            / "programs"
            / f"{report['root_program_id']}.json"
        )
        root = json.loads(root_path.read_text())
        root["metadata"]["checkpoint_activation_bridge"][
            "approved_support_splits"
        ] = [[2, 4]]
        atomic_write_json(root_path, root)

    with pytest.raises(
        RoundTransactionError, match="checkpoint activation bridge"
    ):
        flow_module._validate_checkpoint_activation_bridge_preflight(
            report, **arguments
        )


@pytest.mark.parametrize(
    "tamper",
    (
        "extra_field",
        "activation",
        "support_split",
        "candidate_range",
        "source_population",
        "root_metadata",
        "root_parent",
    ),
)
def test_checkpoint_activation_bridge_preflight_rejects_tampering(
    tmp_path,
    tamper,
):
    report, arguments = _activation_bridge_replay_fixture(tmp_path)
    report = copy.deepcopy(report)
    if tamper == "extra_field":
        report["unexpected"] = True
    elif tamper == "activation":
        report["activation_sha256"] = "0" * 64
    elif tamper == "support_split":
        report["approved_support_split"] = [4, 2]
    elif tamper == "candidate_range":
        report["bridge_candidate_range"]["sha256"] = "0" * 64
    elif tamper == "source_population":
        report["source_program_set_sha256"] = "0" * 64
    else:
        root_path = (
            Path(arguments["result_checkpoint"]["path"])
            / "programs"
            / f"{report['root_program_id']}.json"
        )
        root = json.loads(root_path.read_text())
        if tamper == "root_metadata":
            root["metadata"]["checkpoint_activation_bridge"][
                "activation_sha256"
            ] = "0" * 64
        else:
            assert tamper == "root_parent"
            root["parent_id"] = "source"
        atomic_write_json(root_path, root)

    with pytest.raises(
        RoundTransactionError, match="checkpoint activation bridge"
    ):
        flow_module._validate_checkpoint_activation_bridge_preflight(
            report, **arguments
        )


def write_full_slice_proof(
    flow: HumanizeFlow,
    round_dir: Path,
    checkpoint: Path,
    base: dict | None,
    *,
    schema_version: int = (
        flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
    ),
    all_invalid_mutations: bool = False,
    mutation_error_kind: str = "invalid_mutation",
) -> None:
    config = flow.config
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output, checkpoint
    )
    base_iteration = 0 if base is None else base["last_iteration"]
    count = config.iterations_per_round
    error = b"test worker error"
    transaction = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    candidate_source = (
        flow_module._candidate_log_range_identity(
            flow.candidate_log,
            start_offset=int(transaction["candidate_start_offset"]),
        )
        if schema_version in {
            flow_module.EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION,
            flow_module.EVOLUTION_SLICE_WITNESS_PRE_EVALUATOR_BINDING_SCHEMA_VERSION,
            6,
            flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
        }
        else None
    )
    launch = transaction["launch_binding"]
    invocation = transaction["invocation_binding"]
    start = base_iteration + 1
    parent_checkpoint_path = Path(
        result["path"] if base is None else base["path"]
    )
    program = json.loads(
        (
            parent_checkpoint_path
            / "programs"
            / "program.json"
        ).read_text()
    )
    program["id"] = "evicted-child"
    program["iteration_found"] = start
    if program.get("language") == "json":
        program["parent_id"] = "program"
    encoded_program = json.dumps(
        program,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode()
    witness_path = flow_module._slice_witness_path(round_dir)
    portfolio_contract = None
    if (
        schema_version
        == flow_module.EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION
    ):
        portfolio_enabled = (
            flow_module._legacy_v4_search_portfolio_enabled_from_config(
                Path(launch["config"]["path"])
            )
        )
    else:
        portfolio_contract = (
            flow_module._search_portfolio_contract_from_config(
                Path(launch["config"]["path"])
            )
        )
        portfolio_enabled = portfolio_contract is not None
    coset_portfolio_contract = (
        flow_module._coset_search_portfolio_contract_from_config(
            Path(launch["config"]["path"])
        )
    )
    coset_portfolio_enabled = coset_portfolio_contract is not None
    assert not (portfolio_enabled and coset_portfolio_enabled)
    attempts = [
        {"iteration": i, "island_id": 0, "result": "future"}
        for i in range(base_iteration + 1, base_iteration + count + 1)
    ]
    search_portfolio = None
    if (
        schema_version
        == flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
        and coset_portfolio_enabled
    ):
        parent_code = json.loads(
            (
                parent_checkpoint_path
                / "programs"
                / "program.json"
            ).read_text()
        )["code"]
        parent_code_sha256 = hashlib.sha256(
            parent_code.encode()
        ).hexdigest()
        attempts = [
            {
                "iteration": iteration,
                "island_id": (
                    (iteration - 1)
                    % flow_module.COSET_SEARCH_PORTFOLIO_ISLAND_COUNT
                ),
                "result": "future",
                "coset_parent_program_id": "program",
                "coset_parent_code_sha256": parent_code_sha256,
            }
            for iteration in range(start, start + count)
        ]
    elif (
        schema_version
        in flow_module.EVOLUTION_SLICE_WITNESS_MECHANISM_SCHEMA_VERSIONS
        and portfolio_enabled
    ):
        assert portfolio_contract is not None
        portfolio_schema, feature_dimensions, _feature_bins = (
            portfolio_contract
        )
        policy = flow_module._adaptive_mutation_policy_from_context(
            Path(launch["context"]["path"])
        )
        policy_sha256 = (
            flow_module._adaptive_mutation_policy_sha256(policy)
        )
        regime = flow_module._search_regime_policy_from_context(
            Path(launch["context"]["path"])
        )
        schedule = flow_module._search_island_schedule(
            count, str(regime["status"])
        )
        parent_code = json.loads(
            (
                parent_checkpoint_path
                / "programs"
                / "program.json"
            ).read_text()
        )["code"]
        parent_code_sha256 = hashlib.sha256(
            parent_code.encode()
        ).hexdigest()
        role_counts = {
            role: schedule.count(island)
            for island, role in enumerate(
                flow_module.SEARCH_PORTFOLIO_ROLES
            )
        }
        attempts = []
        for iteration in range(start, start + count):
            island = schedule[iteration - start]
            attempts.append({
                "iteration": iteration,
                "island_id": island,
                "result": "future",
                "search_portfolio_schema_version": (
                    portfolio_schema
                ),
                "search_policy_sha256": policy_sha256,
                "search_regime_status": regime["status"],
                "search_role":
                    flow_module.SEARCH_PORTFOLIO_ROLES[island],
                "search_tactic":
                    flow_module._adaptive_mutation_tactic_from_parent_hash(
                        policy,
                        parent_code_sha256=parent_code_sha256,
                        iteration=iteration,
                    ),
                "search_parent_program_id": "program",
                "search_parent_code_sha256": parent_code_sha256,
                "search_role_submission_counts": role_counts,
            })
        search_portfolio = {
            "schema_version": portfolio_schema,
            "island_count": flow_module.SEARCH_PORTFOLIO_ISLAND_COUNT,
            "roles": list(flow_module.SEARCH_PORTFOLIO_ROLES),
            "feature_dimensions": list(
                feature_dimensions
            ),
            "regime_status": regime["status"],
            "policy_sha256": policy_sha256,
            "role_submission_counts": role_counts,
        }
    elif (
        schema_version
        == flow_module.EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION
        and portfolio_enabled
    ):
        policy = flow_module._adaptive_mutation_policy_from_context(
            Path(launch["context"]["path"])
        )
        policy_sha256 = flow_module._adaptive_mutation_policy_sha256(policy)
        parent_code = json.loads(
            (
                parent_checkpoint_path
                / "programs"
                / "program.json"
            ).read_text()
        )["code"]
        parent_code_sha256 = hashlib.sha256(
            parent_code.encode()
        ).hexdigest()
        roles = flow_module.LEGACY_V4_SEARCH_PORTFOLIO_ROLES
        role_counts = {
            role: sum(
                (iteration - start) % flow_module.SEARCH_PORTFOLIO_ISLAND_COUNT
                == island
                for iteration in range(start, start + count)
            )
            for island, role in enumerate(roles)
        }
        attempts = []
        for iteration in range(start, start + count):
            island = (
                iteration - start
            ) % flow_module.SEARCH_PORTFOLIO_ISLAND_COUNT
            attempts.append({
                "iteration": iteration,
                "island_id": island,
                "result": "future",
                "search_portfolio_schema_version": (
                    flow_module.LEGACY_V4_SEARCH_PORTFOLIO_SCHEMA_VERSION
                ),
                "search_policy_sha256": policy_sha256,
                "search_role": roles[island],
                "search_tactic": (
                    flow_module._adaptive_mutation_tactic_from_parent_hash(
                        policy,
                        parent_code_sha256=parent_code_sha256,
                        iteration=iteration,
                    )
                ),
                "search_parent_program_id": "program",
                "search_parent_code_sha256": parent_code_sha256,
                "search_role_submission_counts": role_counts,
            })
        search_portfolio = {
            "schema_version": (
                flow_module.LEGACY_V4_SEARCH_PORTFOLIO_SCHEMA_VERSION
            ),
            "island_count": flow_module.SEARCH_PORTFOLIO_ISLAND_COUNT,
            "roles": list(roles),
            "policy_sha256": policy_sha256,
            "role_submission_counts": role_counts,
        }
    outcomes = (
        [
            {
                "iteration": i,
                "status": "worker_error",
                "error_sha256": hashlib.sha256(error).hexdigest(),
                "error_bytes": len(error),
                "error_kind": mutation_error_kind,
            }
            for i in range(start, base_iteration + count + 1)
        ]
        if all_invalid_mutations
        else [{
            "iteration": start,
            "status": "program_added",
            "program_id": "evicted-child",
            "program_sha256": hashlib.sha256(encoded_program).hexdigest(),
            "program_bytes": len(encoded_program),
        }] + [
            {
                "iteration": i,
                "status": "worker_error",
                "error_sha256": hashlib.sha256(error).hexdigest(),
                "error_bytes": len(error),
            }
            for i in range(start + 1, base_iteration + count + 1)
        ]
    )
    witness = {
        "schema_version": schema_version,
        "status": "completed",
        "output_dir": str(flow.evolution_output.resolve()),
        "resume_checkpoint": None if base is None else base["path"],
        "base_last_iteration": base_iteration,
        "iterations_requested": count,
        "slice_start_iteration": base_iteration + 1,
        "slice_end_iteration": base_iteration + count,
        "slice_iteration_count": count,
        "slice_iterations_sha256": flow_module._slice_iterations_sha256(
            base_iteration + 1, count
        ),
        "submission_attempts": attempts,
        "outcomes": outcomes,
        "successful_evaluations": 0 if all_invalid_mutations else 1,
        "worker_errors": count if all_invalid_mutations else count - 1,
        "checkpoint_saves": [{
            "iteration": base_iteration + count,
            "accounting_complete": True,
            "checkpoint_sha256": result["sha256"],
            "checkpoint_programs": result["programs"],
        }],
        "result_checkpoint": result["path"],
        "result_last_iteration": result["last_iteration"],
        "result_checkpoint_sha256": result["sha256"],
        "result_checkpoint_programs": result["programs"],
        "openevolve_version": "0.2.26",
        "completed_at": "test",
    }
    if (
        schema_version == flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
        and base is not None
    ):
        # Schema 7 seals the checkpoint preflight that ran before any resumed
        # mutation was submitted.  Most transaction tests use a synthetic,
        # already-complete checkpoint rather than the one-time coset DSL
        # migration, so model the ordinary schema-1 backfill report here.
        witness["checkpoint_preflight"] = {
            "schema_version": 1,
            "status": "completed",
            "contract_version": 2,
            "contract_id": 0,
            "programs": base["programs"],
            "unique_program_codes": base["programs"],
            "programs_already_complete": base["programs"],
            "unique_program_codes_evaluated": 0,
            "programs_updated": 0,
            "worker_cap": 1,
        }
    if schema_version in (
        flow_module.EVOLUTION_SLICE_WITNESS_PORTFOLIO_SCHEMA_VERSIONS
    ):
        witness["search_portfolio"] = search_portfolio
    if candidate_source is not None:
        witness.update({
            "candidate_log_path": candidate_source["path"],
            "candidate_log_device": candidate_source["device"],
            "candidate_log_inode": candidate_source["inode"],
            "candidate_start_offset": candidate_source["start_offset"],
            "candidate_end_offset": candidate_source["end_offset"],
            "candidate_range_sha256": candidate_source["sha256"],
            "candidate_range_bytes": candidate_source["bytes"],
            "candidate_wal_clean": candidate_source["wal_clean"],
        })
    for name, descriptor in launch.items():
        for field in ("path", "sha256", "bytes"):
            witness[f"{name}_{field}"] = descriptor[field]
    witness.update(invocation)
    sources = config.repo_dir / "fake-openevolve"
    source_names = ["controller", "process_parallel", "database", "api"]
    if schema_version in {
        6,
        flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
    }:
        source_names.append("evaluator")
    for name in source_names:
        descriptor = flow_module._file_descriptor(
            sources / f"{name}.py", "fake OpenEvolve source"
        )
        for field in ("path", "sha256", "bytes"):
            witness[f"openevolve_{name}_{field}"] = descriptor[field]
    atomic_write_json(witness_path, witness)
    witness_descriptor = flow_module._file_descriptor(
        witness_path, "test slice witness"
    )
    witness_descriptor["schema_version"] = witness["schema_version"]
    if schema_version in {
        flow_module.EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION,
        flow_module.EVOLUTION_SLICE_WITNESS_PRE_EVALUATOR_BINDING_SCHEMA_VERSION,
        6,
        flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
    }:
        witness_descriptor.update({
            field: witness[field]
            for field in flow_module.CANDIDATE_WITNESS_FIELDS
        })
    marker = flow_module._completion_marker_expected(
        config, base, result, launch, invocation, witness_descriptor
    )
    marker["completed_at"] = "test"
    atomic_write_json(flow_module._completion_marker_path(round_dir), marker)


class Reviewer:
    def review(self, _prompt, _round_dir):
        return validate_review({
            "verdict": "continue",
            "summary": "transaction recovery test",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        })


def test_first_v1_round_archives_legacy_tail_and_partial_line(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-tail",
        max_rounds=2,
        iterations_per_round=25,
        milp_top=0,
    )
    prefix_row = candidate(0)
    abandoned_row = candidate(1)
    retry_row = candidate(2)
    prefix = jsonl(prefix_row)
    abandoned_tail = jsonl(abandoned_row) + b'{"partial":'
    base = write_checkpoint(repo, config.run_id, 25)

    runner_calls = []

    def runner(_config, _state, _round_dir):
        runner_calls.append(True)
        assert candidate_log.read_bytes() == prefix
        with candidate_log.open("ab") as stream:
            stream.write(jsonl(retry_row))
        checkpoint = write_checkpoint(repo, config.run_id, 50)
        base_descriptor = flow_module._checkpoint_descriptor(
            flow.evolution_output, base
        )
        write_full_slice_proof(
            flow, round_two, checkpoint, base_descriptor
        )
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    state.update({
        "current_round": 1,
        "candidate_offset": len(prefix),
        "last_checkpoint": str(base.resolve()),
    })
    flow.store.write_state(state)
    candidate_log = flow.candidate_log
    candidate_log.parent.mkdir(parents=True, exist_ok=True)
    candidate_log.write_bytes(prefix + abandoned_tail)

    round_one = flow.store.round_dir(1)
    (round_one / "candidates.jsonl").write_bytes(prefix)
    flow._materialize_legacy_batch(
        1,
        round_one,
        round_one / "candidates.jsonl",
        binding={"kind": "test-history"},
    )
    round_two = flow.store.round_dir(2)
    rows = flow._capture_round_candidates(state, 2, round_two)

    assert runner_calls == [True]
    assert rows == [retry_row]
    assert candidate_log.read_bytes() == prefix + jsonl(retry_row)
    archive = round_two / "abandoned-candidate-tail-001.bin"
    assert archive.read_bytes() == abandoned_tail
    manifest = json.loads(
        (round_two / "evolution-transaction.json").read_text()
    )
    assert manifest["abandoned_ranges"][0]["partial_bytes"] == 11
    salvaged = round_two / "abandoned-candidate-complete-001.jsonl"
    assert salvaged.read_bytes() == jsonl(abandoned_row)
    assert manifest["abandoned_ranges"][0]["complete_candidate_batch"] == {
        "path": str(salvaged.resolve()),
        "sha256": hashlib.sha256(jsonl(abandoned_row)).hexdigest(),
        "bytes": len(jsonl(abandoned_row)),
        "rows": 1,
    }

    state["current_round"] = 2
    state.pop("pending_round", None)
    state.pop("round_phase", None)
    flow.store.write_state(state)
    inputs = flow.pipeline_candidate_inputs
    assert len(inputs) == 3
    assert inputs[1] == salvaged
    assert inputs[1].read_bytes() == jsonl(abandoned_row)
    assert inputs[2].read_bytes() == jsonl(retry_row)

    salvaged.write_bytes(jsonl(candidate(99)))
    with pytest.raises(
        RoundTransactionError,
        match="abandoned complete candidate batch changed",
    ):
        _ = flow.pipeline_candidate_inputs


def test_first_prepare_rejects_stale_intermediate_checkpoint(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="stale-intermediate",
        iterations_per_round=25,
        milp_top=0,
    )
    calls = []

    def must_not_run(*_args):
        calls.append(True)
        raise AssertionError("stale checkpoint frontier reran evolution")

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=must_not_run
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    stale = write_checkpoint(repo, config.run_id, 10)

    with pytest.raises(RoundTransactionError, match="unbound checkpoint"):
        flow._capture_round_candidates(state, 1, round_dir)

    assert calls == []
    assert stale.is_dir()
    assert not (round_dir / "evolution-transaction.json").exists()


def test_prepared_transaction_adopts_complete_checkpoint_after_crash(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="adopt-checkpoint",
        iterations_per_round=25,
        milp_top=0,
    )
    row = candidate(3)
    calls = []

    def crashes_after_checkpoint(_config, _state, _round_dir):
        calls.append(True)
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(jsonl(row))
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(flow, _round_dir, checkpoint, None)
        raise SystemExit(99)

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=crashes_after_checkpoint
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    with pytest.raises(SystemExit) as raised:
        flow._capture_round_candidates(state, 1, round_dir)
    assert raised.value.code == 99

    def must_not_rerun(*_args):
        raise AssertionError("completed checkpoint was rerun")

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=must_not_rerun
    )
    recovered_state = resumed.store.load_state()
    rows = resumed._capture_round_candidates(
        recovered_state, 1, round_dir
    )
    assert calls == [True]
    assert rows == [row]
    marker = json.loads((round_dir / "openevolve-completed.json").read_text())
    assert marker["schema_version"] == (
        flow_module.EVOLUTION_COMPLETION_SCHEMA_VERSION
    )
    assert (round_dir / "openevolve-slice-witness.json").is_file()


def test_prepared_legacy_proof_with_partial_tail_is_quarantined_and_rerun(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="adopt-checkpoint-partial",
        iterations_per_round=25,
        milp_top=0,
    )
    row = candidate(5)
    fragment = b'{"partial":'
    original_tail = jsonl(row) + fragment
    calls = []

    def crashes_after_checkpoint(_config, _state, _round_dir):
        calls.append(True)
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(original_tail)
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(
            flow,
            _round_dir,
            checkpoint,
            None,
            schema_version=2,
        )
        raise SystemExit(99)

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=crashes_after_checkpoint
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    with pytest.raises(SystemExit):
        flow._capture_round_candidates(state, 1, round_dir)

    def rerun_without_unbound_tail(_config, _state, runner_round):
        calls.append("replayed")
        assert flow.candidate_log.read_bytes() == b""
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(resumed, runner_round, checkpoint, None)
        return checkpoint

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=rerun_without_unbound_tail
    )
    recovered = resumed.store.load_state()
    rows = resumed._capture_round_candidates(recovered, 1, round_dir)

    assert calls == [True, "replayed"]
    assert rows == []
    assert resumed.candidate_log.read_bytes() == b""
    archive = round_dir / "abandoned-candidate-tail-001.bin"
    assert archive.read_bytes() == original_tail
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    recovery = manifest["abandoned_ranges"]
    assert len(recovery) == 1
    assert recovery[0]["last_complete_offset"] == len(jsonl(row))
    assert recovery[0]["partial_bytes"] == len(fragment)
    assert recovery[0]["archive_sha256"] == hashlib.sha256(
        original_tail
    ).hexdigest()
    assert recovery[0]["complete_candidate_batch"]["rows"] == 1
    assert manifest["candidate_end_offset"] == 0
    assert (
        round_dir / "abandoned-checkpoint-attempt-001"
    ).is_dir()


def test_flow_recovers_orphan_candidate_wal_before_tail_inspection(
    tmp_path,
):
    import evolve.openevolve_evaluator as evaluator

    repo = tmp_path / "repo"
    repo.mkdir()
    config = FlowConfig(
        repo_dir=repo,
        run_id="flow-wal-recovery",
        iterations_per_round=1,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    path = flow.candidate_log.resolve()
    path.parent.mkdir(parents=True)
    path.touch()
    payload = jsonl(candidate(51))
    evaluator._install_candidate_log_wal(
        path,
        start_offset=0,
        payload=payload,
    )
    path.write_bytes(payload[:19])
    wal_file, temporary = evaluator._candidate_log_wal_paths(path)

    assert flow._candidate_log_size(start_offset=0) == len(payload)
    assert path.read_bytes() == payload
    assert not wal_file.exists()
    assert not temporary.exists()


@pytest.mark.parametrize(
    "mutation",
    ("delete-empty", "replace-empty", "truncate", "tamper"),
)
def test_candidate_range_witness_rejects_log_replacement_or_change(
    tmp_path,
    mutation,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"candidate-range-{mutation}",
        iterations_per_round=1,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    original = (
        b""
        if mutation in {"delete-empty", "replace-empty"}
        else jsonl(candidate(52))
    )
    flow.candidate_log.write_bytes(original)
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(flow, round_dir, checkpoint, None)

    if mutation == "delete-empty":
        flow.candidate_log.unlink()
    elif mutation == "replace-empty":
        flow_module.atomic_write_bytes(flow.candidate_log, b"")
    elif mutation == "truncate":
        flow.candidate_log.write_bytes(original[:-1])
    else:
        changed = bytearray(original)
        changed[0] = ord("[")
        flow.candidate_log.write_bytes(changed)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="candidate",
    ):
        flow._capture_round_candidates(state, 1, round_dir)


def test_candidate_range_witness_accepts_unchanged_log(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="candidate-range-valid",
        iterations_per_round=1,
        milp_top=0,
    )
    row = candidate(53)
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    flow.candidate_log.write_bytes(jsonl(row))
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(flow, round_dir, checkpoint, None)

    assert flow._capture_round_candidates(state, 1, round_dir) == [row]


@pytest.mark.parametrize(
    "mutation_error_kind",
    ["invalid_mutation", "no_effect_mutation"],
)
def test_current_witness_accepts_an_all_invalid_mutation_slice(
    tmp_path,
    mutation_error_kind,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_coset_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="all-invalid-mutation-slice",
        iterations_per_round=3,
        evolution_config=repo / "evolve/config.yaml",
        evolution_seed=repo / "evolve/seed_solution.py",
        evolution_evaluator="coset-two-block",
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(
        repo,
        config.run_id,
        3,
        coset_policy=True,
    )
    write_full_slice_proof(
        flow,
        round_dir,
        checkpoint,
        None,
        all_invalid_mutations=True,
        mutation_error_kind=mutation_error_kind,
    )
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        checkpoint,
    )

    witness = flow_module._validate_slice_witness(
        flow_module._slice_witness_path(round_dir),
        config,
        None,
        result,
        transaction["launch_binding"],
        transaction["invocation_binding"],
        flow.candidate_log,
        0,
    )

    assert witness["successful_evaluations"] == 0
    assert witness["worker_errors"] == 3
    assert all(
        outcome["error_kind"] == mutation_error_kind
        for outcome in witness["outcomes"]
    )


def test_schema_v7_coset_map_witness_replays_parent_and_lineage(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_coset_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="coset-map-witness-v7",
        iterations_per_round=5,
        evolution_config=repo / "evolve/config.yaml",
        evolution_seed=repo / "evolve/seed_solution.py",
        evolution_evaluator="coset-two-block",
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(
        repo,
        config.run_id,
        5,
        coset_policy=True,
    )
    write_full_slice_proof(flow, round_dir, checkpoint, None)
    witness_path = flow_module._slice_witness_path(round_dir)
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        checkpoint,
    )

    def validate() -> dict:
        return flow_module._validate_slice_witness(
            witness_path,
            config,
            None,
            result,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            flow.candidate_log,
            int(transaction["candidate_start_offset"]),
        )

    accepted = validate()
    assert accepted["search_portfolio"] is None
    assert [
        attempt["island_id"]
        for attempt in accepted["submission_attempts"]
    ] == [0, 1, 2, 3, 0]
    assert all(
        set(attempt)
        == {
            "iteration",
            "island_id",
            "result",
            "coset_parent_program_id",
            "coset_parent_code_sha256",
        }
        for attempt in accepted["submission_attempts"]
    )
    accepted_marker = flow_module._validate_completion_marker(
        flow_module._completion_marker_path(round_dir),
        config,
        None,
        result,
        transaction["launch_binding"],
        transaction["invocation_binding"],
        accepted,
    )
    assert accepted_marker["schema_version"] == 7

    original = json.loads(witness_path.read_text())

    def reject(mutator, match):
        changed = copy.deepcopy(original)
        mutator(changed)
        atomic_write_json(witness_path, changed)
        with pytest.raises(RoundTransactionError, match=match):
            validate()
        atomic_write_json(witness_path, original)

    reject(
        lambda row: row["submission_attempts"][0].__setitem__(
            "island_id", 1
        ),
        "island schedule",
    )
    reject(
        lambda row: row["submission_attempts"][0].__setitem__(
            "coset_parent_code_sha256", "1" * 64
        ),
        "parent code hash changed",
    )
    reject(
        lambda row: row["submission_attempts"][0].__setitem__(
            "coset_parent_program_id", "../program"
        ),
        "parent identity",
    )
    reject(
        lambda row: row["submission_attempts"][0].pop(
            "coset_parent_code_sha256"
        ),
        "fields are not exact",
    )
    reject(
        lambda row: row["submission_attempts"][0].__setitem__(
            "unbound", True
        ),
        "fields are not exact",
    )
    reject(
        lambda row: row.__setitem__(
            "search_portfolio", {"schema_version": 2}
        ),
        "cannot carry a BB portfolio",
    )


def test_schema_v7_coset_resume_replays_parent_from_base_checkpoint(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_coset_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="coset-map-resume-parent-v7",
        iterations_per_round=5,
        evolution_config=repo / "evolve/config.yaml",
        evolution_seed=repo / "evolve/seed_solution.py",
        evolution_evaluator="coset-two-block",
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    base_checkpoint = write_checkpoint(
        repo,
        config.run_id,
        5,
        coset_policy=True,
    )
    base = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        base_checkpoint,
    )
    result_checkpoint = write_checkpoint(
        repo,
        config.run_id,
        10,
        coset_policy=True,
        child_iteration=6,
    )
    (result_checkpoint / "programs/program.json").unlink()
    atomic_write_json(result_checkpoint / "metadata.json", {
        "last_iteration": 10,
        "archive": ["evicted-child"],
        "best_program_id": "evicted-child",
        "islands": [["evicted-child"]],
        "island_best_programs": ["evicted-child"],
        "island_feature_maps": [{"cell": "evicted-child"}],
    })
    write_full_slice_proof(
        flow,
        round_dir,
        result_checkpoint,
        base,
    )
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        result_checkpoint,
    )

    accepted = flow_module._validate_slice_witness(
        flow_module._slice_witness_path(round_dir),
        config,
        base,
        result,
        transaction["launch_binding"],
        transaction["invocation_binding"],
        flow.candidate_log,
        int(transaction["candidate_start_offset"]),
    )

    assert accepted["resume_checkpoint"] == base["path"]
    assert {
        attempt["coset_parent_program_id"]
        for attempt in accepted["submission_attempts"]
    } == {"program"}


def test_schema_v7_dispatches_multisplit_checkpoint_preflight(
    tmp_path,
    monkeypatch,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_coset_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="coset-multisplit-preflight-v7",
        iterations_per_round=1,
        evolution_config=repo / "evolve/config.yaml",
        evolution_seed=repo / "evolve/seed_solution.py",
        evolution_evaluator="coset-two-block",
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    base_checkpoint = write_checkpoint(
        repo,
        config.run_id,
        1,
        coset_policy=True,
    )
    base = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        base_checkpoint,
    )
    result_checkpoint = write_checkpoint(
        repo,
        config.run_id,
        2,
        coset_policy=True,
        child_iteration=2,
    )
    write_full_slice_proof(
        flow,
        round_dir,
        result_checkpoint,
        base,
    )
    witness_path = flow_module._slice_witness_path(round_dir)
    witness = json.loads(witness_path.read_text())
    report = {
        "schema_version": 4,
        "status": "completed",
        "contract_version": 2,
        "contract_id": 17,
    }
    witness["checkpoint_preflight"] = report
    atomic_write_json(witness_path, witness)
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        result_checkpoint,
    )
    calls = []

    def record_dispatch(observed_report, **kwargs):
        calls.append((observed_report, kwargs))

    monkeypatch.setattr(
        flow_module,
        "_validate_checkpoint_activation_bridge_preflight",
        record_dispatch,
    )

    accepted = flow_module._validate_slice_witness(
        witness_path,
        config,
        base,
        result,
        transaction["launch_binding"],
        transaction["invocation_binding"],
        flow.candidate_log,
        int(transaction["candidate_start_offset"]),
    )

    assert accepted["checkpoint_preflight"] == report
    assert len(calls) == 1
    assert calls[0][0] == report
    assert calls[0][1]["base_checkpoint"] == base
    assert calls[0][1]["result_checkpoint"] == result


def test_schema_v7_non_coset_config_rejects_coset_parent_fields(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="non-coset-parent-fields",
        iterations_per_round=1,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(flow, round_dir, checkpoint, None)
    witness_path = flow_module._slice_witness_path(round_dir)
    witness = json.loads(witness_path.read_text())
    witness["submission_attempts"][0].update({
        "coset_parent_program_id": "program",
        "coset_parent_code_sha256": "0" * 64,
    })
    atomic_write_json(witness_path, witness)
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        checkpoint,
    )

    with pytest.raises(
        RoundTransactionError,
        match="non-portfolio submission witness fields are not exact",
    ):
        flow_module._validate_slice_witness(
            witness_path,
            config,
            None,
            result,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            flow.candidate_log,
            int(transaction["candidate_start_offset"]),
        )


def test_schema_v7_coset_map_rejects_untrusted_mutation_error_kind(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_coset_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="coset-untrusted-mutation-error",
        iterations_per_round=2,
        evolution_config=repo / "evolve/config.yaml",
        evolution_seed=repo / "evolve/seed_solution.py",
        evolution_evaluator="coset-two-block",
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(
        repo,
        config.run_id,
        2,
        coset_policy=True,
    )
    write_full_slice_proof(
        flow,
        round_dir,
        checkpoint,
        None,
        all_invalid_mutations=True,
        mutation_error_kind="mutation_binding_invalid",
    )
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        checkpoint,
    )

    with pytest.raises(
        RoundTransactionError,
        match="worker error identity is invalid",
    ):
        flow_module._validate_slice_witness(
            flow_module._slice_witness_path(round_dir),
            config,
            None,
            result,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            flow.candidate_log,
            int(transaction["candidate_start_offset"]),
        )


def test_completed_transaction_accepts_same_bytes_after_inode_rotation(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="committed-candidate-inode-rotation",
        iterations_per_round=1,
        milp_top=0,
    )
    row = candidate(60)
    payload = jsonl(row)

    def runner(_config, _state, runner_round):
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(payload)
        checkpoint = write_checkpoint(repo, config.run_id, 1)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    assert flow._capture_round_candidates(state, 1, round_dir) == [row]

    witness = json.loads(
        flow_module._slice_witness_path(round_dir).read_text()
    )
    with flow.candidate_log.open("rb") as original_log:
        original_inode = flow.candidate_log.stat().st_ino
        assert original_log.read() == payload
        flow_module.atomic_write_bytes(flow.candidate_log, payload)
        replacement = flow.candidate_log.stat()
        assert replacement.st_ino != original_inode
        assert replacement.st_dev == witness["candidate_log_device"]

    assert witness["candidate_log_inode"] == original_inode
    transaction, rows = flow._validate_completed_transaction(1, round_dir)
    assert transaction["status"] == "committed"
    assert rows == [row]
    # A committed round can still be the durable pending round while Stage 1
    # resumes at phase=screen. That production path must use the same
    # historical inode semantics and must not launch evolution again.
    assert flow._capture_round_candidates(
        flow.store.load_state(), 1, round_dir
    ) == [row]


def test_committed_v2_batch_replays_legacy_selector_after_upgrade(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="committed-legacy-candidate-batch-policy",
        iterations_per_round=1,
        milp_top=0,
    )
    partial = sealed_lower_bound_candidate(5, complete=False)
    survivor = sealed_lower_bound_candidate(6, complete=True)
    source_rows = [partial, survivor]

    def runner(_config, _state, runner_round):
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(jsonl(*source_rows))
        checkpoint = write_checkpoint(repo, config.run_id, 1)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    [current] = flow._capture_round_candidates(state, 1, round_dir)
    assert current["distance_lower_bound"] == 6

    manifest_path = round_dir / "evolution-transaction.json"
    transaction = json.loads(manifest_path.read_text())
    assert transaction["schema_version"] == 3
    assert transaction["protocol_version"] == 3
    assert transaction["candidate_batch_policy_version"] == 7
    bound_end = transaction["candidate_end_offset"]

    # Model the immutable protocol-v2 artifact produced before selector
    # versioning, then append a later-round row beyond its frozen source slice.
    legacy_rows = flow_module._deduplicate(
        source_rows,
        policy_version=flow_module.CANDIDATE_BATCH_POLICY_LEGACY_VERSION,
    )
    transaction["schema_version"] = 2
    transaction["protocol_version"] = 2
    transaction.pop("candidate_batch_policy_version")
    transaction["candidate_batch_identity"] = (
        flow_module.atomic_write_jsonl(
            round_dir / "candidate-batch.jsonl",
            legacy_rows,
        )
    )
    atomic_write_json(manifest_path, transaction)
    with flow.candidate_log.open("ab") as stream:
        stream.write(jsonl(candidate(70)))
    resumed_state = flow.store.load_state()
    resumed_state["round_transaction_version"] = 2
    flow.store.write_state(resumed_state)

    [resumed] = flow._capture_round_candidates(
        flow.store.load_state(), 1, round_dir
    )
    assert resumed["distance_lower_bound"] == 5
    assert json.loads(manifest_path.read_text())[
        "candidate_end_offset"
    ] == bound_end
    _transaction, completed_rows = flow._validate_completed_transaction(
        1, round_dir
    )
    assert completed_rows == legacy_rows


def test_candidate_batch_policy_is_required_by_protocol_v3(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="candidate-batch-policy-binding",
        iterations_per_round=1,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    assert flow._candidate_batch_policy_version(transaction) == 7

    historical_v6 = dict(transaction)
    historical_v6["candidate_batch_policy_version"] = 6
    assert flow._candidate_batch_policy_version(historical_v6) == 6

    historical_v5 = dict(transaction)
    historical_v5["candidate_batch_policy_version"] = 5
    assert flow._candidate_batch_policy_version(historical_v5) == 5

    historical_v4 = dict(transaction)
    historical_v4["candidate_batch_policy_version"] = 4
    assert flow._candidate_batch_policy_version(historical_v4) == 4

    historical_v3 = dict(transaction)
    historical_v3["candidate_batch_policy_version"] = 3
    assert flow._candidate_batch_policy_version(historical_v3) == 3

    historical_v2 = dict(transaction)
    historical_v2["candidate_batch_policy_version"] = 2
    assert flow._candidate_batch_policy_version(historical_v2) == 2

    missing = dict(transaction)
    missing.pop("candidate_batch_policy_version")
    with pytest.raises(
        RoundTransactionError,
        match="unsupported candidate batch policy",
    ):
        flow._candidate_batch_policy_version(missing)

    invalid = dict(transaction)
    invalid["candidate_batch_policy_version"] = True
    with pytest.raises(
        RoundTransactionError,
        match="unsupported candidate batch policy",
    ):
        flow._candidate_batch_policy_version(invalid)


@pytest.mark.parametrize("bound_policy", [2, 3, 4, 5, 6, 7])
def test_pending_screen_uses_committed_candidate_batch_policy(
    tmp_path,
    monkeypatch,
    bound_policy,
):
    """A pending round must use its committed selector policy exactly."""

    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    candidate_file = repo / "candidates.jsonl"
    source_row = candidate(0)
    candidate_file.write_bytes(jsonl(source_row))
    config = FlowConfig(
        repo_dir=repo,
        run_id="pending-screen-candidate-batch-policy",
        candidate_file=candidate_file,
        max_rounds=1,
        milp_top=1,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    batch_rows = flow._capture_round_candidates(state, 1, round_dir)

    manifest_path = round_dir / "evolution-transaction.json"
    transaction = json.loads(manifest_path.read_text())
    transaction["candidate_batch_policy_version"] = bound_policy
    transaction["candidate_batch_identity"] = (
        flow_module.atomic_write_jsonl(
            round_dir / "candidate-batch.jsonl",
            flow_module._deduplicate(
                [source_row],
                policy_version=bound_policy,
            ),
        )
    )
    atomic_write_json(manifest_path, transaction)
    assert batch_rows == [source_row]
    assert flow.store.load_state()["round_phase"] == "screen"

    observed_screen_policy_versions = []
    observed_select_policy_versions = []

    def screen_with_bound_policy(rows, *, policy_version):
        observed_screen_policy_versions.append(policy_version)
        return list(rows), [], list(rows), None

    def select_with_bound_policy(
        _candidates,
        _state,
        *,
        screened_history=None,
        policy_version,
        verified_structural_digests=None,
    ):
        assert screened_history == [source_row]
        assert verified_structural_digests is None
        observed_select_policy_versions.append(policy_version)
        return []

    monkeypatch.setattr(
        flow,
        "_screen_candidates_with_pool_indexed",
        screen_with_bound_policy,
    )
    monkeypatch.setattr(
        flow,
        "_select_audit_candidates",
        select_with_bound_policy,
    )
    completed = flow.run()

    assert observed_screen_policy_versions == [
        bound_policy
    ]
    assert observed_select_policy_versions == [
        bound_policy
    ]
    assert completed["current_round"] == 1
    assert completed.get("pending_round") is None


def test_live_transaction_rejects_same_bytes_after_inode_rotation(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="live-candidate-inode-rotation",
        iterations_per_round=1,
        milp_top=0,
    )
    row = candidate(61)
    payload = jsonl(row)
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    flow.candidate_log.write_bytes(payload)
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(flow, round_dir, checkpoint, None)

    with flow.candidate_log.open("rb"):
        original_inode = flow.candidate_log.stat().st_ino
        flow_module.atomic_write_bytes(flow.candidate_log, payload)
        assert flow.candidate_log.stat().st_ino != original_inode

    with pytest.raises(
        RoundTransactionError,
        match="candidate_log_inode",
    ):
        flow._capture_round_candidates(state, 1, round_dir)


def test_completed_transaction_rejects_tampered_rotated_candidate_range(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="committed-candidate-content-tamper",
        iterations_per_round=1,
        milp_top=0,
    )
    row = candidate(62)
    payload = jsonl(row)

    def runner(_config, _state, runner_round):
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(payload)
        checkpoint = write_checkpoint(repo, config.run_id, 1)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    assert flow._capture_round_candidates(state, 1, round_dir) == [row]

    tampered = payload.replace(b'"k": 8', b'"k": 9', 1)
    assert tampered != payload
    assert len(tampered) == len(payload)
    with flow.candidate_log.open("rb"):
        original_inode = flow.candidate_log.stat().st_ino
        flow_module.atomic_write_bytes(flow.candidate_log, tampered)
        assert flow.candidate_log.stat().st_ino != original_inode

    with pytest.raises(
        RoundTransactionError,
        match="candidate_range_sha256",
    ):
        flow._validate_completed_transaction(1, round_dir)


@pytest.mark.parametrize(
    "witness_schema",
    [
        flow_module.EVOLUTION_SLICE_WITNESS_PRE_EVALUATOR_BINDING_SCHEMA_VERSION,
        6,
        flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
    ],
    ids=["schema-v5-legacy-source-binding", "schema-v6", "schema-v7"],
)
def test_portfolio_witness_replays_policy_roles_tactics_and_quota(
    tmp_path,
    witness_schema,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo, portfolio=True)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"portfolio-witness-v{witness_schema}",
        iterations_per_round=7,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    flow.candidate_log.write_bytes(jsonl(candidate(55)))
    checkpoint = write_checkpoint(repo, config.run_id, 7)
    write_full_slice_proof(
        flow,
        round_dir,
        checkpoint,
        None,
        schema_version=witness_schema,
    )
    witness_path = flow_module._slice_witness_path(round_dir)
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output, checkpoint
    )

    def validate() -> dict:
        return flow_module._validate_slice_witness(
            witness_path,
            config,
            None,
            result,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            flow.candidate_log,
            int(transaction["candidate_start_offset"]),
        )

    accepted = validate()
    assert accepted["schema_version"] == witness_schema
    assert (
        "openevolve_evaluator_path" in accepted
    ) == (witness_schema in {6, flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION})
    accepted_marker = flow_module._validate_completion_marker(
        flow_module._completion_marker_path(round_dir),
        config,
        None,
        result,
        transaction["launch_binding"],
        transaction["invocation_binding"],
        accepted,
    )
    assert accepted_marker["schema_version"] == witness_schema
    assert accepted["search_portfolio"]["role_submission_counts"] == {
        "affine_automorphism_cover": 2,
        "shared_anchor_coset_cover": 2,
        "complementary_diagonal_cover": 1,
        "asymmetric_anchor_cover": 1,
        "failure_repair_restart": 1,
    }
    original = json.loads(witness_path.read_text())

    evaluator_source = repo / "fake-openevolve/evaluator.py"
    if witness_schema in {6, flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION}:
        evaluator_source.write_text("# tampered evaluator\n")
        with pytest.raises(RoundTransactionError, match="evaluator_sha256"):
            validate()
        evaluator_source.write_text("# fake evaluator\n")
    else:
        changed = copy.deepcopy(original)
        descriptor = flow_module._file_descriptor(
            evaluator_source, "fake OpenEvolve evaluator source"
        )
        for field in ("path", "sha256", "bytes"):
            changed[f"openevolve_evaluator_{field}"] = descriptor[field]
        atomic_write_json(witness_path, changed)
        with pytest.raises(RoundTransactionError, match="fields are not exact"):
            validate()
    atomic_write_json(witness_path, original)

    mutations = []

    def mutate_policy(row):
        row["search_portfolio"]["policy_sha256"] = "0" * 64

    mutations.append(mutate_policy)

    def mutate_island(row):
        row["submission_attempts"][0]["island_id"] = 4

    mutations.append(mutate_island)

    def mutate_role(row):
        row["submission_attempts"][0]["search_role"] = (
            "failure_repair_restart"
        )

    mutations.append(mutate_role)

    def mutate_tactic(row):
        row["submission_attempts"][0]["search_tactic"] = (
            "repair_x_low_weight"
        )

    mutations.append(mutate_tactic)

    def mutate_parent_hash(row):
        row["submission_attempts"][0][
            "search_parent_code_sha256"
        ] = "1" * 64

    mutations.append(mutate_parent_hash)

    def mutate_bool_quota(row):
        row["search_portfolio"]["role_submission_counts"][
            "balanced_3_3"
        ] = True

    mutations.append(mutate_bool_quota)

    def mutate_extra_field(row):
        row["submission_attempts"][0]["unbound"] = "forbidden"

    mutations.append(mutate_extra_field)

    for mutate in mutations:
        changed = copy.deepcopy(original)
        mutate(changed)
        atomic_write_json(witness_path, changed)
        with pytest.raises(RoundTransactionError):
            validate()


def test_portfolio_witness_v6_accepts_geometry_schema_v3(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo, geometry_portfolio=True)
    config = FlowConfig(
        repo_dir=repo,
        run_id="geometry-portfolio-witness-v6",
        max_rounds=12,
        iterations_per_round=5,
        milp_top=0,
        search_representation_id="css-bb-twisted-torus-generator-v1",
        search_regime_policy_version=3,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    flow.candidate_log.write_bytes(jsonl(candidate(58)))
    checkpoint = write_checkpoint(repo, config.run_id, 5)
    write_full_slice_proof(flow, round_dir, checkpoint, None)
    witness_path = flow_module._slice_witness_path(round_dir)
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output, checkpoint,
    )

    accepted = flow_module._validate_slice_witness(
        witness_path,
        config,
        None,
        result,
        transaction["launch_binding"],
        transaction["invocation_binding"],
        flow.candidate_log,
        int(transaction["candidate_start_offset"]),
    )
    assert accepted["search_portfolio"]["schema_version"] == 3
    assert accepted["search_geometry_contract"] == "twisted-torus-v1"
    assert accepted["search_portfolio"]["feature_dimensions"] == [
        "algebraic_relation_type",
        "support_split_type",
        "geometry_twist_class",
    ]
    assert {
        attempt["search_portfolio_schema_version"]
        for attempt in accepted["submission_attempts"]
    } == {3}


def test_schema_v4_portfolio_uses_only_frozen_legacy_semantics(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo, legacy_portfolio=True)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-portfolio-witness-v4",
        iterations_per_round=7,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    flow.candidate_log.write_bytes(jsonl(candidate(56)))
    checkpoint = write_checkpoint(repo, config.run_id, 7)
    write_full_slice_proof(
        flow,
        round_dir,
        checkpoint,
        None,
        schema_version=(
            flow_module.EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION
        ),
    )
    witness_path = flow_module._slice_witness_path(round_dir)
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output, checkpoint
    )

    def validate() -> dict:
        return flow_module._validate_slice_witness(
            witness_path,
            config,
            None,
            result,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            flow.candidate_log,
            int(transaction["candidate_start_offset"]),
        )

    accepted = validate()
    portfolio = accepted["search_portfolio"]
    assert accepted["schema_version"] == 4
    assert portfolio["schema_version"] == 1
    assert portfolio["roles"] == list(
        flow_module.LEGACY_V4_SEARCH_PORTFOLIO_ROLES
    )
    assert "feature_dimensions" not in portfolio
    assert all(
        "search_regime_status" not in attempt
        for attempt in accepted["submission_attempts"]
    )

    # A v5-only field cannot be smuggled into a v4 artifact and interpreted
    # under the mechanism-portfolio contract.
    changed = json.loads(witness_path.read_text())
    changed["search_portfolio"]["feature_dimensions"] = list(
        flow_module.SEARCH_PORTFOLIO_FEATURE_DIMENSIONS
    )
    atomic_write_json(witness_path, changed)
    with pytest.raises(RoundTransactionError, match="legacy schema-v4"):
        validate()


def test_legacy_source_ready_candidate_binding_remains_resumable(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-source-ready",
        iterations_per_round=1,
        milp_top=0,
    )
    row = candidate(54)
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    encoded = jsonl(row)
    flow.candidate_log.write_bytes(encoded)
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(
        flow,
        round_dir,
        checkpoint,
        None,
        schema_version=2,
    )
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        checkpoint,
    )
    transaction.update({
        "status": "source-ready",
        "result_checkpoint": result,
        "completion_witness_sha256": flow_module._file_sha256(
            flow_module._slice_witness_path(round_dir)
        ),
        "completion_marker_sha256": flow_module._file_sha256(
            flow_module._completion_marker_path(round_dir)
        ),
        "candidate_end_offset": len(encoded),
        "candidate_source_sha256": hashlib.sha256(encoded).hexdigest(),
        "candidate_source_rows": 1,
        "source_ready_at": "legacy",
    })
    atomic_write_json(
        round_dir / "evolution-transaction.json",
        transaction,
    )

    resumed = HumanizeFlow(
        config,
        reviewer=Reviewer(),
        evolution_runner=lambda *_args: (_ for _ in ()).throw(
            AssertionError("source-ready legacy slice must not rerun")
        ),
    )
    assert resumed._capture_round_candidates(
        resumed.store.load_state(),
        1,
        round_dir,
    ) == [row]


def test_swallowed_interrupt_without_checkpoint_cannot_commit_round(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="swallowed-interrupt",
        iterations_per_round=25,
    )
    calls = []

    def swallows_interrupt(*_args):
        calls.append(True)
        try:
            raise KeyboardInterrupt
        except KeyboardInterrupt:
            return None

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=swallows_interrupt
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)

    with pytest.raises(RoundTransactionError, match="checkpoint is missing"):
        flow._capture_round_candidates(state, 1, round_dir)

    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert calls == [True]
    assert manifest["status"] == "prepared"
    persisted = flow.store.load_state()
    assert persisted.get("pending_round") is None
    assert persisted["current_round"] == 0


def test_markerless_expected_checkpoint_is_quarantined_and_rerun(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="incomplete-checkpoint",
        iterations_per_round=25,
    )
    calls = []

    def runner(_config, _state, runner_round):
        calls.append(True)
        expected = flow.evolution_output / "checkpoints" / "checkpoint_25"
        assert not expected.exists()
        quarantined = runner_round / "abandoned-checkpoint-attempt-001"
        assert (quarantined / "metadata.json").is_file()
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    incomplete = flow.evolution_output / "checkpoints" / "checkpoint_25"
    incomplete.mkdir(parents=True)
    atomic_write_json(incomplete / "metadata.json", {"last_iteration": 25})

    rows = flow._capture_round_candidates(state, 1, round_dir)
    assert rows == []
    assert calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert len(manifest["abandoned_checkpoints"]) == 1
    assert manifest["result_checkpoint"]["last_iteration"] == 25


@pytest.mark.parametrize(
    "crash_after",
    (1, 2, 3),
    ids=("checkpoint", "completion-marker", "slice-witness"),
)
def test_checkpoint_quarantine_write_ahead_replays_each_rename_boundary(
    tmp_path, monkeypatch, crash_after
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"quarantine-crash-{crash_after}",
        iterations_per_round=25,
        milp_top=0,
    )
    initial = HumanizeFlow(config, reviewer=Reviewer())
    state = initial.store.initialize(config.serializable())
    round_dir = initial.store.round_dir(1)
    transaction = initial._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(repo, config.run_id, 25)
    marker = flow_module._completion_marker_path(round_dir)
    witness = flow_module._slice_witness_path(round_dir)
    marker.write_text('{"incomplete": true}\n')
    witness.write_text('{"incomplete": true}\n')

    _sources, destinations = initial._checkpoint_quarantine_paths(
        round_dir, checkpoint, 1
    )
    quarantine_targets = {
        path.absolute() for path in destinations.values()
    }
    original_replace = Path.replace
    renamed = []

    class SimulatedProcessDeath(BaseException):
        pass

    def die_after_selected_rename(source, target):
        result = original_replace(source, target)
        if Path(target).absolute() in quarantine_targets:
            renamed.append(Path(target).name)
            if len(renamed) == crash_after:
                raise SimulatedProcessDeath
        return result

    monkeypatch.setattr(Path, "replace", die_after_selected_rename)
    with pytest.raises(SimulatedProcessDeath):
        initial._quarantine_untrusted_evolution_attempt(
            transaction,
            round_dir,
            checkpoint,
            reason="fault-injected incomplete attempt",
        )

    durable_plan = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["abandoned_checkpoints"]
    assert len(durable_plan) == 1
    plan = durable_plan[0]
    assert plan["attempt"] == 1
    assert plan["status"] == "quarantining"
    assert plan["reason"] == "fault-injected incomplete attempt"
    assert plan["expected_checkpoint"] == str(checkpoint.absolute())
    assert plan["artifact_names"] == [
        "checkpoint", "completion_marker", "slice_witness"
    ]
    assert isinstance(plan["planned_at"], str)
    assert set(plan["artifact_identities"]) == set(plan["artifact_names"])
    for name, identity in plan["artifact_identities"].items():
        assert identity["path"] == str(destinations[name].resolve())
        assert isinstance(identity["sha256"], str)
        assert identity["bytes"] > 0
    assert len(renamed) == crash_after

    monkeypatch.setattr(Path, "replace", original_replace)
    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert not checkpoint.exists()
        assert not marker.exists()
        assert not witness.exists()
        assert all(path.exists() for path in destinations.values())
        result = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(resumed, runner_round, result, None)
        return result

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    rows = resumed._capture_round_candidates(
        resumed.store.load_state(), 1, round_dir
    )

    assert rows == []
    assert runner_calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    quarantined = manifest["abandoned_checkpoints"]
    assert len(quarantined) == 1
    assert quarantined[0]["attempt"] == 1
    assert quarantined[0]["reason"] == "fault-injected incomplete attempt"
    assert set(quarantined[0]["artifacts"]) == {
        "checkpoint", "completion_marker", "slice_witness"
    }
    assert manifest["result_checkpoint"]["last_iteration"] == 25
    assert not any(round_dir.glob("abandoned-*-attempt-002*"))


@pytest.mark.parametrize(
    "tampered_artifact",
    ("checkpoint", "completion_marker", "slice_witness"),
    ids=("checkpoint-destination", "marker-source", "witness-source"),
)
def test_checkpoint_quarantine_rejects_tampered_replay_identity(
    tmp_path, monkeypatch, tampered_artifact
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"quarantine-tamper-{tampered_artifact}",
        iterations_per_round=25,
        milp_top=0,
    )
    initial = HumanizeFlow(config, reviewer=Reviewer())
    state = initial.store.initialize(config.serializable())
    round_dir = initial.store.round_dir(1)
    transaction = initial._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(repo, config.run_id, 25)
    marker = flow_module._completion_marker_path(round_dir)
    witness = flow_module._slice_witness_path(round_dir)
    marker.write_text('{"incomplete": true}\n')
    witness.write_text('{"incomplete": true}\n')
    _sources, destinations = initial._checkpoint_quarantine_paths(
        round_dir, checkpoint, 1
    )

    original_replace = Path.replace

    class SimulatedProcessDeath(BaseException):
        pass

    def die_after_checkpoint_rename(source, target):
        result = original_replace(source, target)
        if Path(target).absolute() == destinations["checkpoint"].absolute():
            raise SimulatedProcessDeath
        return result

    monkeypatch.setattr(Path, "replace", die_after_checkpoint_rename)
    with pytest.raises(SimulatedProcessDeath):
        initial._quarantine_untrusted_evolution_attempt(
            transaction,
            round_dir,
            checkpoint,
            reason="fault-injected incomplete attempt",
        )
    monkeypatch.setattr(Path, "replace", original_replace)

    if tampered_artifact == "checkpoint":
        metadata = destinations["checkpoint"] / "metadata.json"
        metadata.write_text(metadata.read_text() + "tampered\n")
    elif tampered_artifact == "completion_marker":
        marker.write_text('{"tampered": true}\n')
    else:
        witness.write_text('{"tampered": true}\n')

    runner_calls = []

    def must_not_run(*_args):
        runner_calls.append(True)
        raise AssertionError("tampered quarantine replay launched evolution")

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=must_not_run
    )
    with pytest.raises(RoundTransactionError, match="identity changed"):
        resumed._capture_round_candidates(
            resumed.store.load_state(), 1, round_dir
        )
    assert runner_calls == []
    durable = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert durable["abandoned_checkpoints"][0]["status"] == "quarantining"
    assert durable["abandoned_checkpoints"][0]["attempt"] == 1


def candidate_file_flow(tmp_path, run_id: str):
    repo = tmp_path / run_id
    repo.mkdir()
    source = repo / "candidates.jsonl"
    source.write_bytes(jsonl(candidate(4)))
    config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        max_rounds=1,
        candidate_file=source,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    return flow, state, flow.store.round_dir(1)


def test_round_finalize_event_failure_keeps_resumable_atomic_state(
    tmp_path, monkeypatch
):
    flow, _state, _round_dir = candidate_file_flow(
        tmp_path, "finalize-event-failure"
    )
    original_event = flow.store.event

    def fail_completed_event(event_name, **fields):
        if event_name == "round_completed":
            raise RuntimeError("injected round completion event failure")
        return original_event(event_name, **fields)

    monkeypatch.setattr(flow.store, "event", fail_completed_event)
    with pytest.raises(RuntimeError, match="injected round completion"):
        flow.run()

    failed = flow.store.load_state()
    assert failed["current_round"] == 0
    assert failed["pending_round"] == 1
    assert failed["round_phase"] == "finalize"
    assert failed["rounds"] == []

    resumed = HumanizeFlow(flow.config, reviewer=Reviewer())
    completed = resumed.run()
    assert completed["current_round"] == 1
    assert "pending_round" not in completed
    assert "round_phase" not in completed
    assert len(completed["rounds"]) == 1


@pytest.mark.parametrize("failure_type", [RuntimeError, KeyboardInterrupt])
def test_postcommit_run_meta_failure_never_rewrites_round_as_failed(
    tmp_path,
    monkeypatch,
    failure_type,
):
    flow, _state, _round_dir = candidate_file_flow(
        tmp_path, "postcommit-run-meta-failure"
    )
    original_write_run_meta = flow._write_run_meta

    def fail_after_round_commit(state):
        if (
            state.get("current_round") == 1
            and state.get("pending_round") is None
            and state.get("round_phase") is None
            and state.get("rounds")
        ):
            raise failure_type("injected postcommit run-meta failure")
        return original_write_run_meta(state)

    monkeypatch.setattr(flow, "_write_run_meta", fail_after_round_commit)
    with pytest.raises(failure_type, match="postcommit run-meta"):
        flow.run()

    committed = flow.store.load_state()
    assert committed is not None
    assert committed["current_round"] == 1
    assert len(committed["rounds"]) == 1
    assert "pending_round" not in committed
    assert "round_phase" not in committed
    assert committed["status"] != "failed"
    assert "failure" not in committed

    resumed = HumanizeFlow(flow.config, reviewer=Reviewer())
    completed = resumed.run()
    assert completed["status"] == "search-complete"
    assert completed["current_round"] == 1
    assert len(completed["rounds"]) == 1


def test_postcommit_handoff_event_failure_preserves_atomic_terminal_state(
    tmp_path,
    monkeypatch,
):
    repo = tmp_path / "postcommit-handoff-event"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    source.write_bytes(jsonl(candidate(4)))
    config = FlowConfig(
        repo_dir=repo,
        run_id="postcommit-handoff-event",
        max_rounds=1,
        candidate_file=source,
        milp_top=0,
        search_representation_id="css-bb-test-v2",
        search_regime_policy_version=2,
        stop_on_representation_change=True,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())

    regime = {
        "schema_version": 1,
        "kind": "qcode-humanize-search-regime",
        "status": "representation_change_required",
        "reason": "injected-sealed-regime-for-postcommit-fault-test",
        "evidence": {
            "basis": "durable-sealed-exact-and-diversity",
            "rounds": [1],
            "exact_distances_by_round": [[2]],
        },
    }

    def finish_with_handoff(
        state,
        number,
        _candidates,
        _audited,
        _review,
        _round_dir,
    ):
        state["rounds"].append({
            "round": number,
            "search_regime_policy_version": 2,
            "search_regime": copy.deepcopy(regime),
        })
        state["current_round"] = number
        state["search_regime"] = copy.deepcopy(regime)

    monkeypatch.setattr(flow, "_finish_round", finish_with_handoff)
    original_event = flow.store.event

    def fail_handoff_event(event_name, **fields):
        if event_name == "search_representation_change_handoff":
            raise RuntimeError("injected postcommit handoff event failure")
        return original_event(event_name, **fields)

    monkeypatch.setattr(flow.store, "event", fail_handoff_event)
    with pytest.raises(RuntimeError, match="postcommit handoff event"):
        flow.run()

    committed = flow.store.load_state()
    assert committed is not None
    assert committed["status"] == "search-complete"
    assert committed["current_round"] == 1
    assert committed["search_handoff_reason"] == (
        "representation_change_required"
    )
    assert committed["search_handoff_at_round"] == 1
    assert "pending_round" not in committed
    assert "round_phase" not in committed
    assert "failure" not in committed


def test_recovers_batch_rename_before_batch_ready_manifest(tmp_path, monkeypatch):
    flow, state, round_dir = candidate_file_flow(tmp_path, "batch-rename")
    original = flow_module.atomic_write_json

    def crash(path, value):
        if (
            path.name == "evolution-transaction.json"
            and value.get("status") == "batch-ready"
        ):
            raise RuntimeError("crash after batch rename")
        return original(path, value)

    monkeypatch.setattr(flow_module, "atomic_write_json", crash)
    with pytest.raises(RuntimeError, match="batch rename"):
        flow._capture_round_candidates(state, 1, round_dir)
    assert (round_dir / "candidate-batch.jsonl").is_file()
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == "source-ready"

    monkeypatch.setattr(flow_module, "atomic_write_json", original)
    resumed = HumanizeFlow(flow.config, reviewer=Reviewer())
    rows = resumed._capture_round_candidates(
        resumed.store.load_state(), 1, round_dir
    )
    assert rows == [candidate(4)]
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == "committed"


def test_recovers_state_commit_before_committed_manifest_and_rejects_redirect(
    tmp_path, monkeypatch
):
    flow, state, round_dir = candidate_file_flow(tmp_path, "state-commit")
    original = flow_module.atomic_write_json

    def crash(path, value):
        if (
            path.name == "evolution-transaction.json"
            and value.get("status") == "committed"
        ):
            raise RuntimeError("crash after state commit")
        return original(path, value)

    monkeypatch.setattr(flow_module, "atomic_write_json", crash)
    with pytest.raises(RuntimeError, match="state commit"):
        flow._capture_round_candidates(state, 1, round_dir)
    persisted = flow.store.load_state()
    assert persisted["pending_round"] == 1
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == "batch-ready"

    monkeypatch.setattr(flow_module, "atomic_write_json", original)
    resumed = HumanizeFlow(flow.config, reviewer=Reviewer())
    recovered = resumed.store.load_state()
    resumed._capture_round_candidates(recovered, 1, round_dir)
    recovered["current_round"] = 1
    recovered.pop("pending_round", None)
    recovered.pop("round_phase", None)
    resumed.store.write_state(recovered)
    assert len(resumed.pipeline_candidate_inputs) == 1

    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    redirected = round_dir / "redirected.jsonl"
    redirected.write_bytes((round_dir / "candidate-batch.jsonl").read_bytes())
    manifest["candidate_batch"] = str(redirected.resolve())
    atomic_write_json(manifest_path, manifest)
    with pytest.raises(RoundTransactionError, match="candidate_batch"):
        _ = resumed.pipeline_candidate_inputs


def test_legacy_pending_checkpoint_25_migrates_without_evolution(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-pending",
        max_rounds=1,
        iterations_per_round=25,
        milp_top=0,
    )
    calls = []

    def runner(*_args):
        calls.append(True)
        raise AssertionError("legacy pending round reran evolution")

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    row = candidate(5)
    flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    flow.candidate_log.write_bytes(jsonl(row))
    checkpoint = write_checkpoint(repo, config.run_id, 25)
    round_dir = flow.store.round_dir(1)
    (round_dir / "candidates.jsonl").write_bytes(jsonl(row))
    (round_dir / "selected.jsonl").write_bytes(b"")
    (round_dir / "milp.jsonl").write_bytes(b"")
    state.update({
        "pending_round": 1,
        "round_phase": "audit",
        "candidate_offset": flow.candidate_log.stat().st_size,
        "last_checkpoint": str(checkpoint.resolve()),
    })
    state.pop("round_transaction_version")
    flow.store.write_state(state)

    completed = flow.run()
    assert calls == []
    assert completed["status"] == "search-complete"
    assert completed["round_transaction_version"] == 3
    assert not (round_dir / "evolution-transaction.json").exists()


def test_prepare_freezes_context_and_api_environment_for_recovery(
    tmp_path, monkeypatch
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    monkeypatch.setenv("OPENAI_API_BASE", "https://frozen.invalid/v1")
    config = FlowConfig(
        repo_dir=repo,
        run_id="frozen-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    flow.store.memory_path.write_text("original bitlesson\n")
    round_dir = flow.store.round_dir(1)

    transaction = flow._prepare_transaction(state, 1, round_dir)

    assert (round_dir / "search-context.md").read_text() == (
        "original bitlesson\n\n"
    )
    assert transaction["launch_binding"]["context"][
        "sha256"
    ] == hashlib.sha256(b"original bitlesson\n\n").hexdigest()
    assert transaction["invocation_binding"]["api_base"] == (
        "https://frozen.invalid/v1"
    )

    flow.store.memory_path.write_text("later bitlesson must not leak\n")
    monkeypatch.setenv("OPENAI_API_BASE", "https://changed.invalid/v1")
    recovered = flow._load_transaction(state, 1, round_dir)

    assert recovered is not None
    assert recovered["invocation_binding"]["api_base"] == (
        "https://frozen.invalid/v1"
    )
    assert (round_dir / "search-context.md").read_text() == (
        "original bitlesson\n\n"
    )


def test_completed_round_records_transaction_bound_candidate_diversity(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    mixed = candidate(60)
    mixed.update({
        "A_terms": [[0, 0], [1, 1]],
        "B_terms": [[0, 1], [1, 0]],
        # These self-reported labels deliberately contradict the terms.
        "pattern_type": "reported-nonmixed",
    })
    duplicate = dict(mixed)
    duplicate.update({
        "d": 5,
        "fom": 999.0,
        "pattern_type": "another-untrusted-label",
    })
    nonmixed = candidate(61)
    nonmixed.update({
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 0], [0, 1], [2, 0]],
        "pattern_type": "reported-mixed",
    })
    source.write_bytes(jsonl(mixed, duplicate, nonmixed))
    config = FlowConfig(
        repo_dir=repo,
        run_id="candidate-diversity-summary",
        max_rounds=1,
        candidate_file=source,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)

    batch = flow._capture_round_candidates(state, 1, round_dir)
    review = Reviewer().review("", round_dir)
    atomic_write_json(round_dir / "review.json", review)
    flow._finish_round(state, 1, batch, [], review, round_dir)
    flow.store.write_state(state)

    persisted = flow.store.load_state()
    assert persisted is not None
    diversity = persisted["rounds"][0]["candidate_diversity"]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert diversity == {
        "schema_version": 1,
        "basis": "transaction-bound-source-and-canonical-batch",
        "raw_candidate_source_rows": 3,
        "canonical_unique_batch_rows": 2,
        "duplicate_count": 1,
        "duplicate_rate": pytest.approx(1 / 3),
        "candidate_source_sha256": manifest["candidate_source_sha256"],
        "candidate_batch_sha256": manifest[
            "candidate_batch_identity"
        ]["sha256"],
        "support_split_counts": {"2+2": 1, "2+3": 1},
        "mixed_vs_nonmixed_counts": {
            "mixed": 1,
            "nonmixed": 1,
            "unclassified": 0,
        },
    }


def _prompt_round_evidence(prompt: str) -> dict:
    encoded = prompt.split("Round evidence JSON:\n", 1)[1].split(
        "\n\nReturn only the JSON object", 1
    )[0]
    return json.loads(encoded)


def test_review_receives_committed_current_diversity_and_resume_is_stable(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    first = candidate(70)
    duplicate = copy.deepcopy(first)
    duplicate["d"] = 999
    duplicate["fom"] = 9999.0
    second = candidate(71)
    source.write_bytes(jsonl(first, duplicate, second))
    config = FlowConfig(
        repo_dir=repo,
        run_id="review-current-diversity-resume",
        max_rounds=1,
        candidate_file=source,
        milp_top=0,
    )

    class CrashReviewer:
        def __init__(self):
            self.prompts = []

        def review(self, prompt, _round_dir):
            self.prompts.append(prompt)
            raise RuntimeError("crash after durable review request")

    crashing = CrashReviewer()
    with pytest.raises(RuntimeError, match="durable review request"):
        HumanizeFlow(config, reviewer=crashing).run()
    assert len(crashing.prompts) == 1
    first_prompt = crashing.prompts[0]
    first_evidence = _prompt_round_evidence(first_prompt)
    diversity = first_evidence["current_candidate_diversity"]
    assert diversity["raw_candidate_source_rows"] == 3
    assert diversity["canonical_unique_batch_rows"] == 2
    assert diversity["duplicate_count"] == 1

    class ResumeReviewer:
        def __init__(self):
            self.prompts = []

        def review(self, prompt, _round_dir):
            self.prompts.append(prompt)
            return Reviewer().review(prompt, _round_dir)

    resumed_reviewer = ResumeReviewer()
    completed = HumanizeFlow(config, reviewer=resumed_reviewer).run()

    assert completed["status"] == "search-complete"
    assert resumed_reviewer.prompts == [first_prompt]
    assert (
        repo
        / "results"
        / "humanize"
        / config.run_id
        / "rounds"
        / "round-001"
        / "review-request.md"
    ).read_text() == first_prompt


def test_review_phase_replays_transaction_and_fails_on_manifest_tamper(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    source.write_bytes(jsonl(candidate(72), candidate(73)))
    config = FlowConfig(
        repo_dir=repo,
        run_id="review-current-diversity-tamper",
        max_rounds=1,
        candidate_file=source,
        milp_top=0,
    )

    class CrashReviewer:
        def review(self, _prompt, _round_dir):
            raise RuntimeError("pause in review")

    with pytest.raises(RuntimeError, match="pause in review"):
        HumanizeFlow(config, reviewer=CrashReviewer()).run()
    manifest_path = (
        repo
        / "results"
        / "humanize"
        / config.run_id
        / "rounds"
        / "round-001"
        / "evolution-transaction.json"
    )
    manifest = json.loads(manifest_path.read_text())
    manifest["candidate_source_rows"] += 1
    atomic_write_json(manifest_path, manifest)

    class MustNotReview:
        def review(self, _prompt, _round_dir):
            raise AssertionError("tampered evidence reached the reviewer")

    with pytest.raises(RoundTransactionError):
        HumanizeFlow(config, reviewer=MustNotReview()).run()


def test_stage2_oracle_witness_is_replayed_into_next_round_context(
    tmp_path, monkeypatch
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    monkeypatch.setattr(
        candidate_evaluator,
        "symplectic_weight_bound",
        lambda code: (code.num_qudits, code.num_qudits, code.num_qudits),
    )
    row = candidate_evaluator.evaluate_candidate(
        12,
        6,
        [(0, 3), (6, 0)],
        [(1, 1), (2, 0), (6, 0), (9, 1)],
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )
    source = repo / "candidates.jsonl"
    source.write_bytes(jsonl(row))
    config = FlowConfig(
        repo_dir=repo,
        run_id="stage2-oracle-feedback",
        max_rounds=2,
        candidate_file=source,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    first_round = flow.store.round_dir(1)
    batch = flow._capture_round_candidates(state, 1, first_round)
    orphan_summary = flow_module._write_round_search_oracle_feedback(
        round_number=1,
        round_dir=first_round,
        candidate_rows=batch,
    )
    orphan_payload = (
        first_round / "search-oracle-feedback.json"
    ).read_bytes()
    # Simulate a crash after the atomic artifact write but before the round
    # state commit: recovery must reproduce and reuse the exact artifact.
    assert flow_module._write_round_search_oracle_feedback(
        round_number=1,
        round_dir=first_round,
        candidate_rows=batch,
    ) == orphan_summary
    assert (
        first_round / "search-oracle-feedback.json"
    ).read_bytes() == orphan_payload
    review = Reviewer().review("", first_round)
    atomic_write_json(first_round / "review.json", review)
    flow._finish_round(state, 1, batch, [], review, first_round)

    feedback = state["rounds"][0]["search_oracle_feedback"]
    assert feedback["replayed_witnesses"] == 1
    assert feedback["x_witnesses"] == 1
    artifact = json.loads(
        (first_round / "search-oracle-feedback.json").read_text()
    )
    [observation] = artifact["observations"]
    assert observation["support"] == row["low_weight_oracle"]["witness"][
        "support"
    ]
    assert observation["semantics"] == "negative_upper_bound_witness"

    second_round = flow.store.round_dir(2)
    context_path = flow_module._freeze_round_context(
        config, state, second_round
    )
    context = context_path.read_text()
    assert "Machine-replayed Stage-2 low-weight oracle witnesses" in context
    assert "negative-only upper-bound witnesses" in context
    assert '"support": [' in context
    assert all(str(index) in context for index in observation["support"])

    artifact["observations"][0]["support"][0] += 1
    atomic_write_json(
        first_round / "search-oracle-feedback.json", artifact
    )
    with pytest.raises(
        RoundTransactionError,
        match="search-oracle feedback",
    ):
        flow_module._previous_round_search_oracle_advisory(
            state, 1, first_round
        )

    forged = copy.deepcopy(row)
    forged["low_weight_oracle"]["witness"]["bits"][0] ^= 1
    with pytest.raises(
        RoundTransactionError,
        match="terminal Stage-2 low-weight oracle witness failed replay",
    ):
        flow_module._build_search_oracle_feedback(
            round_number=1,
            source_candidate_batch={
                "path": "candidate-batch.jsonl",
                "sha256": "a" * 64,
                "bytes": 1,
                "rows": 2,
            },
            candidate_rows=[forged, row],
        )

    # The current strict scalar-FOM target can reject a candidate with a
    # witness that does not exclude the smaller-n Pareto/final gate.  It is a
    # valid terminal scalar-negative row, but not a final-gate repair signal.
    current_scalar_only = copy.deepcopy(row)
    current_witness = current_scalar_only["low_weight_oracle"]["witness"]
    witness_weight = current_witness["weight"]
    scalar_cutoff = current_scalar_only["low_weight_oracle"]["max_weight"]
    assert witness_weight <= scalar_cutoff
    current_scalar_only.update({
        "fom_rejection_cutoff": scalar_cutoff,
        "challenge_rejection_cutoff": witness_weight - 1,
        "minimum_winning_distance": witness_weight,
        "threshold_rejected": True,
        "threshold_proof_distance": witness_weight,
        "threshold_proof_witness": copy.deepcopy(current_witness),
        "low_weight_witness": copy.deepcopy(current_witness),
        "distance_upper_bound": witness_weight,
        "distance_upper_bound_source": "low_weight_oracle",
        "fom_target_excluded_by_upper_bound": True,
        "final_gate_excluded_by_upper_bound": False,
        "search_final_gate_excluded_by_upper_bound": False,
    })
    monkeypatch.setattr(
        candidate_evaluator,
        "compute_challenge_rejection_cutoff",
        lambda _n, _k, _target: witness_weight - 1,
    )
    monkeypatch.setattr(
        candidate_evaluator,
        "compute_fom_rejection_cutoff",
        lambda _n, _k, _target: scalar_cutoff,
    )
    scalar_round = repo / "scalar-only-round"
    scalar_round.mkdir()
    scalar_payload = jsonl(current_scalar_only)
    scalar_round_row = json.loads(scalar_payload)
    (scalar_round / "candidate-batch.jsonl").write_bytes(scalar_payload)
    scalar_feedback = flow_module._write_round_search_oracle_feedback(
        round_number=2,
        round_dir=scalar_round,
        candidate_rows=[scalar_round_row],
    )
    assert scalar_feedback["replay_attempts"] == 0
    assert scalar_feedback["replayed_witnesses"] == 0
    scalar_artifact = json.loads(
        (scalar_round / "search-oracle-feedback.json").read_text()
    )
    assert scalar_artifact["observations"] == []

    # A known old evaluator may be migrated only after the complete, unchanged
    # construction/oracle/witness replays and its scalar-only metadata matches.
    # Patch only the cutoff functions to model a Pareto gap for this real,
    # algebraically replayable fixture; do not forge its n/k or evidence.
    stale_scalar_only = copy.deepcopy(row)
    stale_witness = stale_scalar_only["low_weight_oracle"]["witness"]
    witness_weight = stale_witness["weight"]
    scalar_cutoff = stale_scalar_only["low_weight_oracle"]["max_weight"]
    assert witness_weight <= scalar_cutoff
    stale_scalar_only.update({
        "fom_rejection_cutoff": scalar_cutoff,
        "challenge_rejection_cutoff": scalar_cutoff,
        "minimum_winning_distance": scalar_cutoff + 1,
        "threshold_rejected": True,
        "threshold_proof_distance": witness_weight,
        "threshold_proof_witness": copy.deepcopy(stale_witness),
        "low_weight_witness": copy.deepcopy(stale_witness),
        "distance_upper_bound": witness_weight,
        "distance_upper_bound_source": "low_weight_oracle",
        "fom_target_excluded_by_upper_bound": True,
        "final_gate_excluded_by_upper_bound": True,
        "search_final_gate_excluded_by_upper_bound": True,
    })
    monkeypatch.setattr(
        candidate_evaluator,
        "compute_challenge_rejection_cutoff",
        lambda _n, _k, _target: witness_weight - 1,
    )
    monkeypatch.setattr(
        candidate_evaluator,
        "compute_fom_rejection_cutoff",
        lambda _n, _k, _target: scalar_cutoff,
    )
    feedback = flow_module._build_search_oracle_feedback(
        round_number=1,
        source_candidate_batch={
            "path": "candidate-batch.jsonl",
            "sha256": "b" * 64,
            "bytes": 1,
            "rows": 1,
        },
        candidate_rows=[stale_scalar_only],
        allow_historical_scalar_cutoff=True,
    )
    assert feedback["replay_attempts"] == 0
    assert feedback["observations"] == []

    corrupted_stale = copy.deepcopy(stale_scalar_only)
    corrupted_stale["low_weight_oracle"]["witness"]["bits"][0] ^= 1
    with pytest.raises(
        RoundTransactionError,
        match="terminal Stage-2 low-weight oracle witness failed replay",
    ):
        flow_module._build_search_oracle_feedback(
            round_number=1,
            source_candidate_batch={
                "path": "candidate-batch.jsonl",
                "sha256": "c" * 64,
                "bytes": 1,
                "rows": 1,
            },
            candidate_rows=[corrupted_stale],
            allow_historical_scalar_cutoff=True,
        )


def test_next_round_freezes_machine_diversity_advisory(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="machine-diversity-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    state["current_round"] = 1
    state["rounds"] = [{
        "round": 1,
        "candidate_diversity": {
            "schema_version": 1,
            "basis": "transaction-bound-source-and-canonical-batch",
            "raw_candidate_source_rows": 10,
            "canonical_unique_batch_rows": 4,
            "duplicate_count": 6,
            "duplicate_rate": 0.6,
            "candidate_source_sha256": "a" * 64,
            "candidate_batch_sha256": "b" * 64,
            "support_split_counts": {"2+2": 3, "3+3": 1},
            "mixed_vs_nonmixed_counts": {
                "mixed": 1,
                "nonmixed": 3,
                "unclassified": 0,
            },
        },
    }]
    flow.store.memory_path.write_text("base bitlesson\n")
    round_dir = flow.store.round_dir(2)

    transaction = flow._prepare_transaction(state, 2, round_dir)
    context_path = round_dir / "search-context.md"
    frozen = context_path.read_bytes()
    text = frozen.decode()

    assert "## Machine-derived previous-round diversity advisory" in text
    assert "Raw source rows: 10; canonical unique batch rows: 4." in text
    assert "Exact duplicate rows: 6 (60.00%)." in text
    assert "Support-split distribution (|A|+|B|): 2+2=3, 3+3=1." in text
    assert (
        "Mixed-vs-nonmixed distribution: "
        "mixed=1, nonmixed=3, unclassified=0."
    ) in text
    assert "reduce exact repeats" in text
    assert "correct structural collapse" in text
    assert transaction["launch_binding"]["context"]["sha256"] == (
        hashlib.sha256(frozen).hexdigest()
    )

    # Once prepared, later state changes cannot rewrite the launch-bound
    # advisory for this round.
    state["rounds"][0]["candidate_diversity"]["duplicate_count"] = 0
    state["rounds"][0]["candidate_diversity"]["duplicate_rate"] = 0.0
    recovered = flow._load_transaction(state, 2, round_dir)

    assert recovered is not None
    assert context_path.read_bytes() == frozen
    assert "Exact duplicate rows: 6 (60.00%)." in context_path.read_text()


def test_legacy_round_summary_without_diversity_keeps_context_unchanged(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-diversity-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    state["current_round"] = 1
    state["rounds"] = [{
        "round": 1,
        "review_summary": "legacy state has no machine diversity field",
    }]
    flow.store.memory_path.write_text("legacy bitlesson\n")

    context_path = flow_module._freeze_round_context(
        config,
        state,
        flow.store.round_dir(2),
    )

    assert context_path.read_text() == "legacy bitlesson\n\n"
    assert "Machine-derived" not in context_path.read_text()


def _reviewer_v2(
    round_number: int,
    *,
    intent: str = "maintain",
    verdict: str = "continue",
    horizon_rounds: int = 1,
) -> dict:
    return validate_review(
        {
            "schema_version": 2,
            "verdict": verdict,
            "summary": f"Independent review for round {round_number}.",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
            "search_action": {
                "schema_version": 1,
                "advisory_only": True,
                "intent": intent,
                "horizon_rounds": horizon_rounds,
                "focus": [],
                "evidence_refs": [
                    {
                        "source": "round_history",
                        "round": round_number,
                        "candidate_key": None,
                    }
                ],
                "rationale": f"review-action-round-{round_number}",
            },
        },
        require_current=True,
    )


def _write_bound_round_review(
    flow: HumanizeFlow,
    round_number: int,
    *,
    intent: str = "maintain",
    verdict: str = "continue",
    horizon_rounds: int = 1,
    focus: list[dict] | None = None,
) -> tuple[dict, Path, dict]:
    round_dir = flow.store.round_dir(round_number)
    review_path = round_dir / "review.json"
    review = _reviewer_v2(
        round_number,
        intent=intent,
        verdict=verdict,
        horizon_rounds=horizon_rounds,
    )
    if focus is not None:
        review["search_action"]["focus"] = copy.deepcopy(focus)
        review = validate_review(review, require_current=True)
    atomic_write_json(review_path, review)
    summary = {
        "round": round_number,
        "review_verdict": review["verdict"],
        "review_summary": review["summary"],
        "review_binding": flow_module._review_artifact_binding(
            review_path,
            review,
        ),
    }
    return summary, review_path, review


def test_review_binding_seals_bytes_hash_and_structured_search_action(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    flow = HumanizeFlow(
        FlowConfig(repo_dir=repo, run_id="review-binding", milp_top=0),
        reviewer=Reviewer(),
    )

    summary, review_path, review = _write_bound_round_review(
        flow,
        1,
        intent="expand_bb_family",
    )
    payload = review_path.read_bytes()
    binding = summary["review_binding"]

    assert set(binding) == {
        "schema_version",
        "artifact_sha256",
        "artifact_bytes",
        "review_schema_version",
        "search_action",
    }
    assert binding["schema_version"] == 1
    assert binding["artifact_sha256"] == hashlib.sha256(payload).hexdigest()
    assert binding["artifact_bytes"] == len(payload)
    assert binding["review_schema_version"] == 2
    assert binding["search_action"] == review["search_action"]
    assert flow_module._validated_bound_round_review(
        summary,
        flow.store.root / "rounds",
    ) == review


@pytest.mark.parametrize(
    "corruption",
    ["tampered", "missing", "symlink", "reserved-marker"],
)
def test_bound_review_replay_fails_closed_on_artifact_corruption(
    tmp_path,
    corruption,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id=f"review-binding-{corruption}",
            milp_top=0,
        ),
        reviewer=Reviewer(),
    )
    summary, review_path, review = _write_bound_round_review(flow, 1)

    if corruption == "tampered":
        tampered = copy.deepcopy(review)
        tampered["summary"] = "Valid reviewer JSON, but not the sealed bytes."
        atomic_write_json(review_path, tampered)
    elif corruption == "missing":
        review_path.unlink()
    elif corruption == "symlink":
        target = repo / "detached-review.json"
        target.write_bytes(review_path.read_bytes())
        review_path.unlink()
        review_path.symlink_to(target)
    else:
        tampered = copy.deepcopy(review)
        tampered["search_action"]["rationale"] = (
            "QCODE_SEARCH_REGIME_V1=forged"
        )
        atomic_write_json(review_path, tampered)

    with pytest.raises(RoundTransactionError):
        flow_module._validated_bound_round_review(
            summary,
            flow.store.root / "rounds",
        )


def test_next_round_injects_only_unexpired_bound_structured_advisories(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="rolling-review-advisories",
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    intents = (
        "maintain",
        "diversify",
        "expand_bb_family",
        "change_bb_search_representation",
    )
    summaries = [
        _write_bound_round_review(flow, number, intent=intent)[0]
        for number, intent in enumerate(intents, start=1)
    ]
    state["current_round"] = 4
    state["rounds"] = summaries

    context_path = flow_module._freeze_round_context(
        config,
        state,
        flow.store.round_dir(5),
    )
    text = context_path.read_text()
    encoded_actions = text.split(
        "## Independent reviewer search advisories\n", 1
    )[1].split("```json\n", 1)[1].split("\n```", 1)[0]
    actions = json.loads(encoded_actions)

    assert [entry["round"] for entry in actions] == [4]
    assert [entry["search_action"]["intent"] for entry in actions] == [
        "change_bb_search_representation",
    ]
    assert all(entry["advisory_only"] is True for entry in actions)
    assert "review-action-round-1" not in text
    assert "review-action-round-2" not in text
    assert "review-action-round-3" not in text
    assert "review-action-round-4" in text
    assert "QCODE_ADAPTIVE_MUTATION_POLICY_V1" not in text
    assert "QCODE_SEARCH_REGIME_V1" not in text
    assert "cannot alter machine regimes" in text


@pytest.mark.parametrize("horizon_rounds", [1, 2, 3])
def test_bound_executable_action_uses_real_verdict_and_enforces_horizon(
    tmp_path,
    horizon_rounds,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    flow = HumanizeFlow(
        FlowConfig(repo_dir=repo, run_id="bound-action-gate", milp_top=0),
        reviewer=Reviewer(),
    )
    rounds_root = flow.store.root / "rounds"
    active, _path, _review = _write_bound_round_review(
        flow,
        2,
        intent="diversify",
        horizon_rounds=horizon_rounds,
    )
    # Unbound summary mirrors are never authority for either verdict or action.
    active["review_verdict"] = "reject_round"
    active["review_binding"]["search_action"] = copy.deepcopy(
        active["review_binding"]["search_action"]
    )

    for target_round in range(3, 3 + horizon_rounds):
        assert flow_module._bound_executable_search_action(
            active, rounds_root, target_round
        )["intent"] == "diversify"
    assert flow_module._bound_executable_search_action(
        active, rounds_root, 3 + horizon_rounds
    ) is None

    rejected, _path, rejected_review = _write_bound_round_review(
        flow,
        3,
        intent="expand_bb_family",
        verdict="reject_round",
        horizon_rounds=3,
    )
    assert rejected_review["search_action"]["intent"] == "expand_bb_family"
    rejected["review_verdict"] = "continue"
    assert flow_module._bound_executable_search_action(
        rejected, rounds_root, 4
    ) is None
    # Audit metadata is retained even though it cannot enter execution.
    assert rejected["review_binding"]["search_action"] == (
        rejected_review["search_action"]
    )


def test_scientific_selector_focus_replays_only_bound_in_horizon_action(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    flow = HumanizeFlow(
        FlowConfig(repo_dir=repo, run_id="scientific-review-focus", milp_top=0),
        reviewer=Reviewer(),
    )
    item = {
        "dimension": "support_split_type",
        "value": "2+3",
        "direction": "increase",
        "priority": "high",
    }
    summary, review_path, review = _write_bound_round_review(
        flow,
        1,
        intent="explore_undercovered",
        horizon_rounds=2,
        focus=[item],
    )
    rounds_root = flow.store.root / "rounds"

    projected = flow_module._scientific_selector_reviewer_focus(
        [summary],
        rounds_root=rounds_root,
        target_round=2,
    )
    assert projected["source_round"] == 1
    assert projected["artifact_sha256"] == summary["review_binding"][
        "artifact_sha256"
    ]
    assert projected["focus"] == [item]
    assert flow_module._scientific_selector_reviewer_focus(
        [summary],
        rounds_root=rounds_root,
        target_round=4,
    ) is None

    rejected, _path, _review = _write_bound_round_review(
        flow,
        2,
        intent="explore_undercovered",
        verdict="reject_round",
        horizon_rounds=2,
        focus=[item],
    )
    assert flow_module._scientific_selector_reviewer_focus(
        [rejected],
        rounds_root=rounds_root,
        target_round=3,
    ) is None

    tampered = copy.deepcopy(review)
    tampered["search_action"]["focus"][0]["value"] = "3+2"
    atomic_write_json(review_path, tampered)
    with pytest.raises(RoundTransactionError):
        flow_module._scientific_selector_reviewer_focus(
            [summary],
            rounds_root=rounds_root,
            target_round=2,
        )


def test_policy_v2_context_projects_reviewer_to_closed_structured_action(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prompt-safe-reviewer-v2",
        milp_top=0,
        search_representation_id="css-bb-test-v2",
        search_regime_policy_version=2,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    summary, review_path, review = _write_bound_round_review(
        flow,
        1,
        intent="change_bb_search_representation",
    )
    python_instruction = (
        "import os; os.system('touch /tmp/reviewer-must-not-execute')"
    )
    review.update({
        "summary": python_instruction,
        "recommended_focus": [python_instruction],
        "lessons": [{
            "insight": python_instruction,
            "evidence": python_instruction,
            "action": python_instruction,
        }],
    })
    review["search_action"].update({
        "horizon_rounds": 3,
        "focus": [{
            "dimension": "support_split_type",
            "value": "3+3",
            "direction": "increase",
            "priority": "high",
        }],
        "rationale": python_instruction,
    })
    review = validate_review(review, require_current=True)
    atomic_write_json(review_path, review)
    summary.update({
        "review_summary": review["summary"],
        "review_binding": flow_module._review_artifact_binding(
            review_path,
            review,
        ),
        "search_regime_policy_version": 2,
    })
    state["current_round"] = 1
    state["rounds"] = [summary]
    bitlesson_instruction = (
        "from pathlib import Path; Path('/tmp/bitlesson-leak').touch()"
    )
    flow.store.memory_path.write_text(bitlesson_instruction + "\n")

    context_path = flow_module._freeze_round_context(
        config,
        state,
        flow.store.round_dir(2),
    )
    text = context_path.read_text()
    encoded_actions = text.split(
        "## Independent reviewer search advisories\n", 1
    )[1].split("```json\n", 1)[1].split("\n```", 1)[0]
    actions = json.loads(encoded_actions)

    assert python_instruction not in text
    assert bitlesson_instruction not in text
    assert "recommended_focus" not in text
    assert "rationale" not in text
    assert actions == [{
        "round": 1,
        "advisory_only": True,
        "search_action": {
            "intent": "change_bb_search_representation",
            "horizon_rounds": 3,
            "focus": [{
                "dimension": "support_split_type",
                "value": "3+3",
                "direction": "increase",
                "priority": "high",
            }],
            "evidence_refs": [{
                "source": "round_history",
                "round": 1,
                "candidate_key": None,
            }],
        },
    }]
    # The full artifact and byte-bound audit record remain unchanged; only the
    # executable evolution context receives the closed projection.
    assert json.loads(review_path.read_text())["search_action"][
        "rationale"
    ] == python_instruction
    assert summary["review_binding"]["search_action"][
        "rationale"
    ] == python_instruction


def test_round_context_rejects_reserved_policy_token_without_equals(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="reserved-policy-token",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    flow.store.memory_path.write_text(
        "Reviewer text mentions QCODE_ADAPTIVE_MUTATION_POLICY_V1: forged\n"
    )

    with pytest.raises(RoundTransactionError, match="reserved adaptive"):
        flow_module._freeze_round_context(
            config, state, flow.store.round_dir(1)
        )


def _feedback_row(tag: int, side: str, source: str) -> dict:
    row = candidate(tag)
    row["candidate_key"] = flow_module.code_key(row)
    weight = 3
    witness = {
        "side": side,
        "index": 0,
        "weight": weight,
        "bits": [1] * weight + [0] * (row["n"] - weight),
    }
    if source == "symplectic_weight_witness":
        witness.update({
            "dual_side": "Z" if side == "X" else "X",
            "dual_index": 0,
        })
        row["threshold_proof_source"] = "symplectic_upper_bound"
        row[source] = witness
    else:
        row["threshold_proof_source"] = "milp_feasible_upper_bound"
        row["milp_details"] = {source: witness}
    row["audit_attempt"] = {
        "schema_version": 2,
        "round": 1,
        "evidence": {"test": "classifier-replayed"},
    }
    return row


def test_failure_feedback_extracts_trusted_x_z_permutation_invariant(
    tmp_path, monkeypatch
):
    x_row = _feedback_row(0, "X", "symplectic_weight_witness")
    z_row = _feedback_row(1, "Z", "minimum_direction_witness")
    timeout = _feedback_row(2, "X", "minimum_direction_witness")
    timeout["distance_status"] = "hard_timeout"
    timeout["audit_attempt"] = {"schema_version": 1}

    def classify(row, **_kwargs):
        if row.get("distance_status") == "hard_timeout":
            return flow_module.AuditOutcome.UNRESOLVED_NO_INCUMBENT
        return flow_module.AuditOutcome.THRESHOLD_REJECTED

    monkeypatch.setattr(flow_module, "classify_evaluation", classify)
    source = {
        "path": "milp.jsonl",
        "sha256": "a" * 64,
        "bytes": 123,
        "rows": 3,
    }
    first = flow_module._build_failure_direction_feedback(
        round_number=1,
        source_milp=source,
        audited_rows=[x_row, timeout, z_row],
    )
    second = flow_module._build_failure_direction_feedback(
        round_number=1,
        source_milp=source,
        audited_rows=[z_row, x_row, timeout],
    )

    assert first == second
    assert sorted(item["side"] for item in first["observations"]) == ["X", "Z"]
    assert {
        item["source"] for item in first["observations"]
    } == {"symplectic_weight_witness", "minimum_direction_witness"}
    tactics = first["mutation_policy"]["tactics"]
    assert [item["tactic"] for item in tactics] == list(
        flow_module.ADAPTIVE_MUTATION_TACTICS
    )
    assert all(type(item["weight"]) is int for item in tactics)
    assert sum(item["weight"] for item in tactics) == 1000
    assert tactics[0]["weight"] >= 250
    assert all(item["weight"] > 0 for item in tactics[1:])


def test_untrusted_timeout_does_not_vote_in_failure_policy(
    monkeypatch,
):
    timeout = _feedback_row(3, "X", "minimum_direction_witness")
    timeout["audit_attempt"] = {"schema_version": 1}
    monkeypatch.setattr(
        flow_module,
        "classify_evaluation",
        lambda _row, **_kwargs: (
            flow_module.AuditOutcome.UNRESOLVED_NO_INCUMBENT
        ),
    )
    feedback = flow_module._build_failure_direction_feedback(
        round_number=1,
        source_milp={
            "path": "milp.jsonl",
            "sha256": "b" * 64,
            "bytes": 1,
            "rows": 1,
        },
        audited_rows=[timeout],
    )

    assert feedback["observations"] == []
    assert [item["weight"] for item in feedback["mutation_policy"]["tactics"]] == [
        1000,
        0,
        0,
        0,
    ]


def test_failure_feedback_context_is_deterministic_and_tamper_fails(
    tmp_path, monkeypatch
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="failure-feedback-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    x_row = _feedback_row(0, "X", "symplectic_weight_witness")
    z_row = _feedback_row(1, "Z", "minimum_direction_witness")
    monkeypatch.setattr(
        flow_module,
        "classify_evaluation",
        lambda _row, **_kwargs: flow_module.AuditOutcome.THRESHOLD_REJECTED,
    )
    previous_dir = flow.store.round_dir(1)
    (previous_dir / "milp.jsonl").write_bytes(jsonl(z_row, x_row))
    feedback_summary = (
        flow_module._write_round_failure_direction_feedback(
            round_number=1,
            round_dir=previous_dir,
            audited_rows=[x_row, z_row],
        )
    )
    state["current_round"] = 1
    state["rounds"] = [{
        "round": 1,
        "failure_direction_feedback": feedback_summary,
    }]
    current_dir = flow.store.round_dir(2)

    context = flow_module._freeze_round_context(
        config, state, current_dir
    )
    frozen = context.read_bytes()
    policy_lines = [
        line for line in context.read_text().splitlines()
        if line.startswith("QCODE_ADAPTIVE_MUTATION_POLICY_V1=")
    ]
    assert len(policy_lines) == 1
    policy_mapping = json.loads(policy_lines[0].split("=", 1)[1])
    assert set(policy_mapping) == set(flow_module.ADAPTIVE_MUTATION_TACTICS)
    assert policy_mapping == {
        item["tactic"]: item["weight"]
        for item in json.loads(
            (
                previous_dir / "failure-direction-feedback.json"
            ).read_text()
        )["mutation_policy"]["tactics"]
    }
    assert evolution_launcher._validated_adaptive_mutation_policy(
        context.read_text()
    ) == policy_mapping
    assert "trusted sealed low-weight logical witnesses: 2 (X=1, Z=1)" in (
        context.read_text()
    )
    assert "negative_upper_bound_witness" in context.read_text()
    assert '"support": [' in context.read_text()
    assert '"block_support": [' in context.read_text()
    assert '"A_terms": [' in context.read_text()
    assert '"ell": 6' in context.read_text()
    context.unlink()
    assert flow_module._freeze_round_context(
        config, state, current_dir
    ).read_bytes() == frozen

    artifact_path = previous_dir / "failure-direction-feedback.json"
    artifact = json.loads(artifact_path.read_text())
    artifact["mutation_policy"]["total_weight"] = 999
    artifact_path.write_text(
        flow_module._canonical_compact_json(artifact) + "\n"
    )
    context.unlink()
    with pytest.raises(RoundTransactionError, match="self-hash"):
        flow_module._freeze_round_context(config, state, current_dir)


def test_prepare_quarantines_context_orphaned_before_manifest(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="orphan-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    orphan = round_dir / "search-context.md"
    orphan.write_text("context written before process death\n")

    transaction = flow._prepare_transaction(state, 1, round_dir)

    archives = list(round_dir.glob("orphan-search-context-*.md"))
    assert len(archives) == 1
    assert archives[0].read_text() == "context written before process death\n"
    assert transaction["launch_binding"]["context"]["path"] == str(
        (round_dir / "search-context.md").resolve()
    )
    assert (round_dir / "search-context.md").read_text() != archives[
        0
    ].read_text()


def test_prepared_transaction_rejects_worker_budget_tampering(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    (repo / "evolve/config.yaml").write_text(
        "evaluator:\n  parallel_evaluations: 6\n"
    )
    config = FlowConfig(
        repo_dir=repo,
        run_id="worker-binding-tamper",
        iterations_per_round=3,
        milp_top=0,
        max_total_workers=4,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    assert manifest["invocation_binding"]["max_parallel_evaluations"] == 4
    manifest["invocation_binding"]["max_parallel_evaluations"] = 5
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="unified worker budget",
    ):
        flow._load_transaction(state, 1, round_dir)


@pytest.mark.parametrize(
    "tamper",
    ("context", "dependency", "invocation"),
)
def test_prepared_transaction_rejects_frozen_launch_tampering(
    tmp_path, tamper
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"binding-tamper-{tamper}",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"

    if tamper == "context":
        (round_dir / "search-context.md").write_text("tampered context\n")
        expected = "launch inputs changed"
    elif tamper == "dependency":
        (repo / "evaluation/evaluator.py").write_text(
            "# tampered evaluator dependency\n"
        )
        expected = "launch inputs changed"
    else:
        manifest = json.loads(manifest_path.read_text())
        manifest["invocation_binding"]["model_names"] = ["tampered-model"]
        atomic_write_json(manifest_path, manifest)
        expected = "model binding changed"

    with pytest.raises(flow_module.RoundTransactionError, match=expected):
        flow._load_transaction(state, 1, round_dir)


@pytest.mark.parametrize(
    ("dependency_field", "relative_path"),
    (
        pytest.param(
            "evaluation_evaluator",
            "evaluation/evaluator.py",
            id="evaluator",
        ),
        pytest.param(
            "evaluation_search_contract",
            "evaluation/search_contract.py",
            id="representation-geometry-contract",
        ),
    ),
)
def test_prepared_transaction_rebinds_changed_sources_and_archives_old_attempt(
    tmp_path,
    dependency_field,
    relative_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-source-rebind",
        iterations_per_round=3,
        milp_top=0,
    )
    old_row = candidate(31)
    new_row = candidate(32)
    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert flow.candidate_log.read_bytes() == b""
        assert (
            runner_round / "abandoned-checkpoint-attempt-001"
        ).is_dir()
        assert (
            runner_round
            / "abandoned-completion-marker-attempt-001.json"
        ).is_file()
        assert (
            runner_round / "abandoned-slice-witness-attempt-001.json"
        ).is_file()
        flow.candidate_log.write_bytes(jsonl(new_row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    old_dependency = transaction["launch_binding"][dependency_field]
    flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    flow.candidate_log.write_bytes(jsonl(old_row))
    old_checkpoint = write_checkpoint(repo, config.run_id, 3)
    write_full_slice_proof(flow, round_dir, old_checkpoint, None)

    dependency = repo / relative_path
    dependency.write_text(f"# upgraded {dependency_field} source\n")
    rows = flow._capture_round_candidates(state, 1, round_dir)

    assert rows == [new_row]
    assert runner_calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["status"] == "committed"
    assert len(manifest["evolution_binding_rebinds"]) == 1
    rebind = manifest["evolution_binding_rebinds"][0]
    assert rebind["status"] == "rebound"
    assert f"launch:{dependency_field}" in rebind["reason"]
    assert (
        rebind["old_launch_binding"][dependency_field]
        == old_dependency
    )
    assert (
        rebind["new_launch_binding"][dependency_field]
        == flow_module._file_descriptor(
            dependency,
            f"current {dependency_field}",
        )
    )
    assert rebind["old_binding_sha256"] != rebind["new_binding_sha256"]
    assert rebind["abandoned_ranges_after"] == 1
    assert rebind["abandoned_checkpoints_after"] == 1
    assert (
        round_dir / "abandoned-candidate-tail-001.bin"
    ).read_bytes() == jsonl(old_row)
    assert (
        round_dir / "abandoned-candidate-complete-001.jsonl"
    ).read_bytes() == jsonl(old_row)
    assert manifest["abandoned_checkpoints"][0]["attempt"] == 1


def test_geometry_portfolio_invocation_and_completion_self_describe_contract(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo, geometry_portfolio=True)
    config = FlowConfig(
        repo_dir=repo,
        run_id="geometry-contract-witness",
        max_rounds=12,
        iterations_per_round=3,
        milp_top=0,
        search_representation_id="css-bb-twisted-torus-generator-v1",
        search_regime_policy_version=3,
    )

    def runner(_config, _state, runner_round):
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(jsonl(candidate(41)))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config,
        reviewer=Reviewer(),
        evolution_runner=runner,
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    assert flow._capture_round_candidates(state, 1, round_dir) == [
        candidate(41),
    ]

    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    invocation = manifest["invocation_binding"]
    assert invocation["search_geometry_contract"] == "twisted-torus-v1"
    witness = json.loads(flow_module._slice_witness_path(round_dir).read_text())
    marker = json.loads(
        flow_module._completion_marker_path(round_dir).read_text()
    )
    assert witness["search_geometry_contract"] == "twisted-torus-v1"
    assert marker["search_geometry_contract"] == "twisted-torus-v1"


def test_explicit_legacy_representation_keeps_exact_legacy_invocation_shape(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo, portfolio=True)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-contract-shape",
        iterations_per_round=3,
        milp_top=0,
        search_representation_id="css-bb-cover-algebra-generator-v2",
        search_regime_policy_version=2,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    transaction = flow._prepare_transaction(
        state,
        1,
        flow.store.round_dir(1),
    )

    assert set(transaction["invocation_binding"]) == set(
        flow_module.EVOLUTION_INVOCATION_FIELDS
    )
    assert "search_geometry_contract" not in transaction[
        "invocation_binding"
    ]


@pytest.mark.parametrize(
    ("geometry_portfolio", "portfolio", "representation_id", "message"),
    (
        (
            True,
            False,
            "css-bb-twisted-torus-generator-vl",
            "requires a known twisted-torus",
        ),
        (
            True,
            False,
            "css-bb-cover-algebra-generator-v2",
            "schema v3 requires the twisted-torus",
        ),
        (
            False,
            True,
            "css-bb-twisted-torus-generator-v1",
            "requires geometry-aware search portfolio schema v3",
        ),
    ),
)
def test_representation_geometry_schema_mismatch_fails_before_child(
    tmp_path,
    geometry_portfolio,
    portfolio,
    representation_id,
    message,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(
        repo,
        geometry_portfolio=geometry_portfolio,
        portfolio=portfolio,
    )
    runner_calls = []

    def forbidden_runner(*_args, **_kwargs):
        runner_calls.append(True)
        raise AssertionError("invalid geometry contract launched a child")

    config = FlowConfig(
        repo_dir=repo,
        run_id="invalid-geometry-contract",
        max_rounds=12,
        iterations_per_round=3,
        milp_top=0,
        search_representation_id=representation_id,
        search_regime_policy_version=3,
    )
    flow = HumanizeFlow(
        config,
        reviewer=Reviewer(),
        evolution_runner=forbidden_runner,
    )
    state = flow.store.initialize(config.serializable())
    with pytest.raises(flow_module.RoundTransactionError, match=message):
        flow._capture_round_candidates(state, 1, flow.store.round_dir(1))
    assert runner_calls == []


def test_unbound_prepared_transaction_migrates_allowlisted_legacy_binding(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-legacy-binding",
        iterations_per_round=3,
        milp_top=0,
    )
    old_row = candidate(33)
    new_row = candidate(34)
    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert flow.candidate_log.read_bytes() == b""
        flow.candidate_log.write_bytes(jsonl(new_row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    oldest_launch = dict(manifest["launch_binding"])
    for field in (
        "evaluation_geometry",
        "evaluation_final_gate",
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        oldest_launch.pop(field)
    previous_launch = dict(manifest["launch_binding"])
    for field in (
        "evaluation_geometry",
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        previous_launch.pop(field)
    invocation = manifest["invocation_binding"]
    oldest_sha256 = flow_module._binding_identity_sha256(
        oldest_launch, invocation
    )
    previous_sha256 = flow_module._binding_identity_sha256(
        previous_launch, invocation
    )

    def historical_rebind(
        attempt, old_launch, old_sha256, new_launch, new_sha256
    ):
        return {
            "attempt": attempt,
            "status": "rebound",
            "reason": "historical launch binding schema",
            "old_launch_binding": old_launch,
            "old_invocation_binding": invocation,
            "old_binding_sha256": old_sha256,
            "candidate_start_offset": manifest["candidate_start_offset"],
            "evolution_attempts_before": 0,
            "abandoned_ranges_before": 0,
            "abandoned_checkpoints_before": 0,
            "planned_at": "legacy",
            "new_launch_binding": new_launch,
            "new_invocation_binding": invocation,
            "new_binding_sha256": new_sha256,
            "evolution_attempts_after": 0,
            "abandoned_ranges_after": 0,
            "abandoned_checkpoints_after": 0,
            "rebound_at": "legacy",
        }

    manifest["launch_binding"] = previous_launch
    manifest["evolution_binding_rebinds"] = [
        historical_rebind(
            1,
            oldest_launch,
            oldest_sha256,
            oldest_launch,
            oldest_sha256,
        ),
        historical_rebind(
            2,
            oldest_launch,
            oldest_sha256,
            previous_launch,
            previous_sha256,
        ),
    ]
    atomic_write_json(manifest_path, manifest)
    flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    flow.candidate_log.write_bytes(jsonl(old_row))

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow._load_transaction(state, 1, round_dir)
    assert flow.candidate_log.read_bytes() == jsonl(old_row)

    rows = flow._capture_round_candidates(state, 1, round_dir)

    assert rows == [new_row]
    assert runner_calls == [True]
    durable = json.loads(manifest_path.read_text())
    assert durable["status"] == "committed"
    assert len(durable["evolution_binding_rebinds"]) == 3
    migration = durable["evolution_binding_rebinds"][2]
    assert migration["status"] == "rebound"
    assert "launch:evaluation_search_contract" in migration["reason"]
    assert (
        "evaluation_search_contract"
        not in migration["old_launch_binding"]
    )
    assert (
        "evaluation_search_contract"
        in migration["new_launch_binding"]
    )
    assert (
        round_dir / "abandoned-candidate-complete-001.jsonl"
    ).read_bytes() == jsonl(old_row)
    flow._validate_completed_transaction(1, round_dir)


def test_completed_round_accepts_only_immediately_previous_dependency_shape(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="completed-previous-dependency-shape",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    current_launch = transaction["launch_binding"]
    previous_launch = dict(current_launch)
    previous_launch.pop("evaluation_geometry")

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow_module._validate_stored_binding_shape(
            config,
            previous_launch,
            transaction["invocation_binding"],
            round_dir,
            current_launch,
        )

    validated, _invocation = flow_module._validate_stored_binding_shape(
        config,
        previous_launch,
        transaction["invocation_binding"],
        round_dir,
        current_launch,
        allow_previous_committed=True,
    )
    assert validated == previous_launch

    older_launch = dict(previous_launch)
    older_launch.pop("evaluation_search_contract")
    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow_module._validate_stored_binding_shape(
            config,
            older_launch,
            transaction["invocation_binding"],
            round_dir,
            current_launch,
            allow_previous_committed=True,
        )

    # `_load_transaction` is also used for a committed-but-pending round at
    # phase=screen. Verify it routes that state through the append-only
    # historical schema allowlist instead of the live/prepared schema gate.
    transaction["status"] = "committed"
    transaction["launch_binding"] = previous_launch
    atomic_write_json(
        round_dir / "evolution-transaction.json",
        transaction,
    )
    loaded = flow._load_transaction(state, 1, round_dir)
    assert loaded is not None
    assert loaded["status"] == "committed"
    assert loaded["launch_binding"] == previous_launch


def test_prepared_binding_history_rejects_legacy_schema_downgrade(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-legacy-schema-downgrade",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    invocation = manifest["invocation_binding"]
    previous_launch = dict(manifest["launch_binding"])
    for field in (
        "evaluation_geometry",
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        previous_launch.pop(field)
    oldest_launch = dict(previous_launch)
    oldest_launch.pop("evaluation_final_gate")
    previous_sha256 = flow_module._binding_identity_sha256(
        previous_launch, invocation
    )
    oldest_sha256 = flow_module._binding_identity_sha256(
        oldest_launch, invocation
    )
    manifest["launch_binding"] = oldest_launch
    manifest["evolution_binding_rebinds"] = [{
        "attempt": 1,
        "status": "rebound",
        "reason": "tampered schema downgrade",
        "old_launch_binding": previous_launch,
        "old_invocation_binding": invocation,
        "old_binding_sha256": previous_sha256,
        "candidate_start_offset": manifest["candidate_start_offset"],
        "evolution_attempts_before": 0,
        "abandoned_ranges_before": 0,
        "abandoned_checkpoints_before": 0,
        "planned_at": "legacy",
        "new_launch_binding": oldest_launch,
        "new_invocation_binding": invocation,
        "new_binding_sha256": oldest_sha256,
        "evolution_attempts_after": 0,
        "abandoned_ranges_after": 0,
        "abandoned_checkpoints_after": 0,
        "rebound_at": "legacy",
    }]
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="downgrades its schema",
    ):
        flow._load_transaction(
            state, 1, round_dir, allow_prepared_rebind=True
        )


@pytest.mark.parametrize(
    "missing_field",
    ("evaluation_evaluator", "evaluation_results"),
)
def test_prepared_transaction_rejects_unallowlisted_legacy_shape(
    tmp_path, missing_field
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"prepared-bad-legacy-{missing_field}",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["launch_binding"].pop(missing_field)
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow._capture_round_candidates(state, 1, round_dir)
    assert json.loads(manifest_path.read_text())[
        "evolution_binding_rebinds"
    ] == []


@pytest.mark.parametrize(
    ("status", "bind_source"),
    (
        ("prepared", True),
        ("source-ready", False),
        ("batch-ready", False),
        ("committed", False),
    ),
)
def test_legacy_binding_is_not_migrated_after_source_binding(
    tmp_path, status, bind_source
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"bound-legacy-{status}",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    for field in (
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        manifest["launch_binding"].pop(field)
    manifest["status"] = status
    if bind_source:
        manifest["candidate_end_offset"] = manifest[
            "candidate_start_offset"
        ]
    atomic_write_json(manifest_path, manifest)
    before = manifest_path.read_bytes()

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow._load_transaction(
            state, 1, round_dir, allow_prepared_rebind=True
        )
    assert manifest_path.read_bytes() == before


def test_interrupted_prepared_binding_rebind_resumes_from_its_wal(
    tmp_path, monkeypatch
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-rebind-crash",
        iterations_per_round=3,
        milp_top=0,
    )
    old_row = candidate(41)
    new_row = candidate(42)
    initial = HumanizeFlow(config, reviewer=Reviewer())
    state = initial.store.initialize(config.serializable())
    round_dir = initial.store.round_dir(1)
    initial._prepare_transaction(state, 1, round_dir)
    initial.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    initial.candidate_log.write_bytes(jsonl(old_row))
    write_checkpoint(repo, config.run_id, 3)
    flow_module._completion_marker_path(round_dir).write_text(
        '{"old": "marker"}\n'
    )
    flow_module._slice_witness_path(round_dir).write_text(
        '{"old": "witness"}\n'
    )
    (repo / "evaluation/evaluator.py").write_text(
        "# upgraded evaluator source\n"
    )

    original_quarantine = (
        initial._quarantine_untrusted_evolution_attempt
    )

    class SimulatedProcessDeath(BaseException):
        pass

    def crash_after_quarantine(
        transaction, target_round, checkpoint, *, reason
    ):
        original_quarantine(
            transaction,
            target_round,
            checkpoint,
            reason=reason,
        )
        raise SimulatedProcessDeath

    monkeypatch.setattr(
        initial,
        "_quarantine_untrusted_evolution_attempt",
        crash_after_quarantine,
    )
    with pytest.raises(SimulatedProcessDeath):
        initial._capture_round_candidates(state, 1, round_dir)

    durable = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert durable["evolution_binding_rebinds"][0]["status"] == "rebinding"
    assert len(durable["abandoned_ranges"]) == 1
    assert len(durable["abandoned_checkpoints"]) == 1
    assert initial.candidate_log.read_bytes() == b""

    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert initial.candidate_log.read_bytes() == b""
        initial.candidate_log.write_bytes(jsonl(new_row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(resumed, runner_round, checkpoint, None)
        return checkpoint

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    rows = resumed._capture_round_candidates(
        resumed.store.load_state(), 1, round_dir
    )

    assert rows == [new_row]
    assert runner_calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["evolution_binding_rebinds"][0]["status"] == "rebound"
    assert len(manifest["evolution_binding_rebinds"]) == 1
    assert len(manifest["abandoned_ranges"]) == 1
    assert len(manifest["abandoned_checkpoints"]) == 1
    assert len(list(round_dir.glob("abandoned-candidate-tail-*.bin"))) == 1
    assert len(list(round_dir.glob("abandoned-checkpoint-attempt-*"))) == 1


def test_completed_transaction_preserves_historical_source_binding(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="completed-source-change",
        iterations_per_round=3,
        milp_top=0,
    )

    def runner(_config, _state, runner_round):
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._capture_round_candidates(state, 1, round_dir)
    (repo / "evaluation/evaluator.py").write_text(
        "# source changed after commit\n"
    )

    rows = flow._capture_round_candidates(
        flow.store.load_state(), 1, round_dir
    )
    assert rows == []
    flow._validate_completed_transaction(1, round_dir)
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["status"] == "committed"
    assert manifest["evolution_binding_rebinds"] == []
    assert (
        manifest["launch_binding"]["evaluation_evaluator"]["sha256"]
        != flow_module._file_sha256(repo / "evaluation/evaluator.py")
    )

    # Finishing the historical round must not weaken the next launch: the
    # following prepared transaction freezes the new evaluator bytes.
    next_state = flow.store.load_state()
    next_state["current_round"] = 1
    next_state["pending_round"] = None
    next_state["round_phase"] = None
    next_state.pop("round_transaction_version", None)
    flow.store.write_state(next_state)
    next_round = flow.store.round_dir(2)
    next_transaction = flow._prepare_transaction(
        next_state, 2, next_round
    )
    assert (
        next_transaction["launch_binding"]["evaluation_evaluator"]["sha256"]
        == flow_module._file_sha256(repo / "evaluation/evaluator.py")
    )


@pytest.mark.parametrize("durable_status", ("source-ready", "batch-ready"))
def test_bound_transaction_rejects_source_rebinding(
    tmp_path, monkeypatch, durable_status
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"{durable_status}-source-change",
        iterations_per_round=3,
        milp_top=0,
    )
    row = candidate(51)

    def runner(_config, _state, runner_round):
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(jsonl(row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    original_write = flow_module.atomic_write_json

    class SimulatedProcessDeath(BaseException):
        pass

    def crash_after_bound_manifest(path, value):
        result = original_write(path, value)
        if (
            path.name == "evolution-transaction.json"
            and value.get("status") == durable_status
        ):
            raise SimulatedProcessDeath
        return result

    monkeypatch.setattr(
        flow_module, "atomic_write_json", crash_after_bound_manifest
    )
    with pytest.raises(SimulatedProcessDeath):
        flow._capture_round_candidates(state, 1, round_dir)
    monkeypatch.setattr(flow_module, "atomic_write_json", original_write)
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == durable_status

    (repo / "evaluation/evaluator.py").write_text(
        "# source changed after source binding\n"
    )
    resumed = HumanizeFlow(config, reviewer=Reviewer())
    with pytest.raises(
        flow_module.RoundTransactionError,
        match="launch inputs changed",
    ):
        resumed._capture_round_candidates(
            resumed.store.load_state(), 1, round_dir
        )
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["status"] == durable_status
    assert manifest["evolution_binding_rebinds"] == []


def test_prepared_rebind_rejects_malformed_frozen_identity(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="malformed-rebind-identity",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["launch_binding"]["evaluation_evaluator"]["sha256"] = (
        "not-a-sha256"
    )
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="malformed or redirected",
    ):
        flow._capture_round_candidates(state, 1, round_dir)
    assert json.loads(manifest_path.read_text())[
        "evolution_binding_rebinds"
    ] == []


@pytest.mark.parametrize("tamper", ("binary", "version"))
def test_codex_execution_identity_is_frozen_and_revalidated(
    tmp_path, monkeypatch, tamper
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    native = repo / "fake-codex"
    native.write_bytes(b"\x7fELFfake-codex-v1")
    native.chmod(0o755)
    version = {"value": "codex-test 1.0"}
    monkeypatch.setattr(
        flow_module, "_resolve_native_codex_path", lambda _requested: native
    )
    monkeypatch.setattr(
        flow_module, "_codex_version", lambda _executable: version["value"]
    )
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"codex-binding-{tamper}",
        iterations_per_round=3,
        milp_top=0,
        codex_cli=True,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)

    transaction = flow._prepare_transaction(state, 1, round_dir)

    executable = transaction["launch_binding"]["codex_executable"]
    invocation = transaction["invocation_binding"]
    assert executable["path"] == str(native.resolve())
    assert executable["mode"] == 0o755
    assert invocation["codex_version"] == "codex-test 1.0"
    assert invocation["codex_cwd"] == str(repo.resolve())

    if tamper == "binary":
        native.write_bytes(b"\x7fELFfake-codex-v2")
    else:
        version["value"] = "codex-test 2.0"

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="Codex CLI native executable changed|Codex execution identity changed",
    ):
        flow._load_transaction(state, 1, round_dir)


@pytest.mark.parametrize(
    ("tamper", "message"),
    (
        ("invocation", "witness mismatch for model_names"),
        ("no-success", "no successful program"),
        ("program-identity", "program identity is invalid"),
    ),
)
def test_completed_transaction_replays_exact_witness_binding(
    tmp_path, tamper, message
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"witness-binding-{tamper}",
        iterations_per_round=3,
        milp_top=0,
    )

    def runner(_config, _state, runner_round):
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._capture_round_candidates(state, 1, round_dir)

    witness_path = flow_module._slice_witness_path(round_dir)
    marker_path = flow_module._completion_marker_path(round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    witness = json.loads(witness_path.read_text())
    if tamper == "invocation":
        witness["model_names"] = ["tampered-model"]
    elif tamper == "no-success":
        witness["outcomes"][0] = {
            "iteration": 1,
            "status": "worker_error",
            "error_sha256": hashlib.sha256(b"tampered error").hexdigest(),
            "error_bytes": len(b"tampered error"),
        }
        witness["successful_evaluations"] = 0
        witness["worker_errors"] = 3
    else:
        witness["outcomes"][0]["program_sha256"] = "not-a-digest"
    atomic_write_json(witness_path, witness)

    witness_identity = flow_module._file_descriptor(
        witness_path, "tampered witness"
    )
    marker = json.loads(marker_path.read_text())
    marker["slice_witness_sha256"] = witness_identity["sha256"]
    marker["slice_witness_bytes"] = witness_identity["bytes"]
    if tamper == "invocation":
        marker["model_names"] = ["tampered-model"]
    atomic_write_json(marker_path, marker)

    manifest = json.loads(manifest_path.read_text())
    manifest["completion_witness_sha256"] = witness_identity["sha256"]
    manifest["completion_marker_sha256"] = flow_module._file_sha256(marker_path)
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(flow_module.RoundTransactionError, match=message):
        flow._validate_completed_transaction(1, round_dir)
