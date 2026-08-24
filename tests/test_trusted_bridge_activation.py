from __future__ import annotations

import hashlib
from copy import deepcopy

import pytest

from archon.commands.loop import trusted_bridge_activation as activation
from archon.commands.loop.parallel_formalization_review import (
    _DORMANT_TRUSTED_BRIDGE_PROTOCOL,
    _validate_certificate,
)
from archon.commands.loop.prover.runners import (
    _ImmediateRedraftPromptError,
    _validate_complete_repair_projection,
    build_immediate_redraft_prompt,
)
from archon.commands.loop.review_feedback import build_repair_task


TARGET = "Problems/problem_a.lean"
CANDIDATE_SHA256 = "1" * 64
RULE_ID = "mellitic_acid_p2o5_heating_forms_some_trianhydride"
SECOND_RULE_ID = "closed_domain_mellite_terminal_residue_candidate_filter"


def _certificate(*, requests: list[dict] | None = None) -> dict:
    return {
        "schema_version": 2,
        "status": "failed",
        "reason": "one bridge lacks a source-pinned authority",
        "checks": {
            name: {
                "status": "failed" if name == "derivability" else "passed",
                "evidence": "bounded audit evidence",
            }
            for name in (
                "source_faithfulness",
                "derivability",
                "abstraction_sufficiency",
                "uncertainty_propagation",
                "branch_orientation",
                "countermodel_resistance",
            )
        },
        "bridge_obligations": [{
            "claim": "REVIEWER_CLAIM_MUST_NOT_BECOME_TRUSTED_RULE_TEXT",
            "carrier": "Missing.bridge",
            "status": "blocked",
            "evidence": "source bridge is absent",
        }],
        "trusted_bridge_requests": requests if requests is not None else [],
        "source_contract": {
            "schema_version": 1,
            "contract_kind": "native_problem_input_only",
            "authority": "problem-only",
            "evaluation_mode": "answer_blind",
            "target": TARGET,
            "candidate": TARGET,
            "candidate_sha256": CANDIDATE_SHA256,
        },
    }


def _request(rule_id: str = RULE_ID, index: int = 0) -> dict:
    return {"bridge_obligation_index": index, "rule_id": rule_id}


def _retry_gate_record(
    certificate: dict | None = None,
    *,
    candidate_sha256: str = CANDIDATE_SHA256,
) -> dict:
    return {
        "status": "retry",
        "reviews": 1,
        "last_review_iter": 1,
        "candidate_sha256": candidate_sha256,
        "certificate": certificate or _certificate(),
        "repair_events": [{
            "schema_version": 1,
            "review_kind": "formalization",
            "candidate_sha256": candidate_sha256,
            "iteration": 1,
            "attempt": 1,
            "resulting_status": "retry",
            "decision": "failed",
            "event_id": f"batch:1:{TARGET}:formalization",
            "failed_check_ids": ["bridge_obligations[0]"],
        }],
    }


def _sha256(value: object) -> str:
    return hashlib.sha256(activation._canonical_json_bytes(value)).hexdigest()


def _rehash_lookup(lookup: dict) -> None:
    unsigned = dict(lookup)
    unsigned.pop("record_sha256", None)
    lookup["record_sha256"] = _sha256(unsigned)


def _contract(*, target: str = TARGET, candidate: str = CANDIDATE_SHA256) -> dict:
    return {
        "contract_kind": "native_problem_input_only",
        "target": target,
        "candidate": target,
        "candidate_sha256": candidate,
        "source_bundle_sha256": "2" * 64,
        "source_record_sha256": "3" * 64,
        "answer_submission_sha256": "4" * 64,
        "question_sha256": "5" * 64,
        "requested_outputs_sha256": "6" * 64,
    }


def _lookup(rule_id: str) -> dict:
    return {
        "schema_version": 1,
        "service": "archon_offline_chemistry_reference",
        "dataset_version": "sealed-v1",
        "dataset_sha256": "7" * 64,
        "operation": "empirical_rule",
        "runtime_network_access": False,
        "query": {"rule": rule_id},
        "result": {
            "applicability_conditions": ["CATALOG_APPLICABILITY"],
            "authority_kind": "peer_reviewed_literature",
            "automatic_problem_instantiation": False,
            "claim": "CATALOG_PINNED_CLAIM",
            "exclusions": ["CATALOG_EXCLUSION"],
            "rule_id": rule_id,
            "rule_version": 1,
        },
        "source": {
            "content_sha256": "8" * 64,
            "doi": "10.1000/example",
            "locator": "p. 1",
            "url": "https://example.test/paper",
        },
        "approval": {
            "approval_scope": "rule_and_source",
            "approved_at": "2026-08-24T00:00:00Z",
            "reviewer_id": "reviewer-1",
            "status": "approved",
        },
        "base_dataset_sha256": "9" * 64,
        "empirical_registry_manifest_sha256": "a" * 64,
        "pinned_rule_record_sha256": "b" * 64,
        "record_sha256": "c" * 64,
    }


def _enable_unit_catalog(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        activation, "is_native_problem_only_contract", lambda value: True
    )
    monkeypatch.setattr(
        activation,
        "validate_native_review_source_certificate",
        lambda *_args, **_kwargs: "",
    )
    monkeypatch.setattr(activation, "_validated_catalog_lookup", _lookup)


@pytest.mark.parametrize(
    "mutation",
    [
        "passing_verdict",
        "covered_bridge",
        "failed_bridge",
        "unknown_id",
        "baseline_id",
        "extra_claim",
        "extra_url",
        "duplicate_rule",
        "two_rules_one_bridge",
    ],
)
def test_request_schema_is_exact_failed_blocked_and_minimal(mutation: str) -> None:
    certificate = _certificate(requests=[_request()])
    if mutation == "passing_verdict":
        certificate["status"] = "passed"
    elif mutation == "covered_bridge":
        certificate["bridge_obligations"][0]["status"] = "covered"
    elif mutation == "failed_bridge":
        certificate["bridge_obligations"][0]["status"] = "failed"
    elif mutation == "unknown_id":
        certificate["trusted_bridge_requests"][0]["rule_id"] = "unknown_rule"
    elif mutation == "baseline_id":
        certificate["trusted_bridge_requests"][0]["rule_id"] = (
            "mellite_ideal_stoichiometry"
        )
    elif mutation == "extra_claim":
        certificate["trusted_bridge_requests"][0]["claim"] = "INJECTED"
    elif mutation == "extra_url":
        certificate["trusted_bridge_requests"][0]["url"] = (
            "https://attacker.test"
        )
    else:
        certificate["bridge_obligations"].append({
            **certificate["bridge_obligations"][0],
            "carrier": "Missing.second",
        })
        certificate["trusted_bridge_requests"].append(
            _request(
                RULE_ID if mutation == "duplicate_rule" else SECOND_RULE_ID,
                1 if mutation == "duplicate_rule" else 0,
            )
        )

    assert activation.validate_trusted_bridge_requests(certificate)


@pytest.mark.parametrize(
    "status",
    ["fail", "partial", "needs_redraft", "rejected", "missing"],
)
def test_request_rejects_every_noncanonical_failed_status(status: str) -> None:
    certificate = _certificate(requests=[_request()])
    certificate["status"] = status

    assert activation.validate_trusted_bridge_requests(certificate)


@pytest.mark.parametrize(
    "status",
    ["fail", "failed", "partial", "needs_redraft", "rejected", "missing"],
)
def test_request_rejects_every_noncanonical_blocked_status(status: str) -> None:
    certificate = _certificate(requests=[_request()])
    certificate["bridge_obligations"][0]["status"] = status

    assert activation.validate_trusted_bridge_requests(certificate)


def test_parallel_certificate_validator_and_prompt_expose_only_id_requests() -> None:
    certificate = _certificate(requests=[_request()])
    row = {
        "status": "blocked",
        "formalization_review": certificate,
    }

    assert _validate_certificate(row) == ""
    assert RULE_ID not in _DORMANT_TRUSTED_BRIDGE_PROTOCOL
    assert SECOND_RULE_ID not in _DORMANT_TRUSTED_BRIDGE_PROTOCOL
    assert "exact dormant" in _DORMANT_TRUSTED_BRIDGE_PROTOCOL
    assert "Never supply a claim, source, URL" in _DORMANT_TRUSTED_BRIDGE_PROTOCOL


@pytest.mark.parametrize(
    "mutation", ["claim", "service", "dataset_version"],
)
def test_catalog_rejects_resigned_lookup_envelope_or_content_attack(
    mutation: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    lookup = deepcopy(activation.chemistry_constant.empirical_rule(RULE_ID))
    if mutation == "claim":
        attacker_registry = deepcopy(
            activation.chemistry_constant._EMPIRICAL_REGISTRY
        )
        record = next(
            item
            for item in attacker_registry["records"]
            if item["rule"]["rule_id"] == RULE_ID
        )
        record["rule"]["claim"] = "ATTACKER_RESIGNED_CLAIM"
        unsigned_record = dict(record)
        unsigned_record.pop("record_sha256")
        record["record_sha256"] = _sha256(unsigned_record)
        manifest = attacker_registry["manifest"]
        entry = next(
            item for item in manifest["records"] if item["rule_id"] == RULE_ID
        )
        entry["record_sha256"] = record["record_sha256"]
        unsigned_manifest = dict(manifest)
        unsigned_manifest.pop("manifest_sha256")
        manifest["manifest_sha256"] = _sha256(unsigned_manifest)
        lookup["result"] = deepcopy(record["rule"])
        lookup["source"] = deepcopy(record["source"])
        lookup["approval"] = deepcopy(record["review"])
        lookup["pinned_rule_record_sha256"] = record["record_sha256"]
        lookup["empirical_registry_manifest_sha256"] = manifest[
            "manifest_sha256"
        ]
        monkeypatch.setattr(
            activation.chemistry_constant,
            "_EMPIRICAL_REGISTRY",
            attacker_registry,
        )
    elif mutation == "service":
        lookup["service"] = "attacker_service"
    else:
        lookup["dataset_version"] = "attacker_dataset"
    _rehash_lookup(lookup)
    monkeypatch.setattr(
        activation.chemistry_constant,
        "empirical_rule",
        lambda _rule_id: deepcopy(lookup),
    )

    assert activation._validated_catalog_lookup(RULE_ID) is None


@pytest.mark.parametrize(
    "mutation", ["missing", "duplicate", "rule_version", "record_sha256"],
)
def test_catalog_rejects_nonunique_or_mismatched_manifest_entry(
    mutation: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sealed = activation.chemistry_constant._load_empirical_registry()
    entries = sealed["manifest"]["records"]
    matching = [entry for entry in entries if entry["rule_id"] == RULE_ID]
    assert len(matching) == 1
    entry = matching[0]
    if mutation == "missing":
        entries.remove(entry)
    elif mutation == "duplicate":
        entries.append(deepcopy(entry))
    elif mutation == "rule_version":
        entry["rule_version"] += 1
    else:
        entry["record_sha256"] = "0" * 64
    monkeypatch.setattr(
        activation.chemistry_constant,
        "_load_empirical_registry",
        lambda: deepcopy(sealed),
    )

    assert activation._validated_catalog_lookup(RULE_ID) is None


def test_unrequested_dormant_rule_is_not_activated(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)

    projection = activation.build_trusted_bridge_activation_projection(
        _certificate(),
        target_rel=TARGET,
        candidate_sha256=CANDIDATE_SHA256,
        expected_source_contract=_contract(),
    )

    assert projection == {}


def test_controller_rebuilds_complete_catalog_receipt_not_reviewer_text(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)

    projection = activation.build_trusted_bridge_activation_projection(
        _certificate(requests=[_request()]),
        target_rel=TARGET,
        candidate_sha256=CANDIDATE_SHA256,
        expected_source_contract=_contract(),
    )

    assert projection["complete"] is True
    assert projection["requested_count"] == projection["activated_count"] == 1
    receipt = projection["receipts"][0]
    assert receipt["target"] == {
        "file": TARGET,
        "candidate_sha256": CANDIDATE_SHA256,
    }
    assert receipt["rule"]["claim"] == "CATALOG_PINNED_CLAIM"
    assert receipt["rule"]["applicability_conditions"] == [
        "CATALOG_APPLICABILITY"
    ]
    assert receipt["rule"]["exclusions"] == ["CATALOG_EXCLUSION"]
    assert receipt["source"]["url"] == "https://example.test/paper"
    assert receipt["review"]["status"] == "approved"
    assert set(receipt["catalog_binding"]) == {
        "base_dataset_sha256",
        "dataset_sha256",
        "empirical_registry_manifest_sha256",
        "lookup_record_sha256",
        "pinned_rule_record_sha256",
        "source_content_sha256",
    }
    assert receipt["scope"] == "next_target_local_formalization_redraft_only"
    assert "REVIEWER_CLAIM" not in str(receipt)


@pytest.mark.parametrize("mismatch", ["target", "candidate"])
def test_target_or_candidate_mismatch_never_yields_a_receipt(
    mismatch: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)
    contract = _contract(
        target="Problems/problem_b.lean" if mismatch == "target" else TARGET,
        candidate="0" * 64 if mismatch == "candidate" else CANDIDATE_SHA256,
    )

    projection = activation.build_trusted_bridge_activation_projection(
        _certificate(requests=[_request()]),
        target_rel=TARGET,
        candidate_sha256=CANDIDATE_SHA256,
        expected_source_contract=contract,
    )

    assert projection["complete"] is False
    assert projection["activated_count"] == 0
    assert projection["receipts"] == []


def test_missing_catalog_record_fails_closed_without_partial_activation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)
    monkeypatch.setattr(activation, "_validated_catalog_lookup", lambda _id: None)

    projection = activation.build_trusted_bridge_activation_projection(
        _certificate(requests=[_request()]),
        target_rel=TARGET,
        candidate_sha256=CANDIDATE_SHA256,
        expected_source_contract=_contract(),
    )

    assert projection["complete"] is False
    assert projection["requested_count"] == 1
    assert projection["receipts"] == []


def test_repair_handoff_injects_activation_inside_complete_source_projection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)
    monkeypatch.setattr(
        "archon.commands.loop.review_feedback._source_bound_formalization_review",
        lambda *_args, **_kwargs: {
            "certificate_sha256": "d" * 64,
            "source_contract_sha256": "e" * 64,
            "source_binding": {"candidate_sha256": CANDIDATE_SHA256},
            "reason": "blocked bridge",
            "repair_action_projection": {
                "bridge_obligations_count": 1,
                "failed_bridge_count": 1,
                "retained_count": 1,
                "truncated": False,
                "bridge_obligations_sha256": "f" * 64,
            },
            "repair_actions": [{
                "check_id": "bridge_obligations[0]",
                "source_claim": "untrusted checklist claim",
                "current_carrier": "Missing.bridge",
                "evidence": "untrusted checklist evidence",
            }],
        },
    )
    record = {
        "status": "retry",
        "reviews": 1,
        "candidate_sha256": CANDIDATE_SHA256,
        "certificate": _certificate(requests=[_request()]),
        "repair_events": [{
            "schema_version": 1,
            "review_kind": "formalization",
            "candidate_sha256": CANDIDATE_SHA256,
            "iteration": 1,
            "attempt": 1,
            "resulting_status": "retry",
            "decision": "failed",
            "failed_check_ids": ["bridge_obligations[0]"],
        }],
    }

    task = build_repair_task(
        record,
        review_kind="formalization",
        worker_stage="formalization",
        candidate_sha256=CANDIDATE_SHA256,
        expected_source_contract=_contract(),
        target_rel=TARGET,
    )

    source_review = task["source_bound_review"]
    assert source_review["trusted_bridge_activations"]["complete"] is True
    _validate_complete_repair_projection(task, deepcopy(task))

    incomplete = deepcopy(task)
    incomplete["source_bound_review"]["trusted_bridge_activations"][
        "receipts"
    ] = []
    with pytest.raises(_ImmediateRedraftPromptError):
        _validate_complete_repair_projection(task, incomplete)


@pytest.mark.parametrize("batch_wrapper", [False, True])
def test_next_reviewer_context_is_rebuilt_for_only_the_same_target_transition(
    batch_wrapper: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)
    certificate = _certificate(requests=[_request()])
    if batch_wrapper:
        certificate = {"milestones": [certificate]}
    record = _retry_gate_record(certificate)
    current_sha256 = "0" * 64

    context = activation.build_trusted_bridge_review_context(
        record,
        target_rel=TARGET,
        current_candidate_sha256=current_sha256,
        expected_source_contract=_contract(candidate=current_sha256),
    )

    assert context["target"] == {
        "file": TARGET,
        "activation_input_candidate_sha256": CANDIDATE_SHA256,
        "current_candidate_sha256": current_sha256,
    }
    assert context["trusted_bridge_activations"]["complete"] is True
    assert context["context_receipt_sha256"]
    assert activation.build_trusted_bridge_review_context(
        record,
        target_rel="Problems/problem_b.lean",
        current_candidate_sha256=current_sha256,
        expected_source_contract=_contract(candidate=current_sha256),
    ) == {}


@pytest.mark.parametrize(
    "mutation",
    [
        "missing_status",
        "passed",
        "review_exhausted",
        "solved",
        "missing_reviews",
        "zero_reviews",
        "bool_reviews",
        "missing_last_review_iter",
        "missing_repair_events",
        "event_candidate",
        "event_attempt",
        "event_iteration",
        "event_decision",
        "event_status",
        "event_kind",
        "next_failed_event",
    ],
)
def test_next_reviewer_context_requires_exact_retry_lifecycle(
    mutation: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)
    record = _retry_gate_record(_certificate(requests=[_request()]))
    if mutation == "missing_status":
        record.pop("status")
    elif mutation in {"passed", "review_exhausted", "solved"}:
        record["status"] = mutation
    elif mutation == "missing_reviews":
        record.pop("reviews")
    elif mutation == "zero_reviews":
        record["reviews"] = 0
    elif mutation == "bool_reviews":
        record["reviews"] = True
    elif mutation == "missing_last_review_iter":
        record.pop("last_review_iter")
    elif mutation == "missing_repair_events":
        record.pop("repair_events")
    elif mutation.startswith("event_"):
        field = mutation.removeprefix("event_")
        values = {
            "candidate": ("candidate_sha256", "9" * 64),
            "attempt": ("attempt", 2),
            "iteration": ("iteration", 2),
            "decision": ("decision", "passed"),
            "status": ("resulting_status", "passed"),
            "kind": ("review_kind", "proof"),
        }
        key, value = values[field]
        record["repair_events"][-1][key] = value
    else:
        record["reviews"] = 2
        record["last_review_iter"] = 2
        record["certificate"] = _certificate()
        record["repair_events"].append({
            **record["repair_events"][-1],
            "iteration": 2,
            "attempt": 2,
            "event_id": f"batch:2:{TARGET}:formalization",
        })

    assert activation.build_trusted_bridge_review_context(
        record,
        target_rel=TARGET,
        current_candidate_sha256="0" * 64,
        expected_source_contract=_contract(candidate="0" * 64),
    ) == {}


def test_initial_or_non_review_redraft_has_no_activation_context(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_unit_catalog(monkeypatch)
    kwargs = {
        "target_rel": TARGET,
        "current_candidate_sha256": "0" * 64,
        "expected_source_contract": _contract(candidate="0" * 64),
    }
    assert activation.build_trusted_bridge_review_context(None, **kwargs) == {}
    reopened = _retry_gate_record(_certificate(requests=[_request()]))
    reopened["reopened_by"] = "proof_review"
    reopened["certificate"] = {}
    assert (
        activation.build_trusted_bridge_review_context(reopened, **kwargs)
        == {}
    )


@pytest.mark.parametrize(
    ("rule_id", "pinned_sha256"),
    [
        (
            "mellitic_acid_p2o5_heating_forms_some_trianhydride",
            "3b7cdcf821c3e9a5dd9afa3619055d24128848437b7c52d0af517b61c64c5e1a",
        ),
        (
            "closed_domain_mellite_terminal_residue_candidate_filter",
            "cdb1daf3b0e543ce4e17e399324a2fb3d05c13a2cb896fd692b0d74f9db940f6",
        ),
    ],
)
def test_real_sealed_lookup_flows_through_receipt_redraft_and_next_review(
    rule_id: str,
    pinned_sha256: str,
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    monkeypatch.setattr(
        activation, "is_native_problem_only_contract", lambda value: True
    )
    monkeypatch.setattr(
        activation,
        "validate_native_review_source_certificate",
        lambda *_args, **_kwargs: "",
    )
    certificate = _certificate(requests=[_request(rule_id)])
    lookup = activation._validated_catalog_lookup(rule_id)

    assert lookup is not None
    assert lookup["pinned_rule_record_sha256"] == pinned_sha256
    projection = activation.build_trusted_bridge_activation_projection(
        certificate,
        target_rel=TARGET,
        candidate_sha256=CANDIDATE_SHA256,
        expected_source_contract=_contract(),
    )
    assert projection["complete"] is True
    receipt = projection["receipts"][0]
    assert receipt["catalog_binding"]["pinned_rule_record_sha256"] == pinned_sha256
    assert receipt["rule"] == lookup["result"]
    assert receipt["source"] == lookup["source"]
    assert receipt["review"] == lookup["approval"]

    monkeypatch.setattr(
        "archon.commands.loop.review_feedback._source_bound_formalization_review",
        lambda *_args, **_kwargs: {
            "certificate_sha256": "d" * 64,
            "source_contract_sha256": "e" * 64,
            "source_binding": {"candidate_sha256": CANDIDATE_SHA256},
            "reason": "blocked bridge",
            "repair_action_projection": {
                "bridge_obligations_count": 1,
                "failed_bridge_count": 1,
                "retained_count": 1,
                "truncated": False,
                "bridge_obligations_sha256": "f" * 64,
            },
            "repair_actions": [{
                "check_id": "bridge_obligations[0]",
                "source_claim": "review checklist only",
                "current_carrier": "Missing.bridge",
                "evidence": "review checklist only",
            }],
        },
    )
    record = _retry_gate_record(certificate)
    task = build_repair_task(
        record,
        review_kind="formalization",
        worker_stage="formalization",
        candidate_sha256=CANDIDATE_SHA256,
        expected_source_contract=_contract(),
        target_rel=TARGET,
    )
    assert task["source_bound_review"]["trusted_bridge_activations"][
        "receipts"
    ][0]["rule"] == lookup["result"]

    target = tmp_path / TARGET
    target.parent.mkdir(parents=True)
    target.write_text("theorem placeholder : True := by trivial\n", encoding="utf-8")
    state = tmp_path / ".archon"
    state.mkdir()
    monkeypatch.setattr(
        "archon.commands.loop.prover.runners.select_prover_mode_for_target",
        lambda *_args, **_kwargs: "chemistry-formalize",
    )
    monkeypatch.setattr(
        "archon.commands.loop.prover.runners._sealed_mode_reference",
        lambda *_args, **_kwargs: "sealed-mode-reference",
    )
    monkeypatch.setattr(
        "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
        lambda *_args, **_kwargs: "BASE REDRAFT PROMPT",
    )
    monkeypatch.setattr(
        "archon.commands.loop.prover.runners._native_formalizer_semantic_dag_block",
        lambda **_kwargs: "",
    )
    prompt = build_immediate_redraft_prompt(
        project_name="fixture",
        project_path=tmp_path,
        state_dir=state,
        iter_num=2,
        target=target,
        review_certificate=task,
        debug_feedback=False,
        handoff_label="formalization Review",
    )
    assert "controller_trusted_bridge_activation" in prompt
    assert lookup["result"]["claim"] in prompt
    assert lookup["source"]["locator"] in prompt
    assert "normal empirical-rule lookup" in prompt

    current_candidate_sha256 = "0" * 64
    context = activation.build_trusted_bridge_review_context(
        record,
        target_rel=TARGET,
        current_candidate_sha256=current_candidate_sha256,
        expected_source_contract=_contract(candidate=current_candidate_sha256),
    )
    assert context["trusted_bridge_activations"]["complete"] is True
    assert context["trusted_bridge_activations"]["receipts"][0]["rule"] == (
        lookup["result"]
    )
    assert context["target"]["current_candidate_sha256"] == (
        current_candidate_sha256
    )
