from __future__ import annotations

import importlib.util
import json
from copy import deepcopy
from pathlib import Path

import pytest


_MODULE_PATH = (
    Path(__file__).parents[1]
    / "src/archon/commands/loop/prior_result_dependency.py"
)
_SPEC = importlib.util.spec_from_file_location(
    "prior_result_dependency_under_test", _MODULE_PATH
)
assert _SPEC is not None and _SPEC.loader is not None
prior = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(prior)


A4 = "icho_2026_t1_a4"
A5 = "icho_2026_t1_a5"
A6 = "icho_2026_t1_a6"
PROBLEM = "icho_2026_t1"
SHARED = "shared official T1 context"
PDF_SHA = "1" * 64
PRODUCER_BUNDLE_SHA = "2" * 64
CONSUMER_BUNDLE_SHA = "3" * 64
OUTPUT_IDS = {
    A4: (
        "metal_q_identity", "hydrated_c_formula", "compound_d_formula",
    ),
    A5: (
        "compound_e_structure", "compound_f_structure",
        "compound_g_structure",
    ),
}


def _review(
    *,
    status: str,
    candidate_sha256: str,
    source_record_sha256: str,
    answer_submission_sha256: str,
    marker: str,
) -> dict:
    return {
        "status": status,
        "candidate_sha256": candidate_sha256,
        "certificate_sha256": marker * 64,
        "source_contract_sha256": ("c" if marker != "c" else "d") * 64,
        "source_bundle_sha256": PRODUCER_BUNDLE_SHA,
        "source_record_sha256": source_record_sha256,
        "answer_submission_sha256": answer_submission_sha256,
        "official_answer_seen": False,
    }


def _producer(
    source_id: str,
    previous_ids: list[str],
    binding: dict,
    *,
    marker: str,
) -> dict:
    module = f"IChO2026Problems/problem_{source_id}.lean"
    module_sha256 = marker * 64
    source_record_sha256 = ("d" if marker != "d" else "e") * 64
    answer_submission_sha256 = ("e" if marker != "e" else "f") * 64
    typed_exports = []
    for index, output_id in enumerate(OUTPUT_IDS[source_id]):
        payload = {
            "output_id": output_id,
            "kind": "formula",
            "raw_value": f"derived-{source_id}-{output_id}",
            "display_value": f"derived-{source_id}-{output_id}",
            "unit": "",
        }
        expected_type = (
            f"{source_id}.Result{index} = {source_id}.derivedValue{index}"
        )
        typed_exports.append({
            "export_id": f"certified_prior_result:{source_id}:{output_id}",
            "module": module,
            "module_sha256": module_sha256,
            "declaration": (
                f"IChO2026Problems.{source_id}.derivedResult{index}"
            ),
            "expected_type": expected_type,
            "expected_type_sha256": prior._hash(expected_type),
            "result_payload": payload,
            "result_payload_sha256": prior._hash(payload),
        })
    return {
        "schema_version": 1,
        "controller_binding": deepcopy(binding),
        "source_id": source_id,
        "source_record_sha256": source_record_sha256,
        "previous_part_source_ids": previous_ids,
        "previous_part_source_ids_sha256": prior._hash(previous_ids),
        "source_bundle_sha256": PRODUCER_BUNDLE_SHA,
        "answer_submission_sha256": answer_submission_sha256,
        "official_answer_seen": False,
        "module": module,
        "module_sha256": module_sha256,
        "formalization_review": _review(
            status="passed",
            candidate_sha256="9" * 64,
            source_record_sha256=source_record_sha256,
            answer_submission_sha256=answer_submission_sha256,
            marker="a",
        ),
        "proof_review": _review(
            status="solved",
            candidate_sha256=module_sha256,
            source_record_sha256=source_record_sha256,
            answer_submission_sha256=answer_submission_sha256,
            marker="b",
        ),
        "compile_audit": {
            "status": "passed",
            "candidate_sha256": module_sha256,
            "audit_sha256": "6" * 64,
            "returncode": 0,
            "sorry_count": 0,
        },
        "axiom_audit": {
            "status": "passed",
            "candidate_sha256": module_sha256,
            "audit_sha256": "7" * 64,
            "sorry_launderings": [],
            "nonstandard_axioms": [],
        },
        "typed_exports": typed_exports,
    }


def _case() -> dict:
    bindings = prior.build_validation_lineage_bindings(
        problem_id=PROBLEM,
        problem_pdf_sha256=PDF_SHA,
        shared_context_sha256=prior._hash(SHARED),
        producer_bundle_sha256=PRODUCER_BUNDLE_SHA,
        consumer_bundle_sha256=CONSUMER_BUNDLE_SHA,
        producer_inventory_sha256="4" * 64,
        consumer_inventory_sha256="5" * 64,
    )
    row = {
        "id": A6,
        "problem_id": PROBLEM,
        "official_answer_seen": False,
        "shared_context": SHARED,
        "problem_assets": [{
            "kind": "problem_pdf",
            "path": "theory_problem.pdf",
            "sha256": PDF_SHA,
        }],
        "previous_parts": [
            {"source_id": A4, "part_id": "T1-A4", "question": "A4"},
            {"source_id": A5, "part_id": "T1-A5", "question": "A5"},
        ],
        "requested_outputs": [{"id": "stone_formula"}],
    }
    return {
        "consumer_target": f"IChO2026Problems/problem_{A6}.lean",
        "consumer_source_record": row,
        "consumer_source_record_sha256": prior._hash(row),
        "consumer_controller_binding": bindings["consumer"],
        "producer_snapshots": [
            _producer(A4, [], bindings["producer"], marker="a"),
            _producer(A5, [A4], bindings["producer"], marker="b"),
        ],
    }


def _build(case: dict) -> dict:
    return prior.build_prior_result_dependency_context(**case)


def test_builds_one_exact_a4_a5_receipt_for_a6() -> None:
    case = _case()
    receipt = _build(case)

    assert receipt["complete"] is True
    assert receipt["lineage"]["producer_bundle_sha256"] == PRODUCER_BUNDLE_SHA
    assert receipt["lineage"]["consumer_bundle_sha256"] == CONSUMER_BUNDLE_SHA
    assert [item["source_id"] for item in receipt["producers"]] == [A4, A5]
    assert prior.validate_prior_result_dependency_context_self(receipt) == ""
    assert prior.validate_prior_result_dependency_context(receipt, **case) == ""
    assert prior.canonical_prior_result_value_sha256(
        case["consumer_source_record"]
    ) == case["consumer_source_record_sha256"]

    prompt = prior.render_prior_result_dependency_prompt(receipt)
    assert "certified_prior_result.producers[i].typed_exports[j]" in prompt
    assert f"certified_prior_result:{A4}:metal_q_identity" in prompt


@pytest.mark.parametrize(
    ("path", "value"),
    [
        (("source_record_sha256",), "0" * 64),
        (("answer_submission_sha256",), "0" * 64),
        (("module_sha256",), "0" * 64),
        (("formalization_review", "candidate_sha256"), "0" * 64),
        (("formalization_review", "certificate_sha256"), "0" * 64),
        (("formalization_review", "source_contract_sha256"), "0" * 64),
        (("proof_review", "candidate_sha256"), "0" * 64),
        (("proof_review", "certificate_sha256"), "0" * 64),
        (("proof_review", "source_contract_sha256"), "0" * 64),
        (("compile_audit", "audit_sha256"), "0" * 64),
        (("axiom_audit", "audit_sha256"), "0" * 64),
        (("typed_exports", 0, "expected_type_sha256"), "0" * 64),
        (("typed_exports", 0, "result_payload_sha256"), "0" * 64),
    ],
)
def test_every_bound_producer_hash_is_freshness_checked(
    path: tuple[object, ...], value: object,
) -> None:
    original = _case()
    receipt = _build(original)
    current = deepcopy(original)
    cursor: object = current["producer_snapshots"][0]
    for key in path[:-1]:
        cursor = cursor[key]  # type: ignore[index]
    cursor[path[-1]] = value  # type: ignore[index]

    assert prior.validate_prior_result_dependency_context(
        receipt, **current
    )


@pytest.mark.parametrize("producer_index", [0, 1])
@pytest.mark.parametrize("mutation", ["missing", "extra", "duplicate"])
def test_each_producer_requires_its_exact_unique_typed_outputs(
    producer_index: int,
    mutation: str,
) -> None:
    case = _case()
    producer = case["producer_snapshots"][producer_index]
    exports = producer["typed_exports"]

    if mutation == "missing":
        exports.pop()
    elif mutation == "extra":
        extra = deepcopy(exports[-1])
        output_id = "unexpected_output"
        extra["export_id"] = (
            f"certified_prior_result:{producer['source_id']}:{output_id}"
        )
        extra["result_payload"]["output_id"] = output_id
        extra["result_payload_sha256"] = prior._hash(extra["result_payload"])
        exports.append(extra)
    else:
        exports[-1] = deepcopy(exports[0])

    assert _build(case) == {}


@pytest.mark.parametrize(
    "mutation",
    [
        lambda item: item["formalization_review"].update(status="failed"),
        lambda item: item["proof_review"].update(status="retry"),
        lambda item: item["compile_audit"].update(returncode=1),
        lambda item: item["compile_audit"].update(sorry_count=1),
        lambda item: item["axiom_audit"]["sorry_launderings"].append(
            {"declaration": "bad"}
        ),
        lambda item: item["axiom_audit"]["nonstandard_axioms"].append(
            {"axiom": "bad"}
        ),
        lambda item: item.update(official_answer_seen=True),
    ],
)
def test_non_green_or_answer_seen_producer_fails_closed(mutation) -> None:
    case = _case()
    mutation(case["producer_snapshots"][0])
    assert _build(case) == {}


def test_unrelated_lineage_and_projection_bundles_are_rejected() -> None:
    case = _case()
    unrelated = prior.build_validation_lineage_bindings(
        problem_id=PROBLEM,
        problem_pdf_sha256="8" * 64,
        shared_context_sha256=prior._hash(SHARED),
        producer_bundle_sha256=PRODUCER_BUNDLE_SHA,
        consumer_bundle_sha256=CONSUMER_BUNDLE_SHA,
        producer_inventory_sha256="4" * 64,
        consumer_inventory_sha256="5" * 64,
    )
    case["producer_snapshots"][0]["controller_binding"] = unrelated["producer"]
    assert _build(case) == {}

    case = _case()
    case["producer_snapshots"][0]["formalization_review"][
        "source_bundle_sha256"
    ] = CONSUMER_BUNDLE_SHA
    assert _build(case) == {}


def test_only_ordered_a4_a5_and_acyclic_prior_edges_are_admitted() -> None:
    case = _case()
    case["consumer_source_record"]["previous_parts"].reverse()
    case["consumer_source_record_sha256"] = prior._hash(
        case["consumer_source_record"]
    )
    assert _build(case) == {}

    case = _case()
    producer = case["producer_snapshots"][0]
    producer["previous_part_source_ids"] = [A5]
    producer["previous_part_source_ids_sha256"] = prior._hash([A5])
    assert _build(case) == {}

    case = _case()
    case["producer_snapshots"].pop()
    assert _build(case) == {}


def test_source_record_pdf_shared_context_and_blindness_are_bound() -> None:
    for mutate in (
        lambda row: row.update(shared_context="changed"),
        lambda row: row["problem_assets"][0].update(sha256="0" * 64),
        lambda row: row.update(answer="official leak"),
        lambda row: row.update(official_answer_seen=True),
    ):
        case = _case()
        mutate(case["consumer_source_record"])
        case["consumer_source_record_sha256"] = prior._hash(
            case["consumer_source_record"]
        )
        assert _build(case) == {}


def test_self_hash_detects_tamper_and_full_validation_rejects_rehash() -> None:
    case = _case()
    receipt = _build(case)
    tampered = deepcopy(receipt)
    export = tampered["producers"][0]["typed_exports"][0]
    export["result_payload"]["raw_value"] = "forged"
    export["result_payload_sha256"] = prior._hash(export["result_payload"])

    assert prior.validate_prior_result_dependency_context_self(tampered)

    unsigned = dict(tampered)
    unsigned.pop("receipt_sha256")
    tampered["receipt_sha256"] = prior._hash(unsigned)
    assert prior.validate_prior_result_dependency_context_self(tampered) == ""
    assert prior.validate_prior_result_dependency_context(tampered, **case)


def test_loader_accepts_only_controller_owned_readonly_receipt(
    tmp_path,
) -> None:
    case = _case()
    receipt = _build(case)
    relative = prior.prior_result_dependency_relative_path(A6)
    path = tmp_path / relative
    path.parent.mkdir(parents=True)
    path.write_text(json.dumps(receipt), encoding="utf-8")
    path.chmod(0o444)

    assert prior.load_prior_result_dependency_context(tmp_path, A6) == receipt
    assert prior.load_prior_result_dependency_context_checked(
        tmp_path, A6
    ) == (receipt, "")

    root_mode = tmp_path.stat().st_mode & 0o777
    tmp_path.chmod(root_mode | 0o022)
    loaded, reason = prior.load_prior_result_dependency_context_checked(
        tmp_path, A6
    )
    assert loaded == {}
    assert reason == "unsafe_project_root"
    tmp_path.chmod(root_mode)

    path.chmod(0o644)
    loaded, reason = prior.load_prior_result_dependency_context_checked(
        tmp_path, A6
    )
    assert loaded == {}
    assert reason == "unsafe_receipt_file"
    path.chmod(0o444)

    path.parent.chmod(0o777)
    assert prior.load_prior_result_dependency_context(tmp_path, A6) == {}
    path.parent.chmod(0o755)
    assert prior.load_prior_result_dependency_context(
        tmp_path, A6, controller_uid=path.stat().st_uid + 1
    ) == {}

    path.unlink()
    outside = tmp_path / "outside.json"
    outside.write_text(json.dumps(receipt), encoding="utf-8")
    path.symlink_to(outside)
    assert prior.load_prior_result_dependency_context(tmp_path, A6) == {}
