from __future__ import annotations

import ast
from copy import deepcopy
import hashlib
import json
from pathlib import Path

import pytest

from archon.commands import trusted_chemistry_registry as registry


BASE_DATASET_SHA256 = hashlib.sha256(b"base chemistry dataset").hexdigest()
SOURCE_BYTES = b"%PDF-1.7\nreviewed chemistry source bytes\n%%EOF\n"


def _request(
    rule_id: str = "aqueous_feiii_phenol_colour_test",
) -> dict[str, object]:
    return {
        "schema_version": 1,
        "rule": {
            "rule_id": rule_id,
            "rule_version": 1,
            "authority_kind": "peer_reviewed_literature",
            "claim": (
                "Under the stated aqueous test conditions, an observed "
                "characteristic ferric-ion colour is evidence for a phenolic "
                "hydroxy group."
            ),
            "applicability_conditions": [
                "The sample is tested in aqueous solution with ferric ions.",
                "The reported observation is the source-defined characteristic colour.",
            ],
            "exclusions": [
                "Other ferric-ion-binding functional groups have not been excluded."
            ],
            "automatic_problem_instantiation": False,
        },
        "source": {
            "url": "https://doi.org/10.1000/example.2026.1",
            "doi": "10.1000/example.2026.1",
            "locator": "Section 2.3, qualitative tests, pp. 14-15",
        },
        "review": {
            "status": "approved",
            "reviewer_id": "chem-reviewer-02",
            "approved_at": "2026-08-24T10:30:00Z",
            "approval_scope": "rule_and_source",
        },
    }


def _canonical(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def test_pin_builds_content_record_and_manifest_hashes_offline() -> None:
    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )

    record = builder.pin(_request(), source_bytes=SOURCE_BYTES)

    assert record["schema_version"] == registry.SCHEMA_VERSION
    assert record["record_type"] == registry.RECORD_TYPE
    assert record["base_dataset_sha256"] == BASE_DATASET_SHA256
    assert record["runtime_network_access"] is False
    assert record["source"] == {
        "content_sha256": hashlib.sha256(SOURCE_BYTES).hexdigest(),
        "doi": "10.1000/example.2026.1",
        "locator": "Section 2.3, qualitative tests, pp. 14-15",
        "url": "https://doi.org/10.1000/example.2026.1",
    }
    unsigned_record = dict(record)
    del unsigned_record["record_sha256"]
    assert record["record_sha256"] == hashlib.sha256(
        _canonical(unsigned_record)
    ).hexdigest()

    manifest = builder.manifest()
    assert manifest["base_dataset_sha256"] == BASE_DATASET_SHA256
    assert manifest["record_count"] == 1
    assert manifest["records"] == [
        {
            "record_sha256": record["record_sha256"],
            "rule_id": "aqueous_feiii_phenol_colour_test",
            "rule_version": 1,
        }
    ]
    unsigned_manifest = dict(manifest)
    del unsigned_manifest["manifest_sha256"]
    assert manifest["manifest_sha256"] == hashlib.sha256(
        _canonical(unsigned_manifest)
    ).hexdigest()


def test_canonical_json_and_hashes_ignore_mapping_insertion_order() -> None:
    first_request = _request()
    second_request = {
        "review": dict(reversed(list(first_request["review"].items()))),  # type: ignore[union-attr]
        "source": dict(reversed(list(first_request["source"].items()))),  # type: ignore[union-attr]
        "rule": dict(reversed(list(first_request["rule"].items()))),  # type: ignore[union-attr]
        "schema_version": 1,
    }
    first = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    second = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )

    first_record = first.pin(first_request, source_bytes=SOURCE_BYTES)
    second_record = second.pin(second_request, source_bytes=SOURCE_BYTES)

    assert first_record == second_record
    assert first.manifest() == second.manifest()
    assert registry.canonical_json_bytes(first.snapshot()) == _canonical(
        second.snapshot()
    )


def test_same_record_is_idempotent_and_returned_values_are_copies() -> None:
    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    first = builder.pin(_request(), source_bytes=SOURCE_BYTES)
    first_manifest = builder.manifest()

    first["rule"] = {"claim": "caller mutation"}
    first_manifest["records"] = []
    second = builder.pin(_request(), source_bytes=SOURCE_BYTES)

    assert len(builder) == 1
    assert second["rule"] == _request()["rule"]
    assert builder.get("aqueous_feiii_phenol_colour_test") == second
    assert builder.manifest()["record_count"] == 1
    assert builder.manifest()["records"] != []


@pytest.mark.parametrize("change", ["claim", "source", "review", "bytes"])
def test_same_rule_id_with_different_record_fails_closed_without_mutation(
    change: str,
) -> None:
    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    original = builder.pin(_request(), source_bytes=SOURCE_BYTES)
    original_manifest = builder.manifest()
    conflicting = _request()
    conflicting_bytes = SOURCE_BYTES
    if change == "claim":
        conflicting["rule"]["claim"] = "A materially different generic claim."  # type: ignore[index]
    elif change == "source":
        conflicting["source"]["locator"] = "Section 7"  # type: ignore[index]
    elif change == "review":
        conflicting["review"]["reviewer_id"] = "chem-reviewer-03"  # type: ignore[index]
    else:
        conflicting_bytes = SOURCE_BYTES + b"changed"

    with pytest.raises(
        registry.TrustedChemistryRegistryError, match="conflicting record"
    ):
        builder.pin(conflicting, source_bytes=conflicting_bytes)

    assert len(builder) == 1
    assert builder.get("aqueous_feiii_phenol_colour_test") == original
    assert builder.manifest() == original_manifest


def test_manifest_is_stable_and_sorted_independent_of_pin_order() -> None:
    alpha = _request("alpha_generic_chemistry_rule")
    zeta = _request("zeta_generic_chemistry_rule")
    builders = [
        registry.TrustedChemistryRegistryBuilder(
            base_dataset_sha256=BASE_DATASET_SHA256
        ),
        registry.TrustedChemistryRegistryBuilder(
            base_dataset_sha256=BASE_DATASET_SHA256
        ),
    ]
    builders[0].pin(zeta, source_bytes=SOURCE_BYTES + b"zeta")
    builders[0].pin(alpha, source_bytes=SOURCE_BYTES + b"alpha")
    builders[1].pin(alpha, source_bytes=SOURCE_BYTES + b"alpha")
    builders[1].pin(zeta, source_bytes=SOURCE_BYTES + b"zeta")

    assert builders[0].snapshot() == builders[1].snapshot()
    assert [
        entry["rule_id"] for entry in builders[0].manifest()["records"]
    ] == ["alpha_generic_chemistry_rule", "zeta_generic_chemistry_rule"]


def test_base_dataset_digest_is_bound_into_records_and_manifest() -> None:
    other_base = hashlib.sha256(b"other base dataset").hexdigest()
    first = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    second = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=other_base
    )

    first_record = first.pin(_request(), source_bytes=SOURCE_BYTES)
    second_record = second.pin(_request(), source_bytes=SOURCE_BYTES)

    assert first_record["record_sha256"] != second_record["record_sha256"]
    assert first.manifest()["manifest_sha256"] != second.manifest()[
        "manifest_sha256"
    ]


@pytest.mark.parametrize(
    "bad_digest",
    ["", "0" * 63, "0" * 65, "G" * 64, "A" * 64, None, True],
)
def test_base_dataset_digest_has_strict_sha256_schema(bad_digest: object) -> None:
    with pytest.raises(registry.TrustedChemistryRegistryError):
        registry.TrustedChemistryRegistryBuilder(  # type: ignore[arg-type]
            base_dataset_sha256=bad_digest
        )


@pytest.mark.parametrize(
    "mutation",
    [
        "extra_top_field",
        "missing_top_field",
        "extra_rule_field",
        "missing_rule_field",
        "source_declares_digest",
        "extra_review_field",
        "wrong_schema_type",
        "wrong_schema_version",
        "wrong_rule_version_type",
        "unknown_authority",
        "tuple_conditions",
        "empty_conditions",
        "duplicate_exclusions",
        "automatic_instantiation",
        "insecure_url",
        "url_credentials",
        "bad_doi",
        "empty_locator",
        "pending_review",
        "wrong_review_scope",
        "bad_reviewer",
        "bad_timestamp",
    ],
)
def test_pin_request_uses_an_exact_fail_closed_schema(mutation: str) -> None:
    request = _request()
    if mutation == "extra_top_field":
        request["notes"] = "not in schema"
    elif mutation == "missing_top_field":
        del request["review"]
    elif mutation == "extra_rule_field":
        request["rule"]["derivation"] = "not in schema"  # type: ignore[index]
    elif mutation == "missing_rule_field":
        del request["rule"]["claim"]  # type: ignore[index]
    elif mutation == "source_declares_digest":
        request["source"]["content_sha256"] = "0" * 64  # type: ignore[index]
    elif mutation == "extra_review_field":
        request["review"]["comment"] = "not in schema"  # type: ignore[index]
    elif mutation == "wrong_schema_type":
        request["schema_version"] = True
    elif mutation == "wrong_schema_version":
        request["schema_version"] = 2
    elif mutation == "wrong_rule_version_type":
        request["rule"]["rule_version"] = True  # type: ignore[index]
    elif mutation == "unknown_authority":
        request["rule"]["authority_kind"] = "web_search"  # type: ignore[index]
    elif mutation == "tuple_conditions":
        request["rule"]["applicability_conditions"] = ("condition",)  # type: ignore[index]
    elif mutation == "empty_conditions":
        request["rule"]["applicability_conditions"] = []  # type: ignore[index]
    elif mutation == "duplicate_exclusions":
        request["rule"]["exclusions"] = ["same", "same"]  # type: ignore[index]
    elif mutation == "automatic_instantiation":
        request["rule"]["automatic_problem_instantiation"] = True  # type: ignore[index]
    elif mutation == "insecure_url":
        request["source"]["url"] = "http://example.test/source.pdf"  # type: ignore[index]
    elif mutation == "url_credentials":
        request["source"]["url"] = "https://user@example.test/source.pdf"  # type: ignore[index]
    elif mutation == "bad_doi":
        request["source"]["doi"] = "https://doi.org/10.1000/example"  # type: ignore[index]
    elif mutation == "empty_locator":
        request["source"]["locator"] = ""  # type: ignore[index]
    elif mutation == "pending_review":
        request["review"]["status"] = "pending"  # type: ignore[index]
    elif mutation == "wrong_review_scope":
        request["review"]["approval_scope"] = "rule_only"  # type: ignore[index]
    elif mutation == "bad_reviewer":
        request["review"]["reviewer_id"] = "reviewer with spaces"  # type: ignore[index]
    else:
        request["review"]["approved_at"] = "2026-02-30T10:30:00Z"  # type: ignore[index]

    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    with pytest.raises(registry.TrustedChemistryRegistryError):
        builder.pin(request, source_bytes=SOURCE_BYTES)
    assert len(builder) == 0


@pytest.mark.parametrize(
    ("path", "value"),
    [
        (("question",), "general chemistry"),
        (("target",), "phenol"),
        (("official_answer",), "anything"),
        (("rule", "rule_id"), "generic_rule_t1_a3"),
        (("rule", "claim"), "This is for IChO-2026-T1-A3."),
        (("source", "locator"), "question 12, part b"),
        (("review", "reviewer_id"), "official-answer"),
    ],
)
def test_problem_fields_identifiers_and_answer_labels_are_forbidden(
    path: tuple[str, ...], value: str
) -> None:
    request = _request()
    cursor: dict[str, object] = request
    for component in path[:-1]:
        cursor = cursor[component]  # type: ignore[assignment]
    cursor[path[-1]] = value

    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    with pytest.raises(registry.TrustedChemistryRegistryError):
        builder.pin(request, source_bytes=SOURCE_BYTES)


def test_optional_doi_allows_an_authoritative_non_journal_source() -> None:
    request = _request("authoritative_non_journal_reference")
    request["rule"]["authority_kind"] = "authoritative_reference"  # type: ignore[index]
    request["source"]["doi"] = None  # type: ignore[index]
    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )

    record = builder.pin(request, source_bytes=SOURCE_BYTES)

    assert record["source"]["doi"] is None  # type: ignore[index]


@pytest.mark.parametrize("source_bytes", [b"", bytearray(b"bytes"), "bytes", None])
def test_source_must_be_nonempty_already_downloaded_bytes(
    source_bytes: object,
) -> None:
    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    with pytest.raises(registry.TrustedChemistryRegistryError):
        builder.pin(_request(), source_bytes=source_bytes)  # type: ignore[arg-type]
    assert len(builder) == 0


def test_unknown_rule_lookup_fails_closed() -> None:
    builder = registry.TrustedChemistryRegistryBuilder(
        base_dataset_sha256=BASE_DATASET_SHA256
    )
    with pytest.raises(registry.TrustedChemistryRegistryError, match="unregistered"):
        builder.get("unknown_generic_rule")


def test_module_has_no_file_environment_process_or_network_capability() -> None:
    source = Path(registry.__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    imported_roots: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported_roots.update(alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported_roots.add(node.module.split(".", 1)[0])
    assert imported_roots.isdisjoint(
        {
            "aiohttp",
            "ftplib",
            "http",
            "os",
            "pathlib",
            "requests",
            "socket",
            "subprocess",
            "urllib",
        }
    )
    called_names = {
        node.func.id
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    assert called_names.isdisjoint({"open", "exec", "eval", "compile"})
