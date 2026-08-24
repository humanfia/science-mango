"""Build a reviewed, content-pinned chemistry-rule registry offline.

The builder deliberately performs no file, environment, process, or network
I/O.  A trusted outer workflow downloads a source and passes its bytes here;
this module validates a small JSON-shaped request, pins those bytes, and emits
hash-bound records and a deterministic manifest.

Records are generic evidence rules.  They cannot carry problem targets,
questions, official answers, or recognizable problem identifiers, and they
never authorize automatic instantiation in a problem.
"""

from __future__ import annotations

from copy import deepcopy
from datetime import datetime
import hashlib
import json
import re
from typing import Mapping


SCHEMA_VERSION = 1
RECORD_TYPE = "trusted_chemistry_rule"
MANIFEST_TYPE = "trusted_chemistry_registry"

_SHA256_RE = re.compile(r"[0-9a-f]{64}")
_RULE_ID_RE = re.compile(r"[a-z][a-z0-9_]{2,95}")
_REVIEWER_ID_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:@/-]{1,127}")
_DOI_RE = re.compile(r"10\.\d{4,9}/[-._;()/:A-Z0-9]+", re.IGNORECASE)
_UTC_TIMESTAMP_RE = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z")
_OBVIOUS_PROBLEM_ID_RE = re.compile(
    r"(?<![A-Za-z0-9])(?:T|Q)\d{1,3}[-_ ]?A\d{1,3}(?![A-Za-z0-9])"
    r"|(?<![A-Za-z0-9])(?:problem|question|task)[-_ #]*\d+"
    r"(?:[-_. ]+[A-Za-z0-9]+)*(?![A-Za-z0-9])",
    re.IGNORECASE,
)
_ANSWER_LABEL_RE = re.compile(r"official[-_ ]?answer|answer[-_ ]?key", re.IGNORECASE)

_ALLOWED_AUTHORITY_KINDS = frozenset(
    {
        "authoritative_reference",
        "contest_semantics_policy",
        "peer_reviewed_literature",
    }
)
_FORBIDDEN_FIELD_NAMES = frozenset(
    {
        "answer_key",
        "candidate_answer",
        "expected_answer",
        "official_answer",
        "official_answers",
        "problem",
        "problem_id",
        "question",
        "question_id",
        "target",
        "target_id",
    }
)

_REQUEST_FIELDS = frozenset({"schema_version", "rule", "source", "review"})
_RULE_FIELDS = frozenset(
    {
        "rule_id",
        "rule_version",
        "authority_kind",
        "claim",
        "applicability_conditions",
        "exclusions",
        "automatic_problem_instantiation",
    }
)
_SOURCE_FIELDS = frozenset({"url", "doi", "locator"})
_REVIEW_FIELDS = frozenset(
    {"status", "reviewer_id", "approved_at", "approval_scope"}
)


class TrustedChemistryRegistryError(ValueError):
    """A registry request is invalid, unapproved, unsafe, or conflicting."""


def canonical_json_bytes(value: object) -> bytes:
    """Return the repository's deterministic UTF-8 JSON representation."""

    try:
        return json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise TrustedChemistryRegistryError("value is not canonical JSON data") from exc


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _require_sha256(name: str, value: object) -> str:
    if type(value) is not str or _SHA256_RE.fullmatch(value) is None:
        raise TrustedChemistryRegistryError(
            f"{name} must be a lowercase 64-character SHA-256 digest"
        )
    return value


def _normal_field_name(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.casefold()).strip("_")


def _reject_forbidden_content(value: object, path: str = "request") -> None:
    if isinstance(value, Mapping):
        for key, child in value.items():
            if type(key) is not str:
                raise TrustedChemistryRegistryError(f"{path} has a non-string field")
            if _normal_field_name(key) in _FORBIDDEN_FIELD_NAMES:
                raise TrustedChemistryRegistryError(
                    f"{path}.{key} is forbidden in a generic registry record"
                )
            _reject_forbidden_content(child, f"{path}.{key}")
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _reject_forbidden_content(child, f"{path}[{index}]")
        return
    if type(value) is str and (
        _OBVIOUS_PROBLEM_ID_RE.search(value) is not None
        or _ANSWER_LABEL_RE.search(value) is not None
    ):
        raise TrustedChemistryRegistryError(
            f"{path} contains a problem identifier or answer label"
        )


def _require_exact_mapping(
    name: str, value: object, expected_fields: frozenset[str]
) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TrustedChemistryRegistryError(f"{name} must be an object")
    if any(type(key) is not str for key in value):
        raise TrustedChemistryRegistryError(f"{name} has a non-string field")
    fields = frozenset(value)
    if fields != expected_fields:
        missing = sorted(expected_fields - fields)
        extra = sorted(fields - expected_fields)
        raise TrustedChemistryRegistryError(
            f"{name} has the wrong fields (missing={missing}, extra={extra})"
        )
    return value


def _require_text(
    name: str, value: object, *, maximum: int, minimum: int = 1
) -> str:
    if type(value) is not str:
        raise TrustedChemistryRegistryError(f"{name} must be a string")
    if value != value.strip() or not minimum <= len(value) <= maximum:
        raise TrustedChemistryRegistryError(
            f"{name} must be {minimum}..{maximum} characters with no outer whitespace"
        )
    if any(ord(character) < 32 for character in value):
        raise TrustedChemistryRegistryError(f"{name} contains a control character")
    return value


def _require_text_list(
    name: str,
    value: object,
    *,
    allow_empty: bool,
) -> list[str]:
    if type(value) is not list:
        raise TrustedChemistryRegistryError(f"{name} must be an array")
    if len(value) > 32 or (not allow_empty and not value):
        raise TrustedChemistryRegistryError(
            f"{name} must contain {'0' if allow_empty else '1'}..32 entries"
        )
    result = [
        _require_text(f"{name}[{index}]", item, maximum=500)
        for index, item in enumerate(value)
    ]
    if len(result) != len(set(result)):
        raise TrustedChemistryRegistryError(f"{name} contains duplicate entries")
    return result


def _validate_url(value: object) -> str:
    url = _require_text("source.url", value, maximum=2048)
    if not url.startswith("https://") or any(character.isspace() for character in url):
        raise TrustedChemistryRegistryError("source.url must be an HTTPS URL")
    authority = url[len("https://") :].split("/", 1)[0]
    if (
        not authority
        or "@" in authority
        or authority.startswith(".")
        or authority.endswith(".")
    ):
        raise TrustedChemistryRegistryError("source.url has an invalid authority")
    return url


def _validate_doi(value: object) -> str | None:
    if value is None:
        return None
    doi = _require_text("source.doi", value, maximum=255)
    if _DOI_RE.fullmatch(doi) is None:
        raise TrustedChemistryRegistryError(
            "source.doi must be a bare DOI such as 10.1234/example"
        )
    return doi


def _validate_timestamp(value: object) -> str:
    approved_at = _require_text("review.approved_at", value, maximum=20)
    if _UTC_TIMESTAMP_RE.fullmatch(approved_at) is None:
        raise TrustedChemistryRegistryError(
            "review.approved_at must use UTC YYYY-MM-DDTHH:MM:SSZ"
        )
    try:
        datetime.strptime(approved_at, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError as exc:
        raise TrustedChemistryRegistryError(
            "review.approved_at is not a valid UTC timestamp"
        ) from exc
    return approved_at


def _validate_request(request: object) -> dict[str, object]:
    _reject_forbidden_content(request)
    top = _require_exact_mapping("request", request, _REQUEST_FIELDS)
    if type(top["schema_version"]) is not int or top["schema_version"] != SCHEMA_VERSION:
        raise TrustedChemistryRegistryError(
            f"request.schema_version must equal {SCHEMA_VERSION}"
        )

    raw_rule = _require_exact_mapping("rule", top["rule"], _RULE_FIELDS)
    rule_id = _require_text("rule.rule_id", raw_rule["rule_id"], maximum=96)
    if _RULE_ID_RE.fullmatch(rule_id) is None:
        raise TrustedChemistryRegistryError(
            "rule.rule_id must be stable lowercase snake_case"
        )
    rule_version = raw_rule["rule_version"]
    if type(rule_version) is not int or not 1 <= rule_version <= 1_000_000:
        raise TrustedChemistryRegistryError(
            "rule.rule_version must be an integer from 1 to 1000000"
        )
    authority_kind = raw_rule["authority_kind"]
    if type(authority_kind) is not str or authority_kind not in _ALLOWED_AUTHORITY_KINDS:
        raise TrustedChemistryRegistryError(
            "rule.authority_kind is not an allowed evidence authority"
        )
    automatic = raw_rule["automatic_problem_instantiation"]
    if automatic is not False:
        raise TrustedChemistryRegistryError(
            "rule.automatic_problem_instantiation must be false"
        )
    rule = {
        "applicability_conditions": _require_text_list(
            "rule.applicability_conditions",
            raw_rule["applicability_conditions"],
            allow_empty=False,
        ),
        "authority_kind": authority_kind,
        "automatic_problem_instantiation": False,
        "claim": _require_text("rule.claim", raw_rule["claim"], maximum=2000),
        "exclusions": _require_text_list(
            "rule.exclusions", raw_rule["exclusions"], allow_empty=True
        ),
        "rule_id": rule_id,
        "rule_version": rule_version,
    }

    raw_source = _require_exact_mapping("source", top["source"], _SOURCE_FIELDS)
    source = {
        "doi": _validate_doi(raw_source["doi"]),
        "locator": _require_text(
            "source.locator", raw_source["locator"], maximum=500
        ),
        "url": _validate_url(raw_source["url"]),
    }

    raw_review = _require_exact_mapping("review", top["review"], _REVIEW_FIELDS)
    if raw_review["status"] != "approved":
        raise TrustedChemistryRegistryError("review.status must be approved")
    if raw_review["approval_scope"] != "rule_and_source":
        raise TrustedChemistryRegistryError(
            "review.approval_scope must be rule_and_source"
        )
    reviewer_id = _require_text(
        "review.reviewer_id", raw_review["reviewer_id"], maximum=128, minimum=2
    )
    if _REVIEWER_ID_RE.fullmatch(reviewer_id) is None:
        raise TrustedChemistryRegistryError("review.reviewer_id is invalid")
    review = {
        "approval_scope": "rule_and_source",
        "approved_at": _validate_timestamp(raw_review["approved_at"]),
        "reviewer_id": reviewer_id,
        "status": "approved",
    }
    return {
        "review": review,
        "rule": rule,
        "schema_version": SCHEMA_VERSION,
        "source": source,
    }


class TrustedChemistryRegistryBuilder:
    """Accumulate validated rule records and expose a canonical manifest."""

    def __init__(self, *, base_dataset_sha256: str) -> None:
        self._base_dataset_sha256 = _require_sha256(
            "base_dataset_sha256", base_dataset_sha256
        )
        self._records: dict[str, dict[str, object]] = {}

    @property
    def base_dataset_sha256(self) -> str:
        return self._base_dataset_sha256

    def __len__(self) -> int:
        return len(self._records)

    def pin(self, request: object, *, source_bytes: bytes) -> dict[str, object]:
        """Pin one already-downloaded source and return its immutable record copy."""

        if type(source_bytes) is not bytes or not source_bytes:
            raise TrustedChemistryRegistryError(
                "source_bytes must be a non-empty bytes object"
            )
        validated = _validate_request(request)
        source = dict(validated["source"])  # type: ignore[arg-type]
        source["content_sha256"] = _sha256(source_bytes)
        unsigned: dict[str, object] = {
            "base_dataset_sha256": self._base_dataset_sha256,
            "record_type": RECORD_TYPE,
            "review": validated["review"],
            "rule": validated["rule"],
            "runtime_network_access": False,
            "schema_version": SCHEMA_VERSION,
            "source": source,
        }
        record = dict(unsigned)
        record["record_sha256"] = _sha256(canonical_json_bytes(unsigned))

        rule = validated["rule"]
        assert isinstance(rule, Mapping)
        rule_id = rule["rule_id"]
        assert isinstance(rule_id, str)
        previous = self._records.get(rule_id)
        if previous is not None:
            if previous != record:
                raise TrustedChemistryRegistryError(
                    f"conflicting record for existing rule_id {rule_id!r}"
                )
            return deepcopy(previous)
        self._records[rule_id] = deepcopy(record)
        return deepcopy(record)

    def get(self, rule_id: str) -> dict[str, object]:
        """Return a copy of a pinned record, failing closed if it is absent."""

        if type(rule_id) is not str or _RULE_ID_RE.fullmatch(rule_id) is None:
            raise TrustedChemistryRegistryError("invalid rule_id")
        try:
            return deepcopy(self._records[rule_id])
        except KeyError as exc:
            raise TrustedChemistryRegistryError(
                f"unregistered rule_id {rule_id!r}"
            ) from exc

    def manifest(self) -> dict[str, object]:
        """Return the sorted, hash-bound manifest for the current records."""

        entries: list[dict[str, object]] = []
        for rule_id in sorted(self._records):
            record = self._records[rule_id]
            rule = record["rule"]
            assert isinstance(rule, Mapping)
            entries.append(
                {
                    "record_sha256": record["record_sha256"],
                    "rule_id": rule_id,
                    "rule_version": rule["rule_version"],
                }
            )
        unsigned: dict[str, object] = {
            "base_dataset_sha256": self._base_dataset_sha256,
            "manifest_type": MANIFEST_TYPE,
            "record_count": len(entries),
            "records": entries,
            "schema_version": SCHEMA_VERSION,
        }
        manifest = dict(unsigned)
        manifest["manifest_sha256"] = _sha256(canonical_json_bytes(unsigned))
        return manifest

    def snapshot(self) -> dict[str, object]:
        """Return a self-contained manifest plus sorted record copies."""

        return {
            "manifest": self.manifest(),
            "records": [deepcopy(self._records[key]) for key in sorted(self._records)],
        }
