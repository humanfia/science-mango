"""Deterministic reporting-policy checks for native answer-blind chemistry.

The semantic Review agent can judge whether a Lean carrier represents the
quantity requested by a problem.  It must not, however, be trusted to choose
the last displayed place.  This module reads the predeclared policy from the
problem-only bundle, computes the only admissible reporting quantum, and
builds a Lean probe that checks an exact ``ReportsAtQuantum`` declaration.

The certificate audit is deliberately narrow.  Complete marker absence is recorded
as optional audit evidence; once any marker is present, parsing, policy matching,
and the generated Lean probe remain fail-closed.  It activates only for the
``chemistry-native`` profile and an ``answer_blind`` bundle row.  Other Archon
projects retain their existing Review behaviour.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping

from archon.commands.tooling.domain_profile import load_domain_profile


CERTIFICATE_MARKER = "archon:numeric-reporting-certificate"
CERTIFICATE_SCHEMA_VERSION = 1
NUMERIC_REPORTING_OPTIONAL_AUDIT_STATUS = "optional_audit"
NUMERIC_REPORTING_MARKERS_ABSENT_REASON = (
    "numeric reporting certificate markers are absent; marker evidence is an "
    "optional audit when the original Lean target compiles"
)

_CERTIFICATE_RE = re.compile(
    rf"^\s*--\s*{re.escape(CERTIFICATE_MARKER)}\s+(?P<payload>\{{.*\}})\s*$"
)
_IDENTIFIER_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
_OUTPUT_ID_RE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]{0,127}$")
_DECIMAL_RE = re.compile(
    r"^-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?$"
)
_RATIONAL_RE = re.compile(
    r"^(?P<numerator>-?(?:0|[1-9][0-9]*))/(?P<denominator>[1-9][0-9]*)$"
)
_CERTIFICATE_FIELDS = {
    "schema_version",
    "output_id",
    "reporting_policy_kind",
    "reporting_policy_digits",
    "reported_value",
    "reporting_quantum",
    "raw_declaration",
    "reporting_declaration",
}
MAX_NUMERIC_REPORTING_REASON_LENGTH = 4096
MAX_NUMERIC_REPORTING_CERTIFICATE_BYTES = 4096
_MAX_NUMBER_LENGTH = 256
_MAX_COEFFICIENT_DIGITS = 192
_MAX_EXPONENT_ABS = 1000
_MAX_POLICY_DIGITS = 100


class NumericReportingGuardError(ValueError):
    """A problem-only reporting contract cannot be certified mechanically."""


@dataclass(frozen=True)
class NumericReportingCertificate:
    output_id: str
    reporting_policy_kind: str
    reporting_policy_digits: int
    reported_value: Fraction
    reporting_quantum: Fraction
    raw_declaration: str
    reporting_declaration: str


@dataclass(frozen=True)
class NumericReportingGuard:
    active: bool
    status: str
    reason: str
    numeric_outputs: int = 0
    lean_source_sha256: str = ""
    bundle_sha256: str = ""
    certificates: tuple[NumericReportingCertificate, ...] = ()
    probe_suffix: str = ""

    def evidence(self) -> dict[str, Any]:
        """Return JSON-safe Review evidence without trusting model output."""
        result = asdict(self)
        result.pop("probe_suffix", None)
        result["certificates"] = [
            {
                **asdict(item),
                "reported_value": _fraction_text(item.reported_value),
                "reporting_quantum": _fraction_text(item.reporting_quantum),
            }
            for item in self.certificates
        ]
        return result


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _lean_real(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℝ)"
    return f"(({value.numerator} : ℝ) / {value.denominator})"


def _strict_json_object(payload: str) -> dict[str, Any]:
    duplicate = ""

    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        nonlocal duplicate
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result and not duplicate:
                duplicate = key
            result[key] = value
        return result

    try:
        value = json.loads(payload, object_pairs_hook=pairs_hook)
    except json.JSONDecodeError as exc:
        raise NumericReportingGuardError(
            f"numeric reporting certificate is invalid JSON: {exc.msg}"
        ) from exc
    if duplicate:
        raise NumericReportingGuardError(
            f"numeric reporting certificate repeats field {duplicate!r}"
        )
    if not isinstance(value, dict):
        raise NumericReportingGuardError(
            "numeric reporting certificate must be a JSON object"
        )
    return value


def parse_exact_fraction(value: object, *, field: str) -> Fraction:
    """Parse a bounded canonical decimal or reduced rational JSON string."""
    if (
        isinstance(value, bool)
        or not isinstance(value, str)
        or not value
        or value != value.strip()
        or len(value) > _MAX_NUMBER_LENGTH
    ):
        raise NumericReportingGuardError(
            f"{field} must be a bounded exact decimal or reduced rational string"
        )
    rational = _RATIONAL_RE.fullmatch(value)
    if rational:
        numerator_text = rational.group("numerator")
        denominator_text = rational.group("denominator")
        if max(
            len(numerator_text.lstrip("-")), len(denominator_text)
        ) > _MAX_COEFFICIENT_DIGITS:
            raise NumericReportingGuardError(f"{field} coefficient is too large")
        numerator = int(numerator_text)
        denominator = int(denominator_text)
        parsed = Fraction(numerator, denominator)
        if parsed.numerator != numerator or parsed.denominator != denominator:
            raise NumericReportingGuardError(
                f"{field} rational must be reduced and canonical"
            )
        return parsed
    if not _DECIMAL_RE.fullmatch(value):
        raise NumericReportingGuardError(
            f"{field} must be a canonical decimal or reduced rational"
        )
    mantissa, separator, exponent_text = value.lower().partition("e")
    coefficient_digits = sum(character.isdigit() for character in mantissa)
    if coefficient_digits > _MAX_COEFFICIENT_DIGITS:
        raise NumericReportingGuardError(f"{field} coefficient is too large")
    if separator:
        exponent = int(exponent_text)
        if abs(exponent) > _MAX_EXPONENT_ABS:
            raise NumericReportingGuardError(f"{field} exponent is too large")
    try:
        decimal = Decimal(value)
    except InvalidOperation as exc:
        raise NumericReportingGuardError(f"{field} is not finite") from exc
    if not decimal.is_finite():
        raise NumericReportingGuardError(f"{field} is not finite")
    return Fraction(decimal)


def _power_of_ten(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(10**exponent, 1)
    return Fraction(1, 10 ** (-exponent))


def _decimal_order(value: Fraction) -> int:
    """Return ``floor(log10(abs(value)))`` using integer arithmetic only."""
    magnitude = abs(value)
    if magnitude == 0:
        raise NumericReportingGuardError(
            "zero has no unambiguous significant-figure reporting quantum"
        )
    order = len(str(magnitude.numerator)) - len(str(magnitude.denominator))
    while magnitude < _power_of_ten(order):
        order -= 1
    while magnitude >= _power_of_ten(order + 1):
        order += 1
    return order


def expected_reporting_quantum(
    *, kind: object, digits: object, reported_value: Fraction,
) -> Fraction:
    """Compute the unique quantum fixed by a supported reporting policy."""
    if not isinstance(kind, str):
        raise NumericReportingGuardError("reporting policy kind must be a string")
    normalized_kind = kind.strip().lower()
    if isinstance(digits, bool) or not isinstance(digits, int):
        raise NumericReportingGuardError(
            "reporting policy digits must be an integer, not a boolean"
        )
    if digits < 0 or digits > _MAX_POLICY_DIGITS:
        raise NumericReportingGuardError("reporting policy digits are out of range")
    if normalized_kind == "decimal_places":
        return _power_of_ten(-digits)
    if normalized_kind == "significant_figures":
        if digits < 1:
            raise NumericReportingGuardError(
                "significant-figure digits must be positive"
            )
        return _power_of_ten(_decimal_order(reported_value) - digits + 1)
    raise NumericReportingGuardError(
        f"unsupported numeric reporting policy kind {normalized_kind!r}"
    )


def _safe_project_file(project_path: Path, relative_text: object) -> Path:
    if not isinstance(relative_text, str) or not relative_text.strip():
        raise NumericReportingGuardError("problem-only bundle path is missing")
    relative = Path(relative_text)
    if relative.is_absolute() or ".." in relative.parts:
        raise NumericReportingGuardError("problem-only bundle path is unsafe")
    root = project_path.resolve()
    cursor = root
    for part in relative.parts:
        if part in {"", "."}:
            continue
        cursor = cursor / part
        if cursor.is_symlink():
            raise NumericReportingGuardError(
                "problem-only bundle path may not traverse a symlink"
            )
    resolved = cursor.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise NumericReportingGuardError(
            "problem-only bundle path escapes the project"
        ) from exc
    if not resolved.is_file() or resolved.is_symlink():
        raise NumericReportingGuardError(
            "problem-only bundle is not a regular file"
        )
    return resolved


def _target_id(project_path: Path, target: Path, manifest: Mapping[str, Any]) -> str:
    try:
        rel = target.resolve().relative_to(project_path.resolve())
    except ValueError as exc:
        raise NumericReportingGuardError("numeric target escapes the project") from exc
    prefix = "problem_"
    if (
        len(rel.parts) != 2
        or rel.parts[0] != "IChO2026Problems"
        or rel.suffix != ".lean"
        or not rel.stem.startswith(prefix)
    ):
        raise NumericReportingGuardError(
            "chemistry-native target does not match the sealed target layout"
        )
    identifier = rel.stem.removeprefix(prefix)
    raw_ids = manifest.get("target_ids")
    if (
        not isinstance(raw_ids, list)
        or any(not isinstance(item, str) for item in raw_ids)
        or len(raw_ids) != len(set(raw_ids))
        or identifier not in raw_ids
    ):
        raise NumericReportingGuardError(
            "numeric target is not uniquely authorized by isolation_manifest.json"
        )
    return identifier


def _problem_row(
    project_path: Path, target: Path,
) -> tuple[dict[str, Any], str]:
    manifest_path = project_path / "isolation_manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise NumericReportingGuardError(
            "chemistry-native isolation_manifest.json is missing or invalid"
        ) from exc
    if not isinstance(manifest, dict):
        raise NumericReportingGuardError(
            "chemistry-native isolation manifest must be an object"
        )
    identifier = _target_id(project_path, target, manifest)
    bundle_record = manifest.get("blind_bundle")
    if not isinstance(bundle_record, Mapping):
        raise NumericReportingGuardError(
            "isolation manifest blind_bundle contract is missing"
        )
    bundle_path = _safe_project_file(project_path, bundle_record.get("path"))
    try:
        payload = bundle_path.read_bytes()
    except OSError as exc:
        raise NumericReportingGuardError(
            "problem-only bundle is unreadable"
        ) from exc
    digest = _sha256(payload)
    if bundle_record.get("sha256") != digest:
        raise NumericReportingGuardError(
            "problem-only bundle digest does not match the isolation manifest"
        )
    rows: dict[str, dict[str, Any]] = {}
    try:
        lines = payload.decode("utf-8").splitlines()
    except UnicodeDecodeError as exc:
        raise NumericReportingGuardError(
            "problem-only bundle is not UTF-8"
        ) from exc
    for line_number, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise NumericReportingGuardError(
                f"problem-only bundle line {line_number} is invalid JSON"
            ) from exc
        if not isinstance(row, dict):
            raise NumericReportingGuardError(
                f"problem-only bundle line {line_number} is not an object"
            )
        row_id = row.get("id")
        if not isinstance(row_id, str) or not row_id or row_id in rows:
            raise NumericReportingGuardError(
                "problem-only bundle has a missing or duplicate id"
            )
        rows[row_id] = row
    if identifier not in rows:
        raise NumericReportingGuardError(
            "authorized target is missing from the problem-only bundle"
        )
    row = rows[identifier]
    if (
        row.get("evaluation_mode") != "answer_blind"
        or row.get("official_answer_seen") is not False
    ):
        raise NumericReportingGuardError(
            "numeric reporting guard requires an answer-blind problem row"
        )
    return row, digest


def _numeric_output_policies(row: Mapping[str, Any]) -> dict[str, tuple[str, int]]:
    requested = row.get("requested_outputs")
    if not isinstance(requested, list) or not requested:
        raise NumericReportingGuardError(
            "problem row has no predeclared requested_outputs"
        )
    numeric: dict[str, tuple[str, int]] = {}
    seen: set[str] = set()
    for index, raw_output in enumerate(requested, start=1):
        if not isinstance(raw_output, Mapping):
            raise NumericReportingGuardError(
                f"requested output {index} is not an object"
            )
        output_id = raw_output.get("id")
        if (
            not isinstance(output_id, str)
            or not _OUTPUT_ID_RE.fullmatch(output_id)
            or output_id in seen
        ):
            raise NumericReportingGuardError(
                f"requested output {index} has an invalid or duplicate id"
            )
        seen.add(output_id)
        if raw_output.get("kind") != "numeric":
            continue
        policy = raw_output.get("reporting_policy")
        if not isinstance(policy, Mapping):
            raise NumericReportingGuardError(
                f"numeric requested output {output_id!r} has no reporting policy"
            )
        kind = policy.get("kind")
        digits = policy.get("digits")
        # Validate the policy independently of any reported value.  A value of
        # one avoids the intentionally ambiguous significant-figure zero case.
        expected_reporting_quantum(
            kind=kind, digits=digits, reported_value=Fraction(1),
        )
        assert isinstance(kind, str) and isinstance(digits, int)
        numeric[output_id] = (kind.strip().lower(), digits)
    if numeric:
        global_policy = row.get("reporting_policy")
        if (
            not isinstance(global_policy, Mapping)
            or global_policy.get("intermediate_rounding") != "forbidden"
            or global_policy.get("tie_rule") != "half_away_from_zero"
            or global_policy.get("raw_result_required") is not True
        ):
            raise NumericReportingGuardError(
                "problem row has an unsupported global numeric reporting policy"
            )
    return numeric


def _parse_certificates(source: str) -> tuple[dict[str, Any], ...]:
    parsed: list[dict[str, Any]] = []
    for line in source.splitlines():
        if CERTIFICATE_MARKER not in line:
            continue
        match = _CERTIFICATE_RE.fullmatch(line)
        if not match:
            raise NumericReportingGuardError(
                "numeric reporting certificate marker must occupy one Lean line"
            )
        payload = match.group("payload")
        if len(payload) > MAX_NUMERIC_REPORTING_CERTIFICATE_BYTES:
            raise NumericReportingGuardError(
                "numeric reporting certificate is too large"
            )
        parsed.append(_strict_json_object(payload))
    return tuple(parsed)


def _certificate(
    raw: Mapping[str, Any],
    expected_policies: Mapping[str, tuple[str, int]],
) -> NumericReportingCertificate:
    missing = sorted(_CERTIFICATE_FIELDS - set(raw))
    extra = sorted(set(raw) - _CERTIFICATE_FIELDS)
    if missing or extra:
        details = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        raise NumericReportingGuardError(
            "numeric reporting certificate has invalid fields: " + "; ".join(details)
        )
    schema = raw.get("schema_version")
    if type(schema) is not int or schema != CERTIFICATE_SCHEMA_VERSION:
        raise NumericReportingGuardError(
            "numeric reporting certificate has an unsupported schema_version"
        )
    output_id = raw.get("output_id")
    if not isinstance(output_id, str) or output_id not in expected_policies:
        raise NumericReportingGuardError(
            f"numeric reporting certificate output_id {output_id!r} is not requested"
        )
    expected_kind, expected_digits = expected_policies[output_id]
    kind = raw.get("reporting_policy_kind")
    digits = raw.get("reporting_policy_digits")
    if kind != expected_kind or digits != expected_digits or isinstance(digits, bool):
        raise NumericReportingGuardError(
            f"numeric reporting certificate policy does not match {output_id!r}"
        )
    reported = parse_exact_fraction(
        raw.get("reported_value"), field=f"{output_id} reported_value",
    )
    quantum = parse_exact_fraction(
        raw.get("reporting_quantum"), field=f"{output_id} reporting_quantum",
    )
    expected_quantum = expected_reporting_quantum(
        kind=kind, digits=digits, reported_value=reported,
    )
    if quantum <= 0 or quantum != expected_quantum:
        raise NumericReportingGuardError(
            f"numeric reporting quantum for {output_id!r} must be "
            f"{_fraction_text(expected_quantum)}, not {_fraction_text(quantum)}"
        )
    if (reported / quantum).denominator != 1:
        raise NumericReportingGuardError(
            f"reported value for {output_id!r} is not a multiple of its quantum"
        )
    raw_declaration = raw.get("raw_declaration")
    reporting_declaration = raw.get("reporting_declaration")
    for field, declaration in (
        ("raw_declaration", raw_declaration),
        ("reporting_declaration", reporting_declaration),
    ):
        if not isinstance(declaration, str) or not _IDENTIFIER_RE.fullmatch(declaration):
            raise NumericReportingGuardError(
                f"{output_id} {field} must be a fully qualified Lean identifier"
            )
    assert isinstance(raw_declaration, str)
    assert isinstance(reporting_declaration, str)
    return NumericReportingCertificate(
        output_id=output_id,
        reporting_policy_kind=expected_kind,
        reporting_policy_digits=expected_digits,
        reported_value=reported,
        reporting_quantum=quantum,
        raw_declaration=raw_declaration,
        reporting_declaration=reporting_declaration,
    )


def _probe_suffix(
    certificates: tuple[NumericReportingCertificate, ...],
) -> str:
    lines = [
        "",
        "/- Trusted Archon numeric-reporting probes; generated from the",
        "   problem-only reporting policy and strict certificate identifiers. -/",
    ]
    for certificate in certificates:
        lines.extend([
            f"example : IChO2026Chem.Reporting.ReportsAtQuantum",
            f"    (_root_.{certificate.raw_declaration} : ℝ)",
            f"    {_lean_real(certificate.reported_value)}",
            f"    {_lean_real(certificate.reporting_quantum)} :=",
            f"  _root_.{certificate.reporting_declaration}",
            "",
        ])
    return "\n".join(lines)


def prepare_numeric_reporting_guard(
    *, project_path: Path, target: Path, source_bytes: bytes | None = None,
) -> NumericReportingGuard:
    """Prepare a strict proof probe or record complete marker absence for audit."""
    config_path = project_path / ".archon" / "config.json"
    config_mentions_native = False
    try:
        config_text = config_path.read_text(encoding="utf-8", errors="ignore")
        config_mentions_native = "chemistry-native" in config_text
        parsed_config = json.loads(config_text)
        config_valid = isinstance(parsed_config, dict)
    except (OSError, json.JSONDecodeError):
        config_valid = False
    try:
        profile_name = load_domain_profile(project_path).name
    except Exception as exc:
        # An explicit chemistry-native declaration must never bypass its guard
        # merely because the rest of the config is malformed.  The cheap text
        # check only decides fail-closed activation; it grants no pass.
        if config_mentions_native:
            return NumericReportingGuard(
                active=True,
                status="failed",
                reason=f"chemistry-native domain profile is invalid: {exc}",
            )
        return NumericReportingGuard(
            active=False,
            status="not_applicable",
            reason="domain profile is unavailable and not chemistry-native",
        )
    if config_mentions_native and not config_valid:
        return NumericReportingGuard(
            active=True,
            status="failed",
            reason="chemistry-native domain profile config is invalid JSON",
        )
    if profile_name != "chemistry-native":
        return NumericReportingGuard(
            active=False,
            status="not_applicable",
            reason="domain profile is not chemistry-native",
        )
    lean_source_sha256 = ""
    bundle_digest = ""
    numeric_outputs = 0
    try:
        if source_bytes is None:
            source_bytes = target.read_bytes()
        elif not isinstance(source_bytes, bytes):
            raise NumericReportingGuardError(
                "numeric target source must be supplied as immutable bytes"
            )
        lean_source_sha256 = _sha256(source_bytes)
        source = source_bytes.decode("utf-8")
        row, bundle_digest = _problem_row(project_path, target)
        policies = _numeric_output_policies(row)
        numeric_outputs = len(policies)
        raw_certificates = _parse_certificates(source)
        if not policies:
            if raw_certificates:
                raise NumericReportingGuardError(
                    "nonnumeric target contains a numeric reporting certificate"
                )
            return NumericReportingGuard(
                active=True,
                status="not_applicable",
                reason="target has no numeric requested outputs",
                lean_source_sha256=lean_source_sha256,
                bundle_sha256=bundle_digest,
            )
        if not raw_certificates:
            return NumericReportingGuard(
                active=True,
                status=NUMERIC_REPORTING_OPTIONAL_AUDIT_STATUS,
                reason=NUMERIC_REPORTING_MARKERS_ABSENT_REASON,
                numeric_outputs=numeric_outputs,
                lean_source_sha256=lean_source_sha256,
                bundle_sha256=bundle_digest,
            )
        certificates = tuple(
            _certificate(item, policies) for item in raw_certificates
        )
        by_output: dict[str, list[NumericReportingCertificate]] = {}
        for certificate in certificates:
            by_output.setdefault(certificate.output_id, []).append(certificate)
        missing = sorted(set(policies) - set(by_output))
        duplicates = sorted(
            output_id for output_id, items in by_output.items() if len(items) != 1
        )
        if missing or duplicates:
            details = []
            if missing:
                details.append("missing " + ", ".join(missing))
            if duplicates:
                details.append("duplicate " + ", ".join(duplicates))
            raise NumericReportingGuardError(
                "numeric reporting certificates must cover each numeric output "
                "exactly once: " + "; ".join(details)
            )
        if len({item.raw_declaration for item in certificates}) != len(certificates):
            raise NumericReportingGuardError(
                "numeric outputs must use distinct raw declarations"
            )
        if len({item.reporting_declaration for item in certificates}) != len(certificates):
            raise NumericReportingGuardError(
                "numeric outputs must use distinct reporting declarations"
            )
        ordered = tuple(
            by_output[output_id][0] for output_id in policies
        )
        return NumericReportingGuard(
            active=True,
            status="ready",
            reason="static reporting certificate checks passed; Lean proof pending",
            numeric_outputs=numeric_outputs,
            lean_source_sha256=lean_source_sha256,
            bundle_sha256=bundle_digest,
            certificates=ordered,
            probe_suffix=_probe_suffix(ordered),
        )
    except (OSError, UnicodeDecodeError, NumericReportingGuardError) as exc:
        return NumericReportingGuard(
            active=True,
            status="failed",
            reason=str(exc)[:MAX_NUMERIC_REPORTING_REASON_LENGTH],
            numeric_outputs=numeric_outputs,
            lean_source_sha256=lean_source_sha256,
            bundle_sha256=bundle_digest,
        )


def finalized_guard_evidence(
    guard: NumericReportingGuard, *, lean_probe_passed: bool | None,
) -> dict[str, Any]:
    """Finalize static evidence with the result of the trusted Lean probe."""
    evidence = guard.evidence()
    if guard.status != "ready":
        return evidence
    if lean_probe_passed is True:
        evidence.update(
            status="passed",
            reason=(
                "predeclared precision determines every quantum and Lean "
                "type-checks every exact ReportsAtQuantum carrier"
            ),
            lean_probe_passed=True,
        )
    else:
        evidence.update(
            status="failed",
            reason=(
                "Lean rejected at least one exact ReportsAtQuantum carrier "
                "generated from the predeclared policy"
            ),
            lean_probe_passed=False,
        )
    return evidence


def numeric_reporting_blockers(preflight: Mapping[str, Any] | None) -> list[dict[str, str]]:
    """Convert every nonpassing active guard into a target-scoped blocker."""
    if not isinstance(preflight, Mapping):
        return []
    blockers: list[dict[str, str]] = []
    raw_targets = preflight.get("targets")
    if not isinstance(raw_targets, list):
        return blockers
    for row in raw_targets:
        if not isinstance(row, Mapping):
            continue
        guard = row.get("numeric_reporting")
        if not isinstance(guard, Mapping) or guard.get("active") is not True:
            continue
        status = str(guard.get("status") or "").strip()
        if status in {
            "passed", "not_applicable", NUMERIC_REPORTING_OPTIONAL_AUDIT_STATUS,
        }:
            continue
        rel = str(row.get("file") or "").strip()
        reason = str(guard.get("reason") or "numeric reporting guard failed").strip()
        if rel:
            blockers.append({
                "source": "numeric-reporting-guard",
                "file": rel,
                "kind": (
                    "invalid_reporting_certificate"
                    if status == "failed"
                    else "reporting_verification_unavailable"
                ),
                "reason": reason[:2000],
            })
    return blockers
