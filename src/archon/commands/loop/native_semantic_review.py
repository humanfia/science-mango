"""Fail-closed semantic certificates for native answer-blind chemistry Review.

The native chemistry workflow deliberately removes the strict, answer-bearing
source-report route before the model loop starts.  Its problem-only JSONL
bundle nevertheless contains a controller-authored requested-output contract.
This module binds an ordinary formalization Review milestone to that contract
without loading (or knowing about) any grader or official-answer artifact.

The checks here are structural.  They ensure that a passing reviewer records a
source-first derivation for every requested output, makes its interpretation
and source locators explicit, and reports exact agreement with the semantic
card and Lean statement.  They do not compare a derived raw value with an
answer key; mathematical correctness remains the responsibility of the
independent derivation and Lean proof.
"""

from __future__ import annotations

import copy
import functools
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
from pathlib import Path
from typing import Any, Mapping

from archon.commands.tooling.domain_profile import load_domain_profile


SCHEMA_VERSION = 1
BUNDLE_REL = Path("icho_2026_source/questions_only.jsonl")
MANIFEST_REL = Path("isolation_manifest.json")
SEED_PROTOCOL = "icho-problem-only-solver-seed-v1"
NATIVE_PROFILE = "chemistry-native"
MAX_BUNDLE_BYTES = 16 * 1024 * 1024
MAX_BUNDLE_RECORDS = 4096
MAX_TEXT_CHARS = 1_600
MAX_JSON_VALUE_CHARS = 2_000
MAX_ITEMS_PER_FIELD = 32
MAX_OUTPUT_BYTES = 8 * 1024
MAX_CERTIFICATE_BYTES = 192 * 1024
MAX_PINNED_PROBE_OUTPUT_BYTES = 64 * 1024
PINNED_PROBE_TIMEOUT_SECONDS = 60
PINNED_LEAN_VERSION_TIMEOUT_SECONDS = 5
MAX_PINNED_LEAN_VERSION_OUTPUT_BYTES = 4 * 1024
MAX_PINNED_DECLARATIONS = 256
MAX_PINNED_SOURCE_FILE_BYTES = 4 * 1024 * 1024
MAX_PINNED_SOURCE_SCAN_BYTES = 512 * 1024 * 1024
MAX_PINNED_SOURCE_FILES = 20_000
MAX_PINNED_SOURCE_DECLARATIONS = 1_000_000
MAX_PINNED_CANDIDATE_MODULES = 16
MAX_PINNED_SEARCH_ROOTS = 64

_TOP_FIELDS = {
    "schema_version", "method", "ambiguity", "requested_outputs",
}
_OUTPUT_FIELDS = {
    "id", "kind", "source_requirement", "quantity_definition",
    "process_scope", "basis", "constants", "dependencies",
    "branch_conditions", "unit", "raw_result", "reporting",
    "lean_carriers", "semantic_card_comparison",
    "lean_statement_comparison", "source_locators", "evidence",
}
_LOCATOR_FIELDS = {"kind", "reference"}
_PROCESS_SCOPE_FIELDS = {"kind", "description"}
_CONSTANT_FIELDS = {"name", "value", "unit", "source_locator"}
_BASIS_FIELDS = {
    "status", "numerator", "denominator", "mass_or_composition_basis",
}
_DEPENDENCY_FIELDS = {"kind", "reference", "relation", "source_locator"}
_BRANCH_CONDITION_FIELDS = {"condition", "source_locator"}
_RAW_RESULT_FIELDS = {"value_or_expression", "exact_unrounded", "derivation"}
_REPORTING_FIELDS = {"policy", "global_policy", "application"}
_LEAN_CARRIER_FIELDS = {"inputs", "relations", "raw_result", "reported_result"}
_COMPARISON_FIELDS = {"status", "evidence"}
_LOCATOR_KINDS = {
    "problem_text", "problem_image", "previous_parts", "pinned_library",
}
_PROCESS_SCOPES = {
    "cumulative", "overall", "repeated_process", "per_step", "per_cycle",
    "marginal", "instantaneous", "not_applicable", "other",
}
_BASIS_STATUSES = {"applicable", "not_applicable"}
_DEPENDENCY_KINDS = {
    "requested_output", "previous_part", "source_quantity",
    "governing_relation",
}
_SCHEMA_INDEX = r"[0-9]{1,3}"
_SCHEMA_OUTPUT = (
    rf"independent_rederivation\.requested_outputs\[{_SCHEMA_INDEX}\]"
)
_SCHEMA_LOCATOR = (
    rf"{_SCHEMA_OUTPUT}\."
    rf"(?:(?:constants|dependencies|branch_conditions)\[{_SCHEMA_INDEX}\]"
    rf"\.source_locator|source_locators\[{_SCHEMA_INDEX}\])"
)
_SCHEMA_OBJECTS: tuple[tuple[str, set[str]], ...] = (
    (r"independent_rederivation", _TOP_FIELDS),
    (_SCHEMA_OUTPUT, _OUTPUT_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.process_scope", _PROCESS_SCOPE_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.basis", _BASIS_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.constants\[{_SCHEMA_INDEX}\]", _CONSTANT_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.dependencies\[{_SCHEMA_INDEX}\]", _DEPENDENCY_FIELDS),
    (
        rf"{_SCHEMA_OUTPUT}\.branch_conditions\[{_SCHEMA_INDEX}\]",
        _BRANCH_CONDITION_FIELDS,
    ),
    (rf"{_SCHEMA_OUTPUT}\.raw_result", _RAW_RESULT_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.reporting", _REPORTING_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.lean_carriers", _LEAN_CARRIER_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.semantic_card_comparison", _COMPARISON_FIELDS),
    (rf"{_SCHEMA_OUTPUT}\.lean_statement_comparison", _COMPARISON_FIELDS),
    (
        rf"{_SCHEMA_OUTPUT}\.(?:constants|dependencies)\[{_SCHEMA_INDEX}\]"
        r"\.source_locator",
        _LOCATOR_FIELDS,
    ),
    (
        rf"{_SCHEMA_OUTPUT}\.branch_conditions\[{_SCHEMA_INDEX}\]"
        r"\.source_locator",
        _LOCATOR_FIELDS,
    ),
    (rf"{_SCHEMA_OUTPUT}\.source_locators\[{_SCHEMA_INDEX}\]", _LOCATOR_FIELDS),
)
_SCHEMA_LISTS: tuple[str, ...] = (
    r"independent_rederivation\.requested_outputs",
    rf"{_SCHEMA_OUTPUT}\.(?:constants|dependencies|branch_conditions|source_locators)",
    rf"{_SCHEMA_OUTPUT}\.lean_carriers\."
    r"(?:inputs|relations|raw_result|reported_result)",
)
_SCHEMA_STRINGS: tuple[str, ...] = (
    rf"{_SCHEMA_OUTPUT}\."
    r"(?:id|kind|source_requirement|quantity_definition|unit|evidence)",
    rf"{_SCHEMA_OUTPUT}\.process_scope\.(?:kind|description)",
    rf"{_SCHEMA_OUTPUT}\.basis\."
    r"(?:status|numerator|denominator|mass_or_composition_basis)",
    rf"{_SCHEMA_OUTPUT}\.constants\[{_SCHEMA_INDEX}\]\.(?:name|unit)",
    rf"{_SCHEMA_OUTPUT}\.dependencies\[{_SCHEMA_INDEX}\]\."
    r"(?:kind|reference|relation)",
    rf"{_SCHEMA_OUTPUT}\.branch_conditions\[{_SCHEMA_INDEX}\]\.condition",
    rf"{_SCHEMA_OUTPUT}\.raw_result\.derivation",
    rf"{_SCHEMA_OUTPUT}\.reporting\.application",
    rf"{_SCHEMA_OUTPUT}\.(?:semantic_card|lean_statement)_comparison\.evidence",
    (
        rf"{_SCHEMA_OUTPUT}\.(?:constants|dependencies|branch_conditions)"
        rf"\[{_SCHEMA_INDEX}\]\.source_locator\.(?:kind|reference)"
    ),
    rf"{_SCHEMA_OUTPUT}\.source_locators\[{_SCHEMA_INDEX}\]\.(?:kind|reference)",
)
_LEAN_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
_LEAN_MODULE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
_PREVIOUS_PART_RE = re.compile(
    r"^previous_parts\[(?P<index>[0-9]+)\]"
    r"(?P<suffix>(?:\.[A-Za-z_][A-Za-z0-9_-]*)*)$"
)
_BARE_PREVIOUS_PART_RE = re.compile(r"^[0-9]+$")
_PINNED_PROBE_RESULT_RE = re.compile(
    r"ARCHON_PINNED_ORIGIN\|"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)\|"
    r"(?P<module>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)
_LEAN_SOURCE_DECLARATION_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:public|private|protected|noncomputable|unsafe|partial)[ \t]+)*"
    r"(?:abbrev|axiom|class|def|inductive|instance|lemma|opaque|structure|theorem)"
    r"[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_']*"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*)(?![A-Za-z0-9_'])",
    re.MULTILINE,
)
_LEAN_SOURCE_IDENTIFIER_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(?P<token>[A-Za-z_][A-Za-z0-9_']*)"
    r"(?![A-Za-z0-9_'])"
)
_LEAN_TOOLCHAIN_RE = re.compile(
    r"^leanprover/lean4:v(?P<version>[0-9]+\.[0-9]+\.[0-9]+)$"
)
_PINNED_PACKAGES: dict[str, tuple[str, str]] = {
    # package filter: (fixed source/module root, fixed Lake package directory)
    "Mathlib": ("Mathlib", "mathlib"),
    "Physlib": ("Physlib", "Physlib"),
    "CRNT": ("CRNT", "crnt-lean"),
}
_PREVIOUS_PART_FORMAT = (
    "ASCII decimal zero-based index or previous_parts[index][.field]"
)
_PINNED_LIBRARY_FORMAT = (
    "safe fully-qualified existing declaration from a configured pinned library"
)
_PROBLEM_TEXT_SCALAR_ROOTS = (
    "question", "current_question", "shared_context",
)
_PROBLEM_TEXT_STRUCTURED_ROOTS = (
    "reporting_policy", "measurement_policy", "candidate_domain_policy",
)
_LOCATOR_FIELD_SEGMENT = r"[A-Za-z_][A-Za-z0-9_-]*"
_LOCATOR_FRAGMENT_FORMAT = r"[A-Za-z0-9][A-Za-z0-9_.:-]*"
_LOCATOR_FRAGMENT_RE = re.compile(rf"^{_LOCATOR_FRAGMENT_FORMAT}$")
_STRUCTURED_TEXT_REFERENCE_RE = re.compile(
    rf"^(?P<root>{'|'.join(_PROBLEM_TEXT_STRUCTURED_ROOTS)})"
    rf"(?P<suffix>(?:\.{_LOCATOR_FIELD_SEGMENT})+)$"
)
_REQUESTED_OUTPUT_TEXT_REFERENCE_RE = re.compile(
    rf"^requested_outputs\[(?P<index>0|[1-9][0-9]*)\]"
    rf"(?P<suffix>(?:\.{_LOCATOR_FIELD_SEGMENT})+)$"
)
_PROBLEM_TEXT_FORMAT = (
    "exact scalar root[#safe-fragment], existing structured_root.field chain, "
    "or requested_outputs[existing_index].field chain"
)


class _CertificateError(ValueError):
    pass


class _PinnedResolutionUnavailable(RuntimeError):
    """A transient or trust failure that must never populate a negative cache."""


def _error(message: str) -> None:
    raise _CertificateError(message)


def _safe_bundle_path(project_path: Path) -> Path:
    root = project_path.resolve()
    cursor = root
    for part in BUNDLE_REL.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            _error(f"problem-only bundle traverses a symlink: {BUNDLE_REL}")
    try:
        resolved = cursor.resolve()
        resolved.relative_to(root)
    except (OSError, ValueError):
        _error(f"problem-only bundle escapes the project: {BUNDLE_REL}")
    if not resolved.is_file() or resolved.is_symlink():
        _error(f"problem-only bundle is missing or unsafe: {BUNDLE_REL}")
    try:
        size = resolved.stat().st_size
    except OSError:
        _error(f"problem-only bundle is unreadable: {BUNDLE_REL}")
    if size <= 0 or size > MAX_BUNDLE_BYTES:
        _error("problem-only bundle size is outside the bounded native contract")
    return resolved


def _sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _root_owned_not_publicly_writable(path: Path) -> bool:
    """Return whether a path is controller-owned and solver-immutable."""
    try:
        metadata = path.stat()
    except OSError:
        return False
    return metadata.st_uid == 0 and not (stat.S_IMODE(metadata.st_mode) & 0o022)


def _trusted_plain_file(path: Path) -> bool:
    try:
        metadata = path.lstat()
    except OSError:
        return False
    return (
        stat.S_ISREG(metadata.st_mode)
        and not stat.S_ISLNK(metadata.st_mode)
        and metadata.st_uid == 0
        and not (stat.S_IMODE(metadata.st_mode) & 0o022)
    )


def _trusted_plain_directory(path: Path) -> bool:
    try:
        metadata = path.lstat()
    except OSError:
        return False
    return (
        stat.S_ISDIR(metadata.st_mode)
        and not stat.S_ISLNK(metadata.st_mode)
        and metadata.st_uid == 0
        and not (stat.S_IMODE(metadata.st_mode) & 0o022)
    )


def _minimal_lean_environment(*, lean_path: str | None = None) -> dict[str, str]:
    environment = {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8"}
    if lean_path is not None:
        environment["LEAN_PATH"] = lean_path
    return environment


def _trusted_pinned_environment(
    project_path: Path,
    packages: tuple[str, ...],
) -> tuple[Path, str, Path, tuple[tuple[str, str], ...]] | None:
    """Bind the Lean probe to the controller-sealed project and package tree."""
    try:
        root = project_path.resolve(strict=True)
    except OSError:
        return None
    if not root.is_dir() or not _root_owned_not_publicly_writable(root):
        return None

    controller_files = [
        root / ".archon/config.json",
        root / "lake-manifest.json",
        root / "lean-toolchain",
    ]
    lakefiles = [
        path for path in (root / "lakefile.toml", root / "lakefile.lean")
        if path.exists() or path.is_symlink()
    ]
    if len(lakefiles) != 1:
        return None
    controller_files.extend(lakefiles)
    if any(not _trusted_plain_file(path) for path in controller_files):
        return None

    try:
        toolchain_text = (root / "lean-toolchain").read_text(
            encoding="utf-8",
        ).strip()
    except (OSError, UnicodeDecodeError):
        return None
    toolchain_match = _LEAN_TOOLCHAIN_RE.fullmatch(toolchain_text)
    if toolchain_match is None:
        return None
    lean_version = toolchain_match.group("version")

    lean_command = shutil.which("lean")
    if not lean_command:
        return None
    lean_candidate = Path(lean_command)
    try:
        lean_path = lean_candidate.resolve(strict=True)
    except OSError:
        return None
    if (
        lean_candidate.is_symlink()
        or lean_candidate.absolute() != lean_path
        or not _trusted_plain_file(lean_path)
        or not os.access(lean_path, os.X_OK)
        or lean_path.parent.parent.name != f"lean-v{lean_version}"
        or not _trusted_plain_directory(lean_path.parent)
        or not _trusted_plain_directory(lean_path.parent.parent)
    ):
        return None
    try:
        version_check = subprocess.run(
            [str(lean_path), "--version"],
            cwd=lean_path.parent,
            env=_minimal_lean_environment(),
            capture_output=True,
            text=True,
            timeout=PINNED_LEAN_VERSION_TIMEOUT_SECONDS,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    version_output = (version_check.stdout or "") + (version_check.stderr or "")
    if (
        version_check.returncode != 0
        or len(version_output.encode("utf-8", errors="replace"))
        > MAX_PINNED_LEAN_VERSION_OUTPUT_BYTES
        or re.search(
            rf"\bversion {re.escape(lean_version)}(?:,|\))",
            version_output,
        )
        is None
    ):
        return None

    lake_root = root / ".lake"
    packages_link = lake_root / "packages"
    try:
        link_metadata = packages_link.lstat()
        packages_root = packages_link.resolve(strict=True)
    except OSError:
        return None
    if (
        not _root_owned_not_publicly_writable(lake_root)
        or link_metadata.st_uid != 0
        or not packages_root.is_dir()
        or not _root_owned_not_publicly_writable(packages_root)
    ):
        return None

    search_roots: list[tuple[str, str]] = []
    try:
        package_directories = sorted(
            (path for path in packages_root.iterdir() if path.is_dir()),
            key=lambda path: path.name,
        )
    except OSError:
        return None
    if len(package_directories) > MAX_PINNED_SEARCH_ROOTS:
        return None
    for package_directory in package_directories:
        if not _trusted_plain_directory(package_directory):
            return None
        build_root = package_directory / ".lake/build/lib/lean"
        if not build_root.exists():
            continue
        cursor = package_directory
        for part in Path(".lake/build/lib/lean").parts:
            cursor = cursor / part
            if not _trusted_plain_directory(cursor):
                return None
        try:
            resolved_build_root = build_root.resolve(strict=True)
            resolved_build_root.relative_to(package_directory)
        except (OSError, ValueError):
            return None
        search_roots.append((package_directory.name, str(resolved_build_root)))
    if not search_roots or len(search_roots) > MAX_PINNED_SEARCH_ROOTS:
        return None

    try:
        lean_metadata = lean_path.stat()
    except OSError:
        return None
    fingerprint_parts = [
        str(root),
        str(packages_root),
        f"lean:{lean_path}:{lean_metadata.st_dev}:{lean_metadata.st_ino}:"
        f"{lean_metadata.st_size}:{lean_metadata.st_mtime_ns}:"
        f"{lean_metadata.st_ctime_ns}",
    ]
    for path in controller_files:
        digest = _sha256(path)
        if not digest:
            return None
        fingerprint_parts.append(f"{path.name}:{digest}")
    for package in packages:
        package_config = _PINNED_PACKAGES.get(package)
        if package_config is None:
            return None
        source_root_name, directory = package_config
        package_root = packages_root / directory
        source_root = package_root / source_root_name
        if (
            not _trusted_plain_directory(package_root)
            or not _trusted_plain_directory(source_root)
        ):
            return None
        try:
            package_metadata = package_root.stat()
            source_metadata = source_root.stat()
        except OSError:
            return None
        fingerprint_parts.append(
            f"{package}:{package_metadata.st_dev}:{package_metadata.st_ino}:"
            f"{package_metadata.st_mtime_ns}:{source_metadata.st_ino}:"
            f"{source_metadata.st_mtime_ns}"
        )
    for directory, search_root in search_roots:
        try:
            metadata = Path(search_root).stat()
        except OSError:
            return None
        fingerprint_parts.append(
            f"search:{directory}:{search_root}:{metadata.st_dev}:"
            f"{metadata.st_ino}:{metadata.st_mtime_ns}:{metadata.st_ctime_ns}"
        )
    fingerprint = hashlib.sha256("\n".join(fingerprint_parts).encode()).hexdigest()
    return packages_root, fingerprint, lean_path, tuple(search_roots)


def _trusted_module_artifact_path(
    packages_root: Path,
    *,
    package: str,
    module: str,
    search_roots: tuple[tuple[str, str], ...],
) -> Path | None:
    """Resolve one unshadowed module artifact owned by ``package``."""
    package_config = _PINNED_PACKAGES.get(package)
    if package_config is None or not (
        module == package or module.startswith(package + ".")
    ):
        return None
    _source_root, directory = package_config
    relative = Path(*module.split(".")).with_suffix(".olean")
    matches: list[tuple[str, Path]] = []
    for owner, root_string in search_roots:
        search_root = Path(root_string)
        artifact = search_root / relative
        if not artifact.exists() and not artifact.is_symlink():
            continue
        cursor = search_root
        for part in relative.parts[:-1]:
            cursor = cursor / part
            if not _trusted_plain_directory(cursor):
                return None
        if artifact.is_symlink():
            return None
        try:
            resolved = artifact.resolve(strict=True)
            resolved.relative_to(search_root)
        except (OSError, ValueError):
            return None
        if not _trusted_plain_file(resolved):
            return None
        matches.append((owner, resolved))
    if len(matches) != 1 or matches[0][0] != directory:
        return None
    expected_root = (
        packages_root / directory / ".lake/build/lib/lean"
    ).resolve()
    try:
        matches[0][1].relative_to(expected_root)
    except ValueError:
        return None
    return matches[0][1]


def _trusted_module_artifact(
    packages_root: Path,
    *,
    package: str,
    module: str,
    search_roots: tuple[tuple[str, str], ...],
) -> bool:
    return _trusted_module_artifact_path(
        packages_root,
        package=package,
        module=module,
        search_roots=search_roots,
    ) is not None


def _trusted_module_artifact_fingerprint(
    packages_root: Path,
    *,
    package: str,
    module: str,
    search_roots: tuple[tuple[str, str], ...],
) -> str | None:
    """Return cache-binding metadata for one currently sealed ``.olean``."""
    artifact = _trusted_module_artifact_path(
        packages_root,
        package=package,
        module=module,
        search_roots=search_roots,
    )
    if artifact is None:
        return None
    try:
        metadata = artifact.stat()
    except OSError:
        return None
    return (
        f"{package}|{module}|{metadata.st_dev}|{metadata.st_ino}|"
        f"{metadata.st_size}|{metadata.st_mtime_ns}|{metadata.st_ctime_ns}|"
        f"{metadata.st_uid}|{stat.S_IMODE(metadata.st_mode)}"
    )


def _trusted_source_file(package_root: Path, source: Path) -> bool:
    cursor = package_root
    try:
        relative = source.relative_to(package_root)
    except ValueError:
        return False
    for part in relative.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            return False
    return _trusted_plain_file(source)


@functools.lru_cache(maxsize=16)
def _pinned_source_tail_index(
    packages_root_string: str,
    packages: tuple[str, ...],
    tails: tuple[str, ...],
    environment_fingerprint: str,
) -> tuple[tuple[str, str, str, str], ...]:
    """Find bounded source modules for declaration tails in sealed packages.

    Explicit declaration syntax is preferred.  For names introduced by
    ``alias``, ``to_additive``, or another elaborator, an exact identifier-tail
    occurrence provides a recall-only fallback.  That fallback cannot create
    an acceptance: the subsequent Lean process resolves the full name and its
    defining module from the compiled environment.
    """
    del environment_fingerprint  # It intentionally participates in the cache key.
    if (
        not tails
        or len(tails) > MAX_PINNED_DECLARATIONS
        or any(
            re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", tail) is None
            for tail in tails
        )
    ):
        return ()
    packages_root = Path(packages_root_string)
    wanted = set(tails)
    explicit: dict[str, set[tuple[str, str]]] = {
        tail: set() for tail in tails
    }
    fallback: dict[str, set[tuple[str, str]]] = {
        tail: set() for tail in tails
    }
    scanned_bytes = 0
    scanned_files = 0
    matched_records = 0
    for package in packages:
        package_config = _PINNED_PACKAGES.get(package)
        if package_config is None:
            raise _PinnedResolutionUnavailable("unsupported pinned package")
        source_name, directory = package_config
        package_root = (packages_root / directory).resolve()
        source_root = package_root / source_name
        try:
            source_files = sorted(source_root.rglob("*.lean"))
        except OSError:
            raise _PinnedResolutionUnavailable("pinned source scan failed")
        scanned_files += len(source_files)
        if scanned_files > MAX_PINNED_SOURCE_FILES:
            raise _PinnedResolutionUnavailable("pinned source file limit exceeded")
        for source in source_files:
            try:
                size = source.stat().st_size
            except OSError:
                raise _PinnedResolutionUnavailable("pinned source stat failed")
            scanned_bytes += max(0, size)
            if scanned_bytes > MAX_PINNED_SOURCE_SCAN_BYTES:
                raise _PinnedResolutionUnavailable("pinned source byte limit exceeded")
            if size == 0:
                continue
            if size < 0 or size > MAX_PINNED_SOURCE_FILE_BYTES:
                raise _PinnedResolutionUnavailable("pinned source size limit exceeded")
            if not _trusted_source_file(package_root, source):
                raise _PinnedResolutionUnavailable("untrusted pinned source")
            try:
                text = source.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                raise _PinnedResolutionUnavailable("pinned source read failed")
            module = source.relative_to(package_root).with_suffix("")
            module_name = ".".join(module.parts)
            if _LEAN_MODULE_RE.fullmatch(module_name) is None:
                raise _PinnedResolutionUnavailable("unsafe pinned module name")
            for match in _LEAN_SOURCE_DECLARATION_RE.finditer(text):
                tail = match.group("name").rsplit(".", 1)[-1]
                if tail in wanted:
                    explicit[tail].add((package, module_name))
                    matched_records += 1
            for match in _LEAN_SOURCE_IDENTIFIER_RE.finditer(text):
                token = match.group("token")
                if token not in wanted:
                    continue
                fallback[token].add((package, module_name))
                matched_records += 1
            if matched_records > MAX_PINNED_SOURCE_DECLARATIONS:
                raise _PinnedResolutionUnavailable(
                    "pinned source declaration limit exceeded"
                )
    selected: set[tuple[str, str, str, str]] = set()
    for tail in tails:
        selected.update(
            ("explicit", package, tail, module)
            for package, module in explicit[tail]
        )
        selected.update(
            ("fallback", package, tail, module)
            for package, module in fallback[tail]
        )
    return tuple(sorted(selected))


def _pinned_candidate_modules(
    packages_root: Path,
    packages: tuple[str, ...],
    references: tuple[str, ...],
    environment_fingerprint: str,
    search_roots: tuple[tuple[str, str], ...],
    *,
    match_kind: str,
) -> tuple[str, ...]:
    """Select bounded source candidates; Lean performs the exact-name check."""
    if (
        not references
        or len(references) > MAX_PINNED_DECLARATIONS
        or any(_LEAN_NAME_RE.fullmatch(name) is None for name in references)
    ):
        return ()
    tails = {reference.rsplit(".", 1)[-1] for reference in references}
    modules: set[str] = set()
    for record_kind, package, tail, module in _pinned_source_tail_index(
        str(packages_root), packages, tuple(sorted(tails)), environment_fingerprint,
    ):
        if record_kind != match_kind or tail not in tails:
            continue
        if not _trusted_module_artifact(
            packages_root,
            package=package,
            module=module,
            search_roots=search_roots,
        ):
            continue
        modules.add(module)
        if len(modules) > MAX_PINNED_CANDIDATE_MODULES:
            return ()
    return tuple(sorted(modules))


@functools.lru_cache(maxsize=256)
def _probe_pinned_library_declarations(
    lean_executable: str,
    packages: tuple[str, ...],
    references: tuple[str, ...],
    candidate_modules: tuple[str, ...],
    environment_fingerprint: str,
    artifact_fingerprint: str,
    search_roots: tuple[tuple[str, str], ...],
) -> tuple[tuple[str, str], ...]:
    """Resolve declaration origins in one bounded, read-only Lean process."""
    del environment_fingerprint  # It intentionally participates in the cache key.
    del artifact_fingerprint  # It intentionally participates in the cache key.
    if not references or not candidate_modules:
        return ()
    if any(_LEAN_NAME_RE.fullmatch(name) is None for name in references):
        return ()
    if any(package not in _PINNED_PACKAGES for package in packages):
        return ()
    if any(
        _LEAN_MODULE_RE.fullmatch(module) is None
        or not any(
            module == package or module.startswith(package + ".")
            for package in packages
        )
        for module in candidate_modules
    ):
        return ()

    lean_path = Path(lean_executable)
    try:
        resolved_lean_path = lean_path.resolve(strict=True)
    except OSError:
        raise _PinnedResolutionUnavailable("Lean path is unavailable")
    if (
        resolved_lean_path != lean_path
        or not _trusted_plain_file(lean_path)
        or not os.access(lean_path, os.X_OK)
    ):
        raise _PinnedResolutionUnavailable("Lean executable is untrusted")

    imports = [f"import {module}" for module in candidate_modules]
    source_lines = [
        *imports,
        "open Lean Elab Command",
        'elab "#archonPinnedOrigin " s:str : command => do',
        "  let env ← getEnv",
        "  let name := s.getString.toName",
        "  match env.find? name, env.getModuleIdxFor? name with",
        "  | some info, some moduleIdx =>",
        "    unless info.isUnsafe || info.isPartial do",
        "      let moduleName := env.header.moduleNames[moduleIdx.toNat]!",
        '      logInfo m!"ARCHON_PINNED_ORIGIN|{name}|{moduleName}"',
        "  | _, _ => pure ()",
        *(
            "#archonPinnedOrigin " + json.dumps(name, ensure_ascii=True)
            for name in references
        ),
        "",
    ]
    lean_search_path = os.pathsep.join(root for _owner, root in search_roots)
    if not lean_search_path:
        raise _PinnedResolutionUnavailable("Lean search path is unavailable")
    try:
        completed = subprocess.run(
            [str(lean_path), "--stdin", "-M", "4096"],
            cwd=lean_path.parent,
            env=_minimal_lean_environment(lean_path=lean_search_path),
            input="\n".join(source_lines),
            capture_output=True,
            text=True,
            timeout=PINNED_PROBE_TIMEOUT_SECONDS,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        raise _PinnedResolutionUnavailable("pinned Lean origin probe failed")
    output = (completed.stdout or "") + (completed.stderr or "")
    if completed.returncode != 0:
        raise _PinnedResolutionUnavailable("pinned Lean origin probe rejected input")
    if (
        len(output.encode("utf-8", errors="replace"))
        > MAX_PINNED_PROBE_OUTPUT_BYTES
    ):
        raise _PinnedResolutionUnavailable("pinned Lean origin output exceeded limit")

    requested = set(references)
    observed: dict[str, set[str]] = {}
    for match in _PINNED_PROBE_RESULT_RE.finditer(output):
        name = match.group("name")
        module = match.group("module")
        if name not in requested:
            continue
        observed.setdefault(name, set()).add(module)
    return tuple(sorted(
        (name, next(iter(modules)))
        for name, modules in observed.items()
        if len(modules) == 1
    ))


def _package_for_module(
    packages: tuple[str, ...],
    module: str,
) -> str | None:
    matches = [
        package for package in packages
        if module == package or module.startswith(package + ".")
    ]
    return matches[0] if len(matches) == 1 else None


def _candidate_artifact_fingerprint(
    packages_root: Path,
    packages: tuple[str, ...],
    modules: tuple[str, ...],
    search_roots: tuple[tuple[str, str], ...],
) -> str | None:
    parts: list[str] = []
    for module in modules:
        package = _package_for_module(packages, module)
        if package is None:
            return None
        fingerprint = _trusted_module_artifact_fingerprint(
            packages_root,
            package=package,
            module=module,
            search_roots=search_roots,
        )
        if fingerprint is None:
            return None
        parts.append(fingerprint)
    if not parts:
        return None
    return hashlib.sha256("\n".join(parts).encode()).hexdigest()


def _verified_pinned_library_declarations(
    project_path: Path,
    packages: tuple[str, ...],
    references: set[str],
) -> frozenset[str]:
    candidates = tuple(sorted(
        reference for reference in references
        if _LEAN_NAME_RE.fullmatch(reference) is not None
    ))
    if not candidates:
        return frozenset()
    trusted = _trusted_pinned_environment(project_path, packages)
    if trusted is None:
        return frozenset()
    packages_root, fingerprint, lean_path, search_roots = trusted
    observed: dict[str, str] = {}

    def probe(
        requested: tuple[str, ...],
        modules: tuple[str, ...],
    ) -> None:
        if not requested or not modules:
            return
        artifact_fingerprint = _candidate_artifact_fingerprint(
            packages_root, packages, modules, search_roots,
        )
        if artifact_fingerprint is None:
            raise _PinnedResolutionUnavailable(
                "candidate module artifact is ambiguous or untrusted"
            )
        for name, module in _probe_pinned_library_declarations(
            str(lean_path),
            packages,
            requested,
            modules,
            fingerprint,
            artifact_fingerprint,
            search_roots,
        ):
            observed[name] = module

    try:
        explicit_modules = _pinned_candidate_modules(
            packages_root,
            packages,
            candidates,
            fingerprint,
            search_roots,
            match_kind="explicit",
        )
        probe(candidates, explicit_modules)
        unresolved = tuple(name for name in candidates if name not in observed)
        if unresolved:
            fallback_modules = tuple(
                module for module in _pinned_candidate_modules(
                    packages_root,
                    packages,
                    unresolved,
                    fingerprint,
                    search_roots,
                    match_kind="fallback",
                )
                if module not in explicit_modules
            )
            probe(unresolved, fallback_modules)
    except _PinnedResolutionUnavailable:
        return frozenset()

    # Do not cache trust metadata: defining artifacts are re-resolved and
    # rechecked even when the bounded Lean origin probe itself hits its cache.
    return frozenset(
        name for name, module in observed.items()
        if (
            (package := _package_for_module(packages, module)) is not None
            and _trusted_module_artifact(
                packages_root,
                package=package,
                module=module,
                search_roots=search_roots,
            )
        )
    )


def _safe_project_file(project_path: Path, relative: str, *, label: str) -> Path:
    if not relative or "\\" in relative:
        _error(f"{label} has an unsafe project path")
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        _error(f"{label} has an unsafe project path")
    root = project_path.resolve()
    cursor = root
    for part in path.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            _error(f"{label} traverses a symlink")
    try:
        resolved = cursor.resolve()
        resolved.relative_to(root)
    except (OSError, ValueError):
        _error(f"{label} escapes the project")
    if not resolved.is_file() or resolved.is_symlink():
        _error(f"{label} is missing or unsafe")
    return resolved


def _load_isolation_manifest(
    project_path: Path,
    *,
    bundle_path: Path,
    rows: list[dict[str, Any]],
) -> tuple[dict[str, Any], str]:
    path = _safe_project_file(
        project_path, MANIFEST_REL.as_posix(), label="isolation manifest",
    )
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        _error("isolation manifest is invalid JSON")
    if not isinstance(value, dict):
        _error("isolation manifest is not an object")
    bundle = value.get("blind_bundle")
    if not isinstance(bundle, Mapping):
        _error("isolation manifest has no blind_bundle object")
    digest = _sha256(bundle_path)
    if (
        bundle.get("path") != BUNDLE_REL.as_posix()
        or bundle.get("sha256") != digest
        or value.get("blind_bundle_sha256") != digest
        or bundle.get("size") != bundle_path.stat().st_size
        or bundle.get("row_count") != len(rows)
    ):
        _error("isolation manifest does not bind the exact problem-only bundle")
    row_ids = sorted(str(row.get("id") or "") for row in rows)
    target_ids = value.get("target_ids")
    if target_ids is None:
        if (
            value.get("schema_version") != 1
            or value.get("protocol") != SEED_PROTOCOL
        ):
            _error(
                "isolation manifest without target_ids is not a canonical "
                "problem-only solver seed"
            )
    elif target_ids != row_ids:
        _error("isolation manifest target_ids do not match the problem-only bundle")
    assets = value.get("assets")
    if not isinstance(assets, Mapping) or not assets:
        _error("isolation manifest has no asset hash inventory")
    for relative, expected_digest in assets.items():
        if (
            not isinstance(relative, str)
            or not isinstance(expected_digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", expected_digest) is None
        ):
            _error("isolation manifest contains an invalid asset hash")
    return value, _sha256(path)


def _safe_asset_path(value: Any) -> str:
    text = str(value or "").strip()
    if (
        not text
        or len(text) > MAX_TEXT_CHARS
        or "\\" in text
        or "://" in text
    ):
        return ""
    path = Path(text)
    if path.is_absolute() or ".." in path.parts:
        return ""
    return path.as_posix().lstrip("./")


def _record_assets(
    row: Mapping[str, Any],
    *,
    project_path: Path,
    manifest_assets: Mapping[str, Any],
) -> tuple[dict[str, str], ...]:
    listed_images: list[str] = []
    images = row.get("images")
    if images is not None:
        if not isinstance(images, list):
            _error("problem row images is not a list")
        for value in images:
            path = _safe_asset_path(value)
            if path:
                listed_images.append(path)
    assets: dict[str, str] = {}
    records = row.get("problem_assets")
    if isinstance(records, list):
        for record in records:
            if not isinstance(record, Mapping):
                continue
            path = _safe_asset_path(record.get("path"))
            digest = str(record.get("sha256") or "")
            if path and record.get("kind") == "problem_page":
                if re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                    _error(f"problem image {path!r} has an invalid declared hash")
                prior = assets.get(path)
                if prior is not None and prior != digest:
                    _error(f"problem image {path!r} has inconsistent hashes")
                assets[path] = digest
    if images is None:
        listed_images = list(assets)
    if listed_images != list(assets) or not assets:
        _error("problem row images do not exactly match hashed problem_page assets")
    bound: list[dict[str, str]] = []
    for name, expected_digest in sorted(assets.items()):
        relative = f"icho_2026_source/image/{name}"
        if manifest_assets.get(relative) != expected_digest:
            _error(f"isolation manifest does not bind problem image {name!r}")
        path = _safe_project_file(project_path, relative, label=f"problem image {name}")
        if _sha256(path) != expected_digest:
            _error(f"problem image {name!r} hash does not match its source contract")
        bound.append({"path": name, "sha256": expected_digest})
    return tuple(bound)


def _load_bundle(project_path: Path) -> list[dict[str, Any]]:
    path = _safe_bundle_path(project_path)
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError):
        _error("problem-only bundle is not readable UTF-8")
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        if len(rows) >= MAX_BUNDLE_RECORDS:
            _error("problem-only bundle exceeds the bounded record count")
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            _error(f"problem-only bundle line {line_number} is invalid JSON")
        if not isinstance(value, dict):
            _error(f"problem-only bundle line {line_number} is not an object")
        rows.append(value)
    if not rows:
        _error("problem-only bundle contains no records")
    return rows


def _validate_requested_output(
    raw: Any, *, record_id: str, index: int,
) -> dict[str, Any]:
    if not isinstance(raw, Mapping):
        _error(f"bundle {record_id} requested output {index} is not an object")
    output_id = str(raw.get("id") or "").strip()
    kind = str(raw.get("kind") or "").strip()
    requirement = str(raw.get("source_requirement") or "").strip()
    unit = raw.get("unit")
    policy = raw.get("reporting_policy")
    if not output_id or not kind or not requirement:
        _error(f"bundle {record_id} requested output {index} is incomplete")
    if not isinstance(unit, str):
        _error(f"bundle {record_id}/{output_id} unit is not a string")
    if not isinstance(policy, Mapping) or not policy:
        _error(f"bundle {record_id}/{output_id} reporting policy is missing")
    return {
        "id": output_id,
        "kind": kind,
        "source_requirement": requirement,
        "unit": unit,
        "reporting_policy": copy.deepcopy(dict(policy)),
    }


def build_native_semantic_review_contract(
    *, project_path: Path, target: Path,
) -> dict[str, Any] | None:
    """Build the problem-only expected contract for one native target.

    ``None`` means that the project is not using the native chemistry profile.
    For that profile, every preparation problem becomes an explicit invalid
    contract so a passing milestone can never bypass the gate.
    """
    profile = load_domain_profile(project_path)
    if profile.name != NATIVE_PROFILE:
        return None
    try:
        root = project_path.resolve()
        target_rel = target.resolve().relative_to(root).as_posix()
    except (OSError, ValueError):
        return {
            "required": True,
            "valid": False,
            "target": "",
            "errors": ["native semantic Review target escapes the project"],
        }

    try:
        pinned_library_packages = tuple(
            package for package in profile.lean_search_packages
            if package in _PINNED_PACKAGES
        )
        if not pinned_library_packages:
            _error("native profile has no supported pinned library packages")
        bundle_path = _safe_bundle_path(root)
        rows = _load_bundle(root)
        isolation_manifest, manifest_sha256 = _load_isolation_manifest(
            root, bundle_path=bundle_path, rows=rows,
        )
        by_target: dict[str, dict[str, Any]] = {}
        for row in rows:
            record_id = str(row.get("id") or "").strip()
            if not record_id or not re.fullmatch(r"[A-Za-z0-9._-]+", record_id):
                _error("problem-only bundle contains a missing or unsafe id")
            expected_target = f"IChO2026Problems/problem_{record_id}.lean"
            if expected_target in by_target:
                _error(f"problem-only bundle contains duplicate id {record_id}")
            if (
                row.get("evaluation_mode") != "answer_blind"
                or row.get("official_answer_seen") is not False
                or str(row.get("phase") or "solve") != "solve"
            ):
                _error(f"problem-only bundle record {record_id} is not answer-blind")
            by_target[expected_target] = row
        row = by_target.get(target_rel)
        if row is None:
            _error(f"native target {target_rel!r} has no exact problem-only record")
        record_id = str(row["id"])
        raw_outputs = row.get("requested_outputs")
        if not isinstance(raw_outputs, list) or not raw_outputs:
            _error(f"bundle {record_id} has no requested outputs")
        requested = [
            _validate_requested_output(item, record_id=record_id, index=index)
            for index, item in enumerate(raw_outputs, start=1)
        ]
        ids = [item["id"] for item in requested]
        if len(set(ids)) != len(ids):
            _error(f"bundle {record_id} has duplicate requested output ids")
        reporting_policy = row.get("reporting_policy")
        if not isinstance(reporting_policy, Mapping) or not reporting_policy:
            _error(f"bundle {record_id} has no global reporting policy")
        measurement_policy = row.get("measurement_policy")
        if not isinstance(measurement_policy, Mapping) or not measurement_policy:
            _error(f"bundle {record_id} has no measurement policy")
        candidate_domain_policy = row.get("candidate_domain_policy")
        if (
            not isinstance(candidate_domain_policy, Mapping)
            or not candidate_domain_policy
        ):
            _error(f"bundle {record_id} has no candidate-domain policy")
        previous_parts = row.get("previous_parts")
        if not isinstance(previous_parts, list):
            _error(f"bundle {record_id} previous_parts is not a list")
        image_assets = _record_assets(
            row,
            project_path=root,
            manifest_assets=isolation_manifest["assets"],
        )
        return {
            "required": True,
            "valid": True,
            "target": target_rel,
            "record_id": record_id,
            "requested_outputs": requested,
            "reporting_policy": copy.deepcopy(dict(reporting_policy)),
            "bundle_sha256": _sha256(bundle_path),
            "manifest_sha256": manifest_sha256,
            "image_assets": list(image_assets),
            "previous_parts_count": len(previous_parts),
            "pinned_library_packages": list(pinned_library_packages),
            # Controller-only resolver input. Prompt rendering deliberately
            # projects a fixed public subset and never exposes this path.
            "_project_path": str(root),
            "problem_evidence": {
                "question": copy.deepcopy(row.get("question")),
                "current_question": copy.deepcopy(row.get("current_question")),
                "shared_context": copy.deepcopy(row.get("shared_context")),
                "previous_parts": copy.deepcopy(previous_parts),
                "measurement_policy": copy.deepcopy(dict(measurement_policy)),
                "candidate_domain_policy": copy.deepcopy(
                    dict(candidate_domain_policy)
                ),
            },
            "errors": [],
        }
    except _CertificateError as exc:
        return {
            "required": True,
            "valid": False,
            "target": target_rel,
            "errors": [str(exc)],
        }


def _schema_example_contract() -> dict[str, Any]:
    """Small problem-only contract used to render the static policy example."""
    return {
        "required": True,
        "valid": True,
        "target": "IChO2026Problems/problem_example.lean",
        "record_id": "example",
        "requested_outputs": [{
            "id": "requested_output_id",
            "kind": "numeric",
            "source_requirement": "copy the exact requested-output text",
            "unit": "mol",
            "reporting_policy": {
                "kind": "significant_figures",
                "digits": 3,
            },
        }],
        "reporting_policy": {
            "intermediate_rounding": "forbidden",
            "final_precision": {
                "kind": "per_requested_output",
                "source": "requested_outputs",
            },
            "tie_rule": "half_away_from_zero",
        },
        "image_assets": [{"path": "problem-page.png", "sha256": "0" * 64}],
        "previous_parts_count": 1,
        "pinned_library_packages": list(_PINNED_PACKAGES),
        "problem_evidence": {
            "question": "problem-only question",
            "current_question": "problem-only current question",
            "shared_context": "problem-only shared context",
            "previous_parts": [{"id": "prior"}],
            "measurement_policy": {"printed_constants": "exact"},
            "candidate_domain_policy": {"underdetermined": "report"},
        },
        "errors": [],
    }


def build_independent_rederivation_example(
    contract: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Build one compact, validator-compatible certificate example.

    The policy prompt and tests share this builder so the documented exact-key
    schema cannot drift independently from machine validation.  Values in a
    live certificate must be independently derived; this function supplies
    only compact structural examples and exact bundle-bound fields.
    """
    selected = contract or _schema_example_contract()
    outputs = selected.get("requested_outputs")
    if not isinstance(outputs, list) or not outputs:
        raise ValueError("semantic Review example requires requested outputs")
    global_policy = selected.get("reporting_policy")
    if not isinstance(global_policy, Mapping) or not global_policy:
        raise ValueError("semantic Review example requires a global policy")
    rendered_outputs: list[dict[str, Any]] = []
    for index, expected in enumerate(outputs, start=1):
        if not isinstance(expected, Mapping):
            raise ValueError("semantic Review example output is invalid")
        unit = str(expected.get("unit") or "")
        rendered_outputs.append({
            "id": str(expected.get("id") or ""),
            "kind": str(expected.get("kind") or ""),
            "source_requirement": str(expected.get("source_requirement") or ""),
            "quantity_definition": "concise exact meaning derived from the source",
            "process_scope": {
                "kind": "overall",
                "description": "overall quantity across the stated process",
            },
            "basis": {
                "status": "not_applicable",
                "numerator": "not_applicable",
                "denominator": "not_applicable",
                "mass_or_composition_basis": "not_applicable",
            },
            "constants": [],
            "dependencies": [],
            "branch_conditions": [],
            "unit": unit,
            "raw_result": {
                "value_or_expression": f"independently_derived_expression_{index}",
                "exact_unrounded": True,
                "derivation": "concise substitution into the source-grounded relation",
            },
            "reporting": {
                "policy": copy.deepcopy(dict(expected.get("reporting_policy") or {})),
                "global_policy": copy.deepcopy(dict(global_policy)),
                "application": "apply the bundle rule once to the final raw result",
            },
            "lean_carriers": {
                "inputs": [f"NativeReview.Output{index}.sourceInputs"],
                "relations": [f"NativeReview.Output{index}.governingRelation"],
                "raw_result": [f"NativeReview.Output{index}.rawResult"],
                "reported_result": [f"NativeReview.Output{index}.reportedResult"],
            },
            "semantic_card_comparison": {
                "status": "matched",
                "evidence": "all semantic-card fields match the source-first derivation",
            },
            "lean_statement_comparison": {
                "status": "matched",
                "evidence": "all Lean carriers match the source-first derivation",
            },
            "source_locators": [{
                "kind": "problem_text",
                "reference": "current_question",
            }],
            "evidence": "source-first derivation agrees with the card and Lean contract",
        })
    return {
        "schema_version": SCHEMA_VERSION,
        "method": "source_first_without_lean",
        "ambiguity": "clear",
        "requested_outputs": rendered_outputs,
    }


def render_independent_rederivation_instructions(
    contract: Mapping[str, Any] | None = None,
) -> str:
    """Render the canonical compact schema for the project Review policy."""
    selected = contract or _schema_example_contract()
    configured_packages = [
        package for package in selected.get("pinned_library_packages") or []
        if package in _PINNED_PACKAGES
    ]
    example = {
        "independent_rederivation": build_independent_rederivation_example(selected)
    }
    exact_shape_registry = {
        "independent_rederivation": sorted(_TOP_FIELDS),
        "requested_outputs[]": sorted(_OUTPUT_FIELDS),
        "process_scope": sorted(_PROCESS_SCOPE_FIELDS),
        "basis": sorted(_BASIS_FIELDS),
        "constants[]": sorted(_CONSTANT_FIELDS),
        "dependencies[]": sorted(_DEPENDENCY_FIELDS),
        "branch_conditions[]": sorted(_BRANCH_CONDITION_FIELDS),
        "raw_result": sorted(_RAW_RESULT_FIELDS),
        "reporting": sorted(_REPORTING_FIELDS),
        "lean_carriers": sorted(_LEAN_CARRIER_FIELDS),
        "semantic_card_comparison": sorted(_COMPARISON_FIELDS),
        "lean_statement_comparison": sorted(_COMPARISON_FIELDS),
        "every_source_locator": sorted(_LOCATOR_FIELDS),
    }
    return (
        "Use the exact compact schema below. Replace example semantic values "
        "with your source-first derivation, and copy id/kind/source_requirement, "
        "unit, per-output reporting.policy, and reporting.global_policy exactly "
        "from the matching problem-only bundle row. Do not add or omit keys. "
        "Empty constants/dependencies/branch_conditions arrays explicitly mean "
        "none; otherwise each entry carries its own problem-only source locator. "
        "The controller-owned exact object-key registry is "
        + json.dumps(
            exact_shape_registry,
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
        + ". Fixed structural values: schema_version must be the JSON integer 1 "
        "(not true or 1.0); method must be source_first_without_lean; ambiguity "
        "must be clear. process_scope.kind must be exactly one of "
        + json.dumps(sorted(_PROCESS_SCOPES), ensure_ascii=False)
        + "; basis.status must be exactly one of "
        + json.dumps(sorted(_BASIS_STATUSES), ensure_ascii=False)
        + "; dependencies[].kind must be exactly one of "
        + json.dumps(sorted(_DEPENDENCY_KINDS), ensure_ascii=False)
        + "; and every source_locator.kind must be exactly one of "
        + json.dumps(sorted(_LOCATOR_KINDS), ensure_ascii=False)
        + ". Both comparison statuses must be matched, and "
        "raw_result.exact_unrounded must be the JSON boolean true. Write "
        "unit=dimensionless for a unitless constant. The field role is forbidden. "
        "Do not add role or any other extra field to any schema object.\n\n"
        "```json\n"
        + json.dumps(example, ensure_ascii=False, indent=2, sort_keys=True)
        + "\n```\n\n"
        "Every requested output must appear exactly once and in bundle order. "
        "Allowed locator kinds are problem_text, problem_image, previous_parts, "
        "and pinned_library. A problem image reference is its exact allowed asset "
        "path plus one #safe-fragment; the controller validates attachment/path "
        "binding and fragment syntax, not the fragment's semantic region. A "
        "previous_parts reference may be either a bare "
        "ASCII-decimal zero-based index such as 0, which the controller "
        "canonicalizes to previous_parts[0], or the canonical "
        "previous_parts[index][.field] form; the index must exist. A pinned "
        "library reference must be a safe fully-qualified Lean declaration "
        "whose defining module is verified in one of the configured sealed "
        "packages "
        + json.dumps(configured_packages, ensure_ascii=True)
        + "; declaration namespace text alone is never sufficient. "
        "A problem_text reference must be either an exact scalar root from "
        + json.dumps(list(_PROBLEM_TEXT_SCALAR_ROOTS), ensure_ascii=True)
        + " (optionally followed by exactly one # fragment matching "
        + _LOCATOR_FRAGMENT_FORMAT
        + "), an existing full dot "
        "chain rooted at "
        + json.dumps(list(_PROBLEM_TEXT_STRUCTURED_ROOTS), ensure_ascii=True)
        + ", or requested_outputs[existing_zero_based_index].existing_field "
        "with the entire reference consumed. Prefix collisions and nonexistent "
        "fields or indexes are invalid. Locator references must use only facts already visible in the "
        "problem-only contract; never invent a field, index, asset, or declaration. "
        f"Keep each string at most {MAX_TEXT_CHARS} characters, each JSON value "
        f"at most {MAX_JSON_VALUE_CHARS} characters, each list at most "
        f"{MAX_ITEMS_PER_FIELD} items, each requested-output object at most "
        f"{MAX_OUTPUT_BYTES} UTF-8 bytes, and the complete independent_rederivation "
        f"at most {MAX_CERTIFICATE_BYTES} UTF-8 bytes. "
        f"Use at most {MAX_PINNED_DECLARATIONS} distinct pinned-library "
        f"declarations spanning at most {MAX_PINNED_CANDIDATE_MODULES} defining "
        "modules in one certificate. "
        "URLs, absolute paths, '..', grader data, and external workspaces are "
        "forbidden. Keep evidence concise. Raw values are checked for a source "
        "derivation and exact-unrounded attestation, never against an answer key. "
        "Both comparison statuses are semantic attestations and must be matched "
        "for a passing verdict."
    )


def render_native_problem_contract_prompt(contract: Mapping[str, Any]) -> str:
    """Render only the problem evidence available to one native Review worker."""
    if not contract.get("valid"):
        return (
            "NATIVE PROBLEM-ONLY CONTRACT IS INVALID: "
            + json.dumps(contract.get("errors") or [], ensure_ascii=False)
        )
    payload = {
        "record_id": contract.get("record_id"),
        "target": contract.get("target"),
        "evidence_binding": {
            "problem_bundle_sha256": contract.get("bundle_sha256"),
            "isolation_manifest_sha256": contract.get("manifest_sha256"),
        },
        "problem_evidence": contract.get("problem_evidence"),
        "requested_outputs": contract.get("requested_outputs"),
        "reporting_policy": contract.get("reporting_policy"),
        "problem_images": contract.get("image_assets"),
    }
    return (
        "NATIVE ANSWER-BLIND PROBLEM CONTRACT (only source of problem facts):\n"
        + json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)
        + "\nOpen and inspect every listed problem image from the workspace's "
        "icho_2026_source/image directory. First fix an independent derivation "
        "using only this problem contract, those images, and pinned general laws. "
        "Do not inspect the Semantic Card, Lean target, task results, blueprint, "
        "or traces until that derivation is fixed. Never seek or read an official "
        "answer, grader, solution, rubric, candidate artifact, or prior run."
    )


def _exact_fields(value: Any, expected: set[str], *, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        _error(f"{label} must be an object")
    missing = sorted(expected - set(value))
    extra = sorted(set(value) - expected)
    if missing or extra:
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        _error(f"{label} has invalid fields: {'; '.join(details)}")
    return value


def build_native_schema_feedback(error: str) -> dict[str, Any] | None:
    """Return bounded structural retry feedback for a trusted validator error.

    The rejected certificate and the raw error detail are deliberately not
    returned.  Only paths with controller-owned exact-key/enum definitions and
    fixed, problem-independent locator/size grammars are recognized, so problem
    text, answer-shaped values, locator values, and prior derivations cannot be
    reflected into a later model prompt.
    """
    invalid_fields_suffix = " has invalid fields: "
    if invalid_fields_suffix in error:
        path, _separator, detail = error.partition(invalid_fields_suffix)
        for pattern, exact_keys in _SCHEMA_OBJECTS:
            if re.fullmatch(pattern, path) is None:
                continue
            if detail.startswith("missing ") and "; unexpected " in detail:
                issue = "missing_and_unexpected_keys"
            elif detail.startswith("missing "):
                issue = "missing_required_keys"
            elif detail.startswith("unexpected "):
                issue = "unexpected_keys"
            else:
                return None
            return {
                "error_kind": "schema_validation",
                "issue": issue,
                "field_path": path,
                "required_exact_keys": sorted(exact_keys),
            }

    object_suffix = " must be an object"
    if error.endswith(object_suffix):
        path = error.removesuffix(object_suffix)
        if any(re.fullmatch(pattern, path) for pattern, _keys in _SCHEMA_OBJECTS):
            return {
                "error_kind": "schema_validation",
                "issue": "wrong_type",
                "field_path": path,
                "expected_type": "object",
            }

    list_suffix = " must be a list"
    if error.endswith(list_suffix):
        path = error.removesuffix(list_suffix)
        if any(re.fullmatch(pattern, path) for pattern in _SCHEMA_LISTS):
            return {
                "error_kind": "schema_validation",
                "issue": "wrong_type",
                "field_path": path,
                "expected_type": "list",
            }

    enum_rules: tuple[tuple[str, list[Any]], ...] = (
        (
            rf"{_SCHEMA_OUTPUT}\.process_scope\.kind",
            sorted(_PROCESS_SCOPES),
        ),
        (rf"{_SCHEMA_OUTPUT}\.basis\.status", sorted(_BASIS_STATUSES)),
        (
            rf"{_SCHEMA_OUTPUT}\.dependencies\[{_SCHEMA_INDEX}\]\.kind",
            sorted(_DEPENDENCY_KINDS),
        ),
        (
            rf"{_SCHEMA_OUTPUT}\.(?:constants|dependencies|branch_conditions)"
            rf"\[{_SCHEMA_INDEX}\]\.source_locator\.kind",
            sorted(_LOCATOR_KINDS),
        ),
        (
            rf"{_SCHEMA_OUTPUT}\.source_locators\[{_SCHEMA_INDEX}\]\.kind",
            sorted(_LOCATOR_KINDS),
        ),
    )
    for suffix, issue in (
        (" is unsupported", "unsupported_enum"),
        (" must be a string", "wrong_type"),
    ):
        if not error.endswith(suffix):
            continue
        path = error.removesuffix(suffix)
        for pattern, allowed_values in enum_rules:
            if re.fullmatch(pattern, path) is None:
                continue
            feedback = {
                "error_kind": "schema_validation",
                "issue": issue,
                "field_path": path,
                "allowed_values": allowed_values,
            }
            if issue == "wrong_type":
                feedback["expected_type"] = "string"
            return feedback

    if error == "independent_rederivation.schema_version is unsupported":
        return {
            "error_kind": "schema_validation",
            "issue": "wrong_fixed_value",
            "field_path": "independent_rederivation.schema_version",
            "expected_type": "integer",
            "allowed_values": [SCHEMA_VERSION],
        }
    if error == (
        "independent_rederivation.method must be source_first_without_lean"
    ):
        return {
            "error_kind": "schema_validation",
            "issue": "wrong_fixed_value",
            "field_path": "independent_rederivation.method",
            "expected_type": "string",
            "allowed_values": ["source_first_without_lean"],
        }

    string_suffix = " must be a string"
    if error.endswith(string_suffix):
        path = error.removesuffix(string_suffix)
        if any(re.fullmatch(pattern, path) for pattern in _SCHEMA_STRINGS):
            return {
                "error_kind": "schema_validation",
                "issue": "wrong_type",
                "field_path": path,
                "expected_type": "string",
            }

    locator_rules: tuple[tuple[str, str], ...] = (
        (
            " contains an external or unsafe locator",
            "safe_relative_problem_locator",
        ),
        (
            " must reference an allowed problem image as path#region",
            "exact_problem_image_path#region",
        ),
        (
            " does not identify an available previous_parts entry",
            _PREVIOUS_PART_FORMAT,
        ),
        (
            " is not a pinned Mathlib/Physlib/CRNT declaration",
            _PINNED_LIBRARY_FORMAT,
        ),
        (
            " does not identify a problem-only text field",
            _PROBLEM_TEXT_FORMAT,
        ),
    )
    for suffix, expected_format in locator_rules:
        if not error.endswith(suffix):
            continue
        path = error.removesuffix(suffix)
        locator_path = path.removesuffix(".reference")
        if re.fullmatch(_SCHEMA_LOCATOR, locator_path) is None:
            return None
        return {
            "error_kind": "schema_validation",
            "issue": "invalid_locator_binding",
            "field_path": path,
            "expected_format": expected_format,
        }

    output_size_suffix = " exceeds the compact Review certificate limit"
    if error.endswith(output_size_suffix):
        path = error.removesuffix(output_size_suffix)
        if re.fullmatch(_SCHEMA_OUTPUT, path) is not None:
            return {
                "error_kind": "schema_validation",
                "issue": "payload_too_large",
                "field_path": path,
                "max_bytes": MAX_OUTPUT_BYTES,
            }
    if error == "independent_rederivation exceeds the compact certificate limit":
        return {
            "error_kind": "schema_validation",
            "issue": "payload_too_large",
            "field_path": "independent_rederivation",
            "max_bytes": MAX_CERTIFICATE_BYTES,
        }
    if error == (
        "independent_rederivation has too many distinct pinned library declarations"
    ):
        return {
            "error_kind": "schema_validation",
            "issue": "too_many_distinct_pinned_declarations",
            "field_path": "independent_rederivation",
            "max_items": MAX_PINNED_DECLARATIONS,
        }
    return None


def _text(value: Any, *, label: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        _error(f"{label} must be a string")
    normalized = value.strip()
    if (not normalized and not allow_empty) or len(normalized) > MAX_TEXT_CHARS:
        _error(f"{label} is empty or too long")
    return normalized


def _plain_reference(value: Any, *, label: str) -> str:
    text = _text(value, label=label)
    if "\x00" in text or "\\" in text or "://" in text or text.startswith("/"):
        _error(f"{label} contains an external or unsafe locator")
    if ".." in Path(text.split("#", 1)[0]).parts:
        _error(f"{label} contains an external or unsafe locator")
    return text


def _field_chain_exists(value: Any, suffix: str) -> bool:
    if not suffix or not suffix.startswith("."):
        return False
    cursor = value
    for field in suffix[1:].split("."):
        if not isinstance(cursor, Mapping) or field not in cursor:
            return False
        cursor = cursor[field]
    return True


def _problem_text_reference_is_bound(
    reference: str,
    contract: Mapping[str, Any],
) -> bool:
    base, marker, fragment = reference.partition("#")
    evidence = contract.get("problem_evidence")
    if not isinstance(evidence, Mapping):
        return False
    scalar_value = evidence.get(base)
    scalar_is_bound = isinstance(scalar_value, str) and bool(scalar_value.strip())
    if marker:
        return (
            base in _PROBLEM_TEXT_SCALAR_ROOTS
            and base in evidence
            and scalar_is_bound
            and _LOCATOR_FRAGMENT_RE.fullmatch(fragment) is not None
        )
    if base in _PROBLEM_TEXT_SCALAR_ROOTS:
        return base in evidence and scalar_is_bound

    structured = _STRUCTURED_TEXT_REFERENCE_RE.fullmatch(base)
    if structured is not None:
        root = structured.group("root")
        source = (
            contract.get("reporting_policy")
            if root == "reporting_policy"
            else evidence.get(root)
        )
        return _field_chain_exists(source, structured.group("suffix"))

    requested = _REQUESTED_OUTPUT_TEXT_REFERENCE_RE.fullmatch(base)
    if requested is None:
        return False
    outputs = contract.get("requested_outputs")
    try:
        index = int(requested.group("index"))
    except ValueError:
        return False
    return (
        isinstance(outputs, list)
        and 0 <= index < len(outputs)
        and _field_chain_exists(outputs[index], requested.group("suffix"))
    )


def _locator(
    value: Any, *, label: str, contract: Mapping[str, Any],
) -> dict[str, str]:
    raw = _exact_fields(value, _LOCATOR_FIELDS, label=label)
    kind = _text(raw.get("kind"), label=f"{label}.kind")
    reference = _plain_reference(raw.get("reference"), label=f"{label}.reference")
    if kind not in _LOCATOR_KINDS:
        _error(f"{label}.kind is unsupported")
    if kind == "problem_image":
        asset, marker, region = reference.partition("#")
        allowed_assets = {
            str(item.get("path") or "")
            for item in contract.get("image_assets") or []
            if isinstance(item, Mapping)
        }
        if (
            not marker
            or _LOCATOR_FRAGMENT_RE.fullmatch(region) is None
            or asset not in allowed_assets
        ):
            _error(
                f"{label}.reference must reference an allowed problem image as path#region"
            )
    elif kind == "previous_parts":
        bare_match = _BARE_PREVIOUS_PART_RE.fullmatch(reference)
        match = _PREVIOUS_PART_RE.fullmatch(reference)
        index_text = (
            reference if bare_match is not None
            else match.group("index") if match is not None
            else ""
        )
        try:
            index = int(index_text)
            previous_parts_count = int(contract.get("previous_parts_count") or 0)
        except (TypeError, ValueError):
            index = -1
            previous_parts_count = 0
        if (
            not index_text
            or index < 0
            or index >= previous_parts_count
        ):
            _error(
                f"{label}.reference does not identify an available previous_parts entry"
            )
        suffix = match.group("suffix") if match is not None else ""
        previous_parts = (
            contract.get("problem_evidence", {}).get("previous_parts")
            if isinstance(contract.get("problem_evidence"), Mapping)
            else None
        )
        if (
            suffix
            and (
                not isinstance(previous_parts, list)
                or index >= len(previous_parts)
                or not _field_chain_exists(previous_parts[index], suffix)
            )
        ):
            _error(
                f"{label}.reference does not identify an available previous_parts entry"
            )
        reference = f"previous_parts[{index}]{suffix}"
    elif kind == "pinned_library":
        verified = contract.get("_verified_pinned_library_declarations")
        if (
            _LEAN_NAME_RE.fullmatch(reference) is None
            or not isinstance(verified, (set, frozenset))
            or reference not in verified
        ):
            _error(
                f"{label}.reference is not a pinned Mathlib/Physlib/CRNT declaration"
            )
    elif not _problem_text_reference_is_bound(reference, contract):
        _error(f"{label}.reference does not identify a problem-only text field")
    return {"kind": kind, "reference": reference}


def _locators(
    value: Any, *, label: str, contract: Mapping[str, Any],
) -> list[dict[str, str]]:
    value = _bounded_list(value, label=label, allow_empty=False)
    return [
        _locator(item, label=f"{label}[{index}]", contract=contract)
        for index, item in enumerate(value)
    ]


def _comparison(value: Any, *, label: str) -> dict[str, str]:
    raw = _exact_fields(value, _COMPARISON_FIELDS, label=label)
    status = _text(raw.get("status"), label=f"{label}.status")
    evidence = _text(raw.get("evidence"), label=f"{label}.evidence")
    if status != "matched":
        _error(f"{label}.status must be matched for a passing Review")
    return {"status": status, "evidence": evidence}


def _json_value(value: Any, *, label: str) -> Any:
    if value is None or isinstance(value, bool):
        _error(f"{label} must be a source-derived value or symbolic expression")
    try:
        payload = json.dumps(value, ensure_ascii=False, sort_keys=True)
    except (TypeError, ValueError):
        _error(f"{label} is not JSON serializable")
    if not payload or len(payload) > MAX_JSON_VALUE_CHARS or value in ("", [], {}):
        _error(f"{label} is empty or too long")
    return copy.deepcopy(value)


def _bounded_list(value: Any, *, label: str, allow_empty: bool = True) -> list[Any]:
    if not isinstance(value, list):
        _error(f"{label} must be a list")
    if (not allow_empty and not value) or len(value) > MAX_ITEMS_PER_FIELD:
        _error(f"{label} has an invalid item count")
    return value


def _pinned_references(outputs: list[Any]) -> set[str]:
    """Collect only safe pinned names from the exact locator-bearing fields."""
    references: set[str] = set()
    for output in outputs:
        if not isinstance(output, Mapping):
            continue
        locator_values: list[Any] = []
        for field in ("constants", "dependencies", "branch_conditions"):
            items = output.get(field)
            if isinstance(items, list):
                locator_values.extend(
                    item.get("source_locator")
                    for item in items
                    if isinstance(item, Mapping)
                )
        direct = output.get("source_locators")
        if isinstance(direct, list):
            locator_values.extend(direct)
        for locator in locator_values:
            if not isinstance(locator, Mapping) or locator.get("kind") != "pinned_library":
                continue
            reference = locator.get("reference")
            if isinstance(reference, str):
                normalized = reference.strip()
                if _LEAN_NAME_RE.fullmatch(normalized) is not None:
                    references.add(normalized)
    return references


def _validate_output(
    raw_value: Any,
    *,
    expected: Mapping[str, Any],
    all_output_ids: set[str],
    contract: Mapping[str, Any],
    index: int,
) -> None:
    label = f"independent_rederivation.requested_outputs[{index}]"
    raw = _exact_fields(raw_value, _OUTPUT_FIELDS, label=label)
    try:
        output_bytes = len(
            json.dumps(raw, ensure_ascii=False, sort_keys=True).encode("utf-8")
        )
    except (TypeError, ValueError):
        _error(f"{label} is not JSON serializable")
    if output_bytes > MAX_OUTPUT_BYTES:
        _error(f"{label} exceeds the compact Review certificate limit")
    for field in ("id", "kind", "source_requirement"):
        actual = _text(raw.get(field), label=f"{label}.{field}")
        if actual != expected.get(field):
            _error(f"{label}.{field} does not exactly match the problem bundle")

    _text(raw.get("quantity_definition"), label=f"{label}.quantity_definition")

    scope = _exact_fields(
        raw.get("process_scope"), _PROCESS_SCOPE_FIELDS,
        label=f"{label}.process_scope",
    )
    scope_kind = _text(scope.get("kind"), label=f"{label}.process_scope.kind")
    if scope_kind not in _PROCESS_SCOPES:
        _error(f"{label}.process_scope.kind is unsupported")
    _text(scope.get("description"), label=f"{label}.process_scope.description")

    basis = _exact_fields(
        raw.get("basis"),
        _BASIS_FIELDS,
        label=f"{label}.basis",
    )
    basis_status = _text(basis.get("status"), label=f"{label}.basis.status")
    if basis_status not in _BASIS_STATUSES:
        _error(f"{label}.basis.status is unsupported")
    for field in ("numerator", "denominator", "mass_or_composition_basis"):
        text = _text(basis.get(field), label=f"{label}.basis.{field}")
        if basis_status == "not_applicable" and text != "not_applicable":
            _error(f"{label}.basis.{field} must explicitly be not_applicable")

    constant_items = _bounded_list(
        raw.get("constants"), label=f"{label}.constants"
    )
    for item_index, item in enumerate(constant_items):
        item_label = f"{label}.constants[{item_index}]"
        item_map = _exact_fields(
            item, _CONSTANT_FIELDS, label=item_label,
        )
        _text(item_map.get("name"), label=f"{item_label}.name")
        _json_value(item_map.get("value"), label=f"{item_label}.value")
        _text(item_map.get("unit"), label=f"{item_label}.unit")
        normalized_locator = _locator(
            item_map.get("source_locator"),
            label=f"{item_label}.source_locator", contract=contract,
        )
        if isinstance(item, dict):
            item["source_locator"] = normalized_locator

    dependency_items = _bounded_list(
        raw.get("dependencies"), label=f"{label}.dependencies"
    )
    for item_index, item in enumerate(dependency_items):
        item_label = f"{label}.dependencies[{item_index}]"
        item_map = _exact_fields(
            item, _DEPENDENCY_FIELDS,
            label=item_label,
        )
        dependency_kind = _text(item_map.get("kind"), label=f"{item_label}.kind")
        reference = _text(item_map.get("reference"), label=f"{item_label}.reference")
        if dependency_kind not in _DEPENDENCY_KINDS:
            _error(f"{item_label}.kind is unsupported")
        if dependency_kind == "requested_output" and reference not in all_output_ids:
            _error(f"{item_label}.reference is not a requested output id")
        _text(item_map.get("relation"), label=f"{item_label}.relation")
        normalized_locator = _locator(
            item_map.get("source_locator"),
            label=f"{item_label}.source_locator", contract=contract,
        )
        if isinstance(item, dict):
            item["source_locator"] = normalized_locator

    branch_items = _bounded_list(
        raw.get("branch_conditions"), label=f"{label}.branch_conditions"
    )
    for item_index, item in enumerate(branch_items):
        item_label = f"{label}.branch_conditions[{item_index}]"
        item_map = _exact_fields(
            item, _BRANCH_CONDITION_FIELDS, label=item_label,
        )
        _text(item_map.get("condition"), label=f"{item_label}.condition")
        normalized_locator = _locator(
            item_map.get("source_locator"),
            label=f"{item_label}.source_locator", contract=contract,
        )
        if isinstance(item, dict):
            item["source_locator"] = normalized_locator

    unit_value = _text(
        raw.get("unit"), label=f"{label}.unit", allow_empty=True,
    )
    if unit_value != expected.get("unit"):
        _error(f"{label}.unit does not exactly match the problem bundle")

    raw_result = _exact_fields(
        raw.get("raw_result"),
        _RAW_RESULT_FIELDS,
        label=f"{label}.raw_result",
    )
    _json_value(
        raw_result.get("value_or_expression"),
        label=f"{label}.raw_result.value_or_expression",
    )
    if raw_result.get("exact_unrounded") is not True:
        _error(f"{label}.raw_result.exact_unrounded must be true")
    _text(raw_result.get("derivation"), label=f"{label}.raw_result.derivation")

    reporting = _exact_fields(
        raw.get("reporting"), _REPORTING_FIELDS,
        label=f"{label}.reporting",
    )
    if reporting.get("policy") != expected.get("reporting_policy"):
        _error(f"{label}.reporting.policy does not exactly match the bundle")
    if reporting.get("global_policy") != contract.get("reporting_policy"):
        _error(f"{label}.reporting.global_policy does not exactly match the bundle")
    _text(reporting.get("application"), label=f"{label}.reporting.application")

    carriers = _exact_fields(
        raw.get("lean_carriers"),
        _LEAN_CARRIER_FIELDS,
        label=f"{label}.lean_carriers",
    )
    for field in ("inputs", "relations", "raw_result", "reported_result"):
        names = carriers.get(field)
        names = _bounded_list(
            names, label=f"{label}.lean_carriers.{field}", allow_empty=False,
        )
        if any(
            not isinstance(name, str) or _LEAN_NAME_RE.fullmatch(name.strip()) is None
            for name in names
        ):
            _error(f"{label}.lean_carriers.{field} has an unsafe declaration")

    _comparison(
        raw.get("semantic_card_comparison"),
        label=f"{label}.semantic_card_comparison",
    )
    _comparison(
        raw.get("lean_statement_comparison"),
        label=f"{label}.lean_statement_comparison",
    )
    normalized_locators = _locators(
        raw.get("source_locators"),
        label=f"{label}.source_locators",
        contract=contract,
    )
    if isinstance(raw_value, dict):
        raw_value["source_locators"] = normalized_locators
    _text(raw.get("evidence"), label=f"{label}.evidence")


def validate_independent_rederivation(
    review: Mapping[str, Any],
    contract: Mapping[str, Any] | None,
) -> tuple[str, dict[str, Any]]:
    """Validate one passing native certificate, returning error + normalized.

    Non-native callers pass ``None`` and retain the historical Review schema.
    An invalid native preparation contract always fails closed.
    """
    if contract is None:
        return "", {}
    errors = contract.get("errors")
    errors = errors if isinstance(errors, list) else []
    if not contract.get("valid") or errors:
        detail = "; ".join(str(item) for item in errors) or "unknown contract error"
        return f"native semantic Review contract is invalid: {detail}", {}
    try:
        raw_source = _exact_fields(
            review.get("independent_rederivation"),
            _TOP_FIELDS,
            label="independent_rederivation",
        )
        if (
            type(raw_source.get("schema_version")) is not int
            or raw_source.get("schema_version") != SCHEMA_VERSION
        ):
            _error("independent_rederivation.schema_version is unsupported")
        if raw_source.get("method") != "source_first_without_lean":
            _error("independent_rederivation.method must be source_first_without_lean")
        if raw_source.get("ambiguity") != "clear":
            _error("independent_rederivation.ambiguity must be clear for a passing Review")
        try:
            certificate_bytes = len(
                json.dumps(raw_source, ensure_ascii=False, sort_keys=True).encode("utf-8")
            )
        except (TypeError, ValueError):
            _error("independent_rederivation is not JSON serializable")
        if certificate_bytes > MAX_CERTIFICATE_BYTES:
            _error("independent_rederivation exceeds the compact certificate limit")
        raw = copy.deepcopy(dict(raw_source))
        expected_outputs = contract.get("requested_outputs")
        if not isinstance(expected_outputs, list):
            _error("independent_rederivation requested output inventory is invalid")
        actual_outputs = _bounded_list(
            raw.get("requested_outputs"),
            label="independent_rederivation.requested_outputs",
        )
        for index, actual in enumerate(actual_outputs):
            _exact_fields(
                actual,
                _OUTPUT_FIELDS,
                label=f"independent_rederivation.requested_outputs[{index}]",
            )
        expected_ids = [str(item.get("id") or "") for item in expected_outputs]
        actual_ids = [
            str(item.get("id") or "") if isinstance(item, Mapping) else ""
            for item in actual_outputs
        ]
        if actual_ids != expected_ids:
            _error(
                "independent_rederivation must cover the exact ordered requested output ids"
            )
        package_values = contract.get("pinned_library_packages")
        if (
            not isinstance(package_values, list)
            or not package_values
            or any(
                not isinstance(package, str) or package not in _PINNED_PACKAGES
                for package in package_values
            )
            or len(set(package_values)) != len(package_values)
        ):
            _error("native pinned library package inventory is invalid")
        pinned_references = _pinned_references(actual_outputs)
        if len(pinned_references) > MAX_PINNED_DECLARATIONS:
            _error(
                "independent_rederivation has too many distinct pinned library declarations"
            )
        validation_contract = dict(contract)
        project_value = contract.get("_project_path")
        verified = (
            _verified_pinned_library_declarations(
                Path(project_value), tuple(package_values), pinned_references,
            )
            if pinned_references and isinstance(project_value, str) and project_value
            else frozenset()
        )
        validation_contract["_verified_pinned_library_declarations"] = verified
        all_output_ids = set(expected_ids)
        for index, (actual, expected) in enumerate(
            zip(actual_outputs, expected_outputs, strict=True)
        ):
            _validate_output(
                actual,
                expected=expected,
                all_output_ids=all_output_ids,
                contract=validation_contract,
                index=index,
            )
        return "", raw
    except _CertificateError as exc:
        return str(exc), {}


__all__ = [
    "BUNDLE_REL",
    "NATIVE_PROFILE",
    "SCHEMA_VERSION",
    "build_independent_rederivation_example",
    "build_native_schema_feedback",
    "build_native_semantic_review_contract",
    "render_independent_rederivation_instructions",
    "render_native_problem_contract_prompt",
    "validate_independent_rederivation",
]
