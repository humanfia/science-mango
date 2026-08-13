"""Project-level domain-library settings for physics-style formalization loops.

The original physics pipeline assumed every project used Mathlib plus Physlib.
Quantum benchmarks use the same formalization/review/proof routing, but expose
their domain API through benchmark-local libraries such as ``QAlgBench.Base``
or ``QITBench.Base``.  This module keeps the legacy defaults while allowing a
project to describe the exact imports and LeanExplore package filters in
``.archon/config.json``.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from archon.commands.tooling.project_config import load_project_config


DEFAULT_PHYSICS_PREFLIGHT_IMPORTS: tuple[str, ...] = (
    "Mathlib",
    "Physlib.Units.Basic",
    "Physlib.Units.Dimension",
    "Physlib.Units.WithDim.Basic",
    "Physlib.Units.WithDim.Mass",
    "Physlib.Units.WithDim.Velocity",
    "Physlib.Units.WithDim.Energy",
    "Physlib.SpaceAndTime.Space.Basic",
    "Physlib.SpaceAndTime.Time.Basic",
    "Physlib.SpaceAndTime.Space.Derivatives.Basic",
    "Physlib.Mathematics.InnerProductSpace.Basic",
    "Physlib.ClassicalMechanics.Basic",
    "Physlib.ClassicalMechanics.EulerLagrange",
    "Physlib.ClassicalMechanics.HarmonicOscillator.Basic",
    "Physlib.ClassicalMechanics.RigidBody.Basic",
    "Physlib.Electromagnetism.Basic",
    "Physlib.Electromagnetism.Dynamics.Basic",
    "Physlib.Thermodynamics.Basic",
    "Physlib.Thermodynamics.Temperature.Basic",
    "Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic",
    "Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic",
    "Physlib.Relativity.LorentzGroup.Basic",
    "Physlib.Relativity.Special.ProperTime",
)


def _strings(value: Any, default: Iterable[str]) -> tuple[str, ...]:
    if value is None:
        value = default
    if isinstance(value, str):
        value = [value]
    if not isinstance(value, (list, tuple)):
        return tuple(default)
    out: list[str] = []
    seen: set[str] = set()
    for item in value:
        text = str(item).strip()
        if not text or text in seen:
            continue
        seen.add(text)
        out.append(text)
    return tuple(out)


@dataclass(frozen=True)
class DomainProfile:
    """Resolved domain-library contract for one Archon project."""

    name: str
    display_name: str
    preflight_imports: tuple[str, ...]
    lean_search_packages: tuple[str, ...]
    target_import_prefixes: tuple[str, ...]
    enforce_classical_physics_modeling: bool
    require_explicit_mathlib_import: bool

    @property
    def preflight_lines(self) -> tuple[str, ...]:
        return tuple(
            item if item.startswith("import ") else f"import {item}"
            for item in self.preflight_imports
        )

    @property
    def is_legacy_physics(self) -> bool:
        return self.name == "physics" and self.enforce_classical_physics_modeling

    @property
    def blueprint_markers(self) -> tuple[str, ...]:
        """Markers that opt a chapter into this profile's specialized loop."""
        if self.name == "chemistry-native":
            # Native answer-blind chemistry keeps grounding active without the
            # legacy physics marker, which also opts into physics-only Review
            # prompt checks.
            return ("% archon:chemistry",)
        if self.name == "chemistry":
            # Keep the historical marker as a compatibility alias for
            # chemistry chapters prepared before the domain-specific marker.
            return ("% archon:chemistry", "% archon:physics")
        return ("% archon:physics",)

    def mode_for_stage(self, stage: str) -> str | None:
        """Return the profile-specific formalizer/prover mode for ``stage``."""
        canonical = stage.strip().lower()
        chemistry = self.name in {"chemistry", "chemistry-native"}
        if canonical.startswith("autoformalize"):
            return (
                "chemistry-formalize"
                if chemistry
                else "physics-formalize"
            )
        if canonical.startswith("prover"):
            return "chemistry" if chemistry else "physics"
        return None


def load_domain_profile(project_path: Path) -> DomainProfile:
    """Load ``loop.domain_profile`` while preserving historical defaults."""

    cfg = load_project_config(project_path)
    loop_cfg = cfg.loop_section()
    raw = loop_cfg.get("domain_profile")
    if not isinstance(raw, dict):
        raw = {}

    name = str(raw.get("name") or "physics").strip() or "physics"
    display_name = str(raw.get("display_name") or name.replace("-", " ")).strip()
    if not display_name:
        display_name = name

    preflight_imports = _strings(
        raw.get("preflight_imports"),
        DEFAULT_PHYSICS_PREFLIGHT_IMPORTS,
    )
    lean_search_packages = _strings(
        raw.get("lean_search_packages"),
        ("Mathlib", "Physlib"),
    )
    target_import_prefixes = _strings(
        raw.get("target_import_prefixes"),
        ("Physlib", "PhysLean"),
    )

    legacy = name == "physics"
    enforce_classical = bool(
        raw.get("enforce_classical_physics_modeling", legacy)
    )
    require_mathlib = bool(raw.get("require_explicit_mathlib_import", legacy))

    return DomainProfile(
        name=name,
        display_name=display_name,
        preflight_imports=preflight_imports,
        lean_search_packages=lean_search_packages,
        target_import_prefixes=target_import_prefixes,
        enforce_classical_physics_modeling=enforce_classical,
        require_explicit_mathlib_import=require_mathlib,
    )
