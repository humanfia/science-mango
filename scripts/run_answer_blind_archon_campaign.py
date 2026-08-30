#!/usr/bin/env python3
"""Thin full32 answer-blind entry point for Archon's native workflow.

One fresh workspace is prepared from the sanitized seed.  The only model-facing
command is ``archon loop``; Archon schedules all prepared targets at the configured
parallelism and owns formalization, both Review gates, proof construction, and
final Lake build.  Without ``--run`` the script prepares the workspace but does
not start the loop.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import datetime as dt
import hashlib
import importlib.util
import json
import os
import re
import shlex
import shutil
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from archon.commands.chemistry_constant import DATASET_SHA256, DATASET_VERSION
from archon.commands.loop.physics_grounding import (
    _report_name as grounding_report_name,
    run_physics_grounding,
)
from archon.commands.tooling.project_lean_index import build_project_index
from archon.commands.loop.prior_result_dependency import (
    load_prior_result_dependency_context_checked,
    prior_result_dependency_relative_path,
)
from archon.commands.loop.utils import data_path as archon_data_path


SCHEMA_VERSION = 1
PIPELINE = "archon-native-answer-blind-full32"
EXPECTED_ITEMS = 32
VARIANTS = ("gpt", "kimi-k3")
DEFAULT_MAX_PARALLEL = 4
REVIEW_PREFLIGHT_TIMEOUT_SEC = 3600
BUNDLE_REL = Path("icho_2026_source/questions_only.jsonl")
SOURCE_REPORT_MARKER = "% archon:source-report "
PHYSICS_MARKER = "% archon:physics"
CHEMISTRY_MARKER = "% archon:chemistry"
LEAN_SEARCH_PACKAGES = ("Mathlib", "Physlib", "CRNT")
CRNT_PACKAGE_REL = Path("crnt-lean")
CRNT_INDEX_REL = Path(".archon/lean-explore/project-index.json")
PACKAGE_OVERRIDES_REL = Path(".lake/package-overrides.json")
TRUSTED_PRIOR_RESULT_CONSUMER_ID = "icho_2026_t1_a6"
LIVE_LITERATURE_TARGET_IDS = frozenset({
    "icho_2026_t1_a4",
    "icho_2026_t1_a5",
})
WEB_SEARCH_DISABLED_SETTINGS = (
    'web_search="disabled"',
    "features.standalone_web_search=false",
    "features.search_tool=false",
)
WEB_SEARCH_LIVE_SETTINGS = ('web_search="live"', "tools.web_search=true")

NATIVE_AGENTS = """# Answer-Blind Native Archon Instructions

Use only the problem statement, problem images, local Lean libraries, artifacts
created in this workspace, and—only when exact target-bound campaign config
enables it—public literature found with generic chemistry keywords. Never seek
or read an official answer, solution, rubric, marking scheme, grader output,
prior run, or another solver workspace. When Live Web Search is enabled, never
send a problem id, exact question wording, or answer clue; record the title, DOI
or stable URL, locator, exact scoped claim, and applicability conditions.
Everything inside the sealed problem bundle and its problem PDF/images is
student-visible problem input, including printed fallback values. A fallback
for one part may be used only for the later part(s) that the problem explicitly
authorizes; it may not justify or select the answer to the part it replaces.
If answer-bearing material outside the sealed problem inputs is visible, stop
and report it without using it.

Do not edit the question bundle, source reports, problem PDF/images,
`isolation_manifest.json`, `.archon/config.json`, or this file. During a
target-scoped prover task, edit only the assigned Lean file, its task-result
report, and the exact target-scoped answer submission required by the active
Formalizer/Prover mode. Preserve the quantities, units, hypotheses, requested outputs, and
chemical alternatives stated in the problem; do not replace the goal with a
tautology or unsupported premise.

A compiling theorem is not by itself a faithful answer. For every requested
output, formalization must leave a source-grounded semantic card in the target
task-result, and formalization Review must independently rederive the output
from the problem statement and images before inspecting that card or the Lean
statement. Missing cards, ambiguous source meaning, or a mismatch between the
independent derivation, card, and Lean contract require redraft.

For every numeric requested output, the Lean file must also carry the exact
machine-readable numeric-reporting certificate required by the formalizer
mode. Archon derives the reporting quantum from the sealed problem-only policy
and type-checks its named `ReportsAtQuantum` theorem; an agent verdict cannot
override a missing or failed deterministic certificate.

Archon's native acceptance path is: formalization, formalization Review, proof,
proof Review, and final Lake build. The solver must not run or access the answer
freeze. After its dedicated UID/process group is quiescent, a trusted external
controller freezes the answer submissions before any official-answer reveal or
scoring.
"""

NATIVE_PROTOCOL = """# Answer-Blind Native Archon Protocol

This run provides the model only the problem-only bundle, its referenced problem
assets, local Lean libraries, and any public literature obtained by a specifically
authorized target-bound Live Web Search. `official_answer_seen = false`. It does
not claim operating-system network isolation. Live queries, when enabled, must
contain only generic chemistry keywords and must never contain a problem id,
exact question wording, or answer clue; searches for official answers, solutions,
rubrics, marking schemes, and prior runs are forbidden. Browser, plugins, and
apps remain disabled. Printed fallback values inside problem assets are
exam-visible inputs; they are admissible only for the downstream parts
explicitly named by the problem, never as evidence for the upstream result they
replace.

Archon performs the normal chemistry workflow in one workspace: create faithful
Lean statements, run formalization Review, fill proofs, run proof Review, then
run the final Lake build. The solver cannot read or write the external freeze.
Only the trusted root/controller, after confirming the dedicated solver
UID/process group is quiescent, freezes submissions before official-answer
reveal or scoring.
"""

NATIVE_FORMALIZE_MODE = """---
name: physics-formalize
description: "Formalize a problem-only chemistry chapter into compiling Lean statements."
compatible_stages:
  - autoformalize
read_blueprint: true
---

## Goal

Read the assigned problem-only blueprint chapter and every problem image listed
there. Translate the chemistry faithfully into definitions and theorem
statements with `by sorry` bodies. This stage writes the statement; it does not
solve the proof.

- Preserve every requested output, given quantity, unit, sign, bound, branch,
  conservation law, stoichiometric coefficient, and domain condition.
- Derive numerical values from the supplied data; do not invent empirical facts
  or encode a desired result as an assumption.
- Before writing the Lean statement, derive and record a `Semantic Card` section
  in the assigned task-result. It must contain exactly one entry for every
  requested output and, for each entry:
  - the source wording/part label and an exact definition of the requested
    quantity, explicitly distinguishing cumulative/overall/repeated-process
    quantities from per-step, per-cycle, marginal, or instantaneous ones;
  - the numerator and denominator or composition/mass basis (for example dry
    carrier, loaded material, solution, aliquot, or total mixture), or an
    explicit source-based reason that this field is not applicable;
  - every numerical or symbolic constant used, each with exact value, unit,
    and a source locator such as a problem paragraph, table cell, figure label,
    image filename plus region, or pinned-library declaration;
  - upstream requested-output dependencies, governing equations, evaluation
    order, and every sign, case, branch, stereochemical, or identification
    condition (or a source-based not-applicable reason);
  - the output unit/dimension, exact unrounded raw value or symbolic result,
    source-authorized reporting/rounding rule, and the Lean declarations that
    carry each input, relation, raw result, and reported result; and
  - `ambiguity_status: clear`. If any source meaning, basis, constant, branch,
    or reporting rule cannot be justified from the allowed inputs, record the
    ambiguity and report `needs_redraft`; do not choose the interpretation that
    makes the current Lean goal easiest to prove.
- Keep exact values through the derivation and round only the final requested
  output unless the problem explicitly directs an intermediate rounding step.
  Record such a direction with its source locator.
- For every requested output whose `kind` is `numeric`, read its predeclared
  policy from the matching row of
  `icho_2026_source/questions_only.jsonl`. Define a fully-qualified raw scalar
  declaration of type `ℝ` and a fully-qualified theorem whose exact type is
  `IChO2026Chem.Reporting.ReportsAtQuantum raw reported quantum`. Immediately
  before that theorem, write exactly one single-line Lean comment in this form
  (JSON keys and value types are exact):
  `-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"<requested id>","reporting_policy_kind":"significant_figures|decimal_places","reporting_policy_digits":<integer>,"reported_value":"<exact decimal or reduced fraction>","reporting_quantum":"<exact decimal or reduced fraction>","raw_declaration":"<fully.qualified.raw.name>","reporting_declaration":"<fully.qualified.theorem.name>"}`
  The two declaration names must be distinct across outputs. Decimal-place
  quantum is `10^-digits`. Significant-figure quantum is determined from the
  nonzero reported magnitude and digits (for example three significant figures
  at magnitude `10^3` has quantum `10`). Do not choose it from a desired
  answer. A zero significant-figure report is ambiguous in this protocol and
  must be routed to `needs_redraft`; do not invent a quantum. The deterministic
  guard rejects missing/duplicate certificates, booleans in numeric fields,
  unsafe names, noncanonical numbers, and any policy or quantum mismatch.
- Do not weaken the requested result to `True`, a reflexive equality, or an
  unrelated existence claim.
- Use local Mathlib/Physlib/CRNT/project declarations whose signatures you have
  checked. Read the current target's `physics-grounding-*` report before
  editing, then use `lake env lean` to compile the assigned file.
- If the searched libraries do not provide a problem-specific bridge, state
  and prove a target-local helper from available foundations. Do not install,
  update, fetch, or replace Lake dependencies.
- For routine atomic weights, isotope masses, formula molar masses, a
  registered generic reaction schema, a controller-pinned contest
  interpretation, or an exact allowlisted reviewed rule, use only the offline CLI.
  Query grammar (angle-bracket names are placeholders, not literal tokens):
  `"$ARCHON_CLI_BIN" chemistry-constant atomic_weight <ELEMENT>`,
  `"$ARCHON_CLI_BIN" chemistry-constant isotope_mass <ISOTOPE>`,
  `"$ARCHON_CLI_BIN" chemistry-constant molar_mass <FORMULA>`,
  `"$ARCHON_CLI_BIN" chemistry-constant reaction_template <TEMPLATE_ID>`,
  `"$ARCHON_CLI_BIN" chemistry-constant contest_interpretation <POLICY_ID>`, or
  `"$ARCHON_CLI_BIN" chemistry-constant empirical_rule <RULE_ID>`.
  For `atomic_weight`, `isotope_mass`, and `molar_mass` only, these grammar lines
  and examples are illustrative, not an allowlist: any structurally valid
  element, canonical isotope, or formula supported by this dataset is permitted.
  The exact `TEMPLATE_ID` allowlist is:
  `binary_two_fragment_electrophilic_addition`.
  The exact `POLICY_ID` allowlist is:
  `analogous_halogen_addition`.
  For `empirical_rule`, the exact baseline `RULE_ID` values usable without
  runtime activation are:
  `aqueous_feiii_phenol_colored_complex`,
  `hexamethylbenzene_cold_kmno4_to_mellitic_acid`,
  `mellite_ideal_stoichiometry`, and
  `mellitic_acid_benzoyl_chloride_to_c12o9`.
  The Reference-only empirical-rule IDs are:
  `mellitic_acid_p2o5_heating_forms_some_trianhydride`.
  A reference-only record is never baseline evidence and cannot receive a
  controller activation receipt. Its claim may be cited only when independent
  problem evidence supplies every exact applicability condition; the lookup
  itself proves none. Never borrow a missing protocol condition from literature.
  When a condition is absent, the record may nominate a closed-audit candidate
  but remains non-premise context for the current reaction.
  The dormant Reviewer-requestable bridge IDs are:
  `closed_candidate_cryolite_aluminum_production_filter`,
  `closed_candidate_feiii_phenol_filter`,
  `closed_domain_mellite_terminal_residue_candidate_filter`, and
  `directed_reaction_omitted_protocol_candidate_filter`.
  This four-ID baseline list is an exact allowlist without activation. Dormant
  records may be returned by the CLI but are not active evidence in an initial
  formalization or ordinary lookup. Use one only when the current immediate-
  redraft prompt contains its complete controller-built receipt bound to this
  exact target and candidate. A bare ID, lookup, candidate citation, or Reviewer
  paraphrase never activates it. All applicability conditions are conjunctive
  and source-bound: if even one lacks exact evidence, the rule is inapplicable
  and the target must remain blocked. Receipt completeness never establishes
  applicability. The baseline, reference-only, and dormant
  lists are the full empirical-rule inventory. Never guess, enumerate, or probe
  any other registry id; an unlisted id fails closed. Pass exactly one
  allowed token—never a problem id, question/source text, URL, or search phrase.
  The command performs no network access and returns a dataset version/hash that
  must be preserved as provenance.
  Problem-stipulated values take precedence. A pinned nominal value may be used
  for an olympiad-style central answer when requested, but check whether source
  uncertainty could change the required reported digits or classification. A
  returned reaction template is not evidence that the current problem
  instantiates it; establish that classification separately from problem
  evidence or trusted general chemistry.
  A returned contest interpretation is a non-empirical contest-semantics
  policy, not a paper or universal chemical law. Use it only when every
  required cue is bound to an exact problem locator and no problem-statement
  override applies; a missing or ambiguous cue or a different substrate must
  fail closed. It authorizes only the returned domain, template,
  stoichiometry, and retention scope and does not identify the specific
  reagent. Derive that identity independently from the problem measurements
  and separately receipted constants, preserving both `dataset_sha256` and
  `record_sha256`.
  A baseline `empirical_rule` receipt, or a dormant rule carried by a complete
  current controller activation receipt, grounds only the returned claim under
  its returned
  `authority_kind`, inside every returned applicability condition, and outside
  every returned exclusion. For `peer_reviewed_literature`, use it only as a
  source-scoped literature claim, never beyond its cited substrate, reagent, or
  conditions. For `contest_semantics_policy`, use it only as a bounded policy,
  not a paper or universal empirical law, and require the complete source-
  supplied finite candidate set, full structural-feature audit, and explicit
  interference exclusions required by the record. The returned
  `automatic_problem_instantiation` must be false; never turn a literature claim
  into an inverse classification or the bounded policy into an open-world rule.
  When used, preserve `dataset_sha256`, `record_sha256`,
  `base_dataset_sha256`, `pinned_rule_record_sha256`,
  `empirical_registry_manifest_sha256`, and returned `source.url`, `source.doi`,
  `source.locator`, `source.content_sha256`, plus the approved review metadata.
  A Reviewer must rerun the exact operation and allowed id and compare all those
  values. A missing or mismatched hash, source locator, approval, applicability
  condition, or scope—or a different substrate or reagent—must fail closed.
  A reference-only `empirical_rule` receipt is not covered by that baseline or
  dormant grounding permission. Its exact returned claim may be cited only
  after independent problem evidence establishes every applicability condition.
  Otherwise it cannot fill an omitted condition or ground a source-to-Lean
  bridge about the current reaction.

- For assigned `IChO2026Problems/problem_<TARGET_ID>.lean`, atomically overwrite
  `.archon/task_results/IChO2026Problems_problem_<TARGET_ID>.answer.json` on
  every formalization and redraft. It is generated output, never source
  evidence, and must have exactly this schema:
  ```json
  {
    "schema_version": 1,
    "id": "<TARGET_ID>",
    "official_answer_seen": false,
    "outputs": [
      {
        "id": "<exact requested_outputs id>",
        "kind": "<exact requested_outputs kind>",
        "raw_value": "<finite number or non-empty exact symbolic string>",
        "display_value": "<required non-empty displayed string>",
        "unit": "<exact requested_outputs unit>"
      }
    ]
  }
  ```
  Preserve the requested output order/count/id/kind/unit exactly. Apply each
  requested output's reporting_policy to `display_value`; it is always a JSON
  string, including for integer/numeric outputs. Keep exact, unrounded
  arithmetic in `raw_value` when applicable. For numeric outputs prefer ASCII
  decimal/e notation such as `7.03e12`; never use Unicode superscript digits.
  Do not add `composition_accounting`, topology, ledger, or any other field to
  this exact answer JSON schema; image-accounting details belong in Lean/task
  reports and Review certificates only.
- Edit only the assigned Lean file, its `.archon/task_results` report, and that
  exact `.answer.json`. Do not create any other candidate/answer JSON, edit the
  problem sources, or edit another target.
- If official answers, solutions, rubrics, grader data, or prior-run answers are
  visible, stop and report an answer-blind violation without reading them.
"""

NATIVE_PROOF_MODE = """---
name: physics
description: "Prove the reviewed chemistry statements without weakening them."
compatible_stages:
  - prover
read_blueprint: true
---

## Goal

Replace `sorry` in the assigned chemistry Lean file with sound proofs. Keep the
reviewed declaration signatures and chemical meaning fixed. Use the encoded
source data and governing relations. Read the current target's
`physics-grounding-*` report before proving; search Mathlib/Physlib and the CRNT
overlay, and run `lake env lean` until the file compiles. A missing
problem-specific bridge may be synthesized as a proved target-local helper. If
a foundational bridge cannot be derived from the pinned libraries and source
hypotheses, report `needs_redraft` so the next iteration can re-ground and
rebuild the formalization; do not weaken it. Never install, update, fetch, or
replace Lake dependencies.

Before returning, verify the exact target-scoped `.answer.json` required by the
Formalizer mode still matches requested_outputs, reporting_policy, and the
reviewed Lean result carriers. It is part of the reviewed statement contract:
never invent or revise its answer merely to make a proof work. If it is missing,
invalid, or stale, recreate/refresh it only by unambiguous transcription from
the already reviewed Lean carriers, preserving the same answer semantics. If
that is impossible, report `needs_redraft`; do not guess. `display_value` must
remain a JSON string. Edit only the assigned Lean file, task-result report, and
that exact answer file; do not create another candidate/answer artifact.

Never seek or use an official answer, solution, rubric, grader output,
prior run, or another solver's work.
Do not edit numeric-reporting certificate comments, raw declaration types, or
reporting theorem types. Prove every named `ReportsAtQuantum` theorem exactly;
the deterministic Review preflight will type-check it against the problem-only
policy after proof completion.
"""

NATIVE_PLAN_GUIDE = """# Native answer-blind planning

Plan only from the problem-only blueprint, current Lean files, deterministic
Lean diagnostics, current target grounding reports, and the preceding Archon
Review. Missing problem-specific bridges may be target-local proved helpers;
missing foundational bridges must be routed through `needs_redraft`, never a
dependency update. Keep the current target set within the configured prover
lanes. Never seek an official answer, solution, rubric, grader output, prior
run, or another solver's work.
"""

NATIVE_REVIEW_GUIDE = f"""# Native answer-blind Review

Review the current targets against their problem-only blueprint chapters and
problem images and current LeanExplore grounding report. During autoformalize,
decide whether each Lean statement is a faithful and derivable encoding and
emit the structured formalization Review certificate requested by the
invocation. During prover, audit the exact Lean proof and emit the requested
proof Review route. Accept proved target-local helper lemmas when they derive
the required bridge from pinned foundations; route a missing foundational
bridge to `needs_redraft` so grounding and formalization are rebuilt on the next
iteration. Treat an exam-visible fallback as evidence only for downstream parts
that explicitly authorize it; require an independent derivation for the part
whose missing result the fallback replaces. Never request a dependency install
or update. Write exactly one
JSONL row for every listed objective: no omissions, duplicates, or extra
targets. Also write the requested summary, recommendations, and PROJECT_STATUS
files. Do not modify Lean files and never seek an official answer, solution,
rubric, grader output, prior run, or another solver's work.

The deterministic preflight includes `numeric_reporting` evidence for each
target. A numeric target may pass only when that evidence has status `passed`;
`failed` requires formalization redraft and cannot be waived by semantic
judgment. `not_applicable` is valid only when the problem-only requested-output
inventory contains no numeric output.

For autoformalize, semantic Review is a source-first independent derivation,
not a consistency check of generated artifacts. For each target, follow this
order:

1. Read the problem statement and every referenced problem image. Before
   inspecting the target Lean file, its Semantic Card, prover trace, or claimed
   result, independently reconstruct exactly one audit entry per requested
   output. Do the arithmetic, stoichiometric counting, conservation reasoning,
   and case analysis yourself from those allowed sources.
2. Record that derivation in the existing `checks`, `requested_outputs`,
   `blind_source_audit`, `contract_audit`, and `chemistry_checks` fields. These
   fields carry the semantic verdict; give concise evidence for every requested
   output, decisive candidate-domain choice, uniqueness claim, and
   answer-smuggling check.
3. Only then inspect the formalizer's Semantic Card and Lean statement. Compare
   the independently derived entry field by field with both artifacts. Check
   atom/repeating-unit counts, mass-balance bases, cumulative yields or losses,
   denominators, constants, unit conversions, branches, and the absence of
   unauthorized intermediate rounding. A proof of the encoded statement is no
   evidence that the encoding matches the problem.
4. `independent_rederivation` is optional audit metadata. Its auxiliary JSON
   absence or wrong-type shape alone does not determine the verdict or consume
   a Review retry. A substantive mismatch remains blocking: record it in the
   existing semantic fields and return `status=failed` with `needs_redraft`.
5. `formalization_review.status=passed` is allowed only when ambiguity is clear
   and every independent entry exactly matches both the Semantic Card and Lean
   contract. A missing/duplicate requested output, conflicting reasonable
   interpretation, or semantic mismatch is `status=failed` with a
   `needs_redraft` reason. Do not silently select one ambiguous interpretation.

During prover Review, re-check that the proof closes the already reviewed raw
and reported result carriers without changing this semantic mapping. If proof
work exposes a wrong quantity, basis, constant, branch, unit, dependency, or
reporting rule, route `needs_redraft`, even if Lean compiles. Use `solved` only
when the faithful contract and its proof both pass.
For each target, read only its explicitly bound `.answer.json` as untrusted
generated output. Re-derive every raw/display value independently, then audit
the exact output order/id/kind/unit/reporting_policy and its named Lean carrier.
Record match/failure status by output id without copying raw answer values into
source provenance or controller history.

The only permitted general-knowledge lookup is the pinned offline structured
CLI. Query grammar (angle-bracket names are placeholders, not literal tokens):
`"$ARCHON_CLI_BIN" chemistry-constant atomic_weight <ELEMENT>`,
`"$ARCHON_CLI_BIN" chemistry-constant isotope_mass <ISOTOPE>`,
`"$ARCHON_CLI_BIN" chemistry-constant molar_mass <FORMULA>`,
`"$ARCHON_CLI_BIN" chemistry-constant reaction_template <TEMPLATE_ID>`,
`"$ARCHON_CLI_BIN" chemistry-constant contest_interpretation <POLICY_ID>`, or
`"$ARCHON_CLI_BIN" chemistry-constant empirical_rule <RULE_ID>`.
For `atomic_weight`, `isotope_mass`, and `molar_mass` only, these grammar lines
and examples are illustrative, not an allowlist: any structurally valid element,
canonical isotope, or formula supported by this dataset is permitted.
The exact `TEMPLATE_ID` allowlist is:
`binary_two_fragment_electrophilic_addition`.
The exact `POLICY_ID` allowlist is:
`analogous_halogen_addition`.
For `empirical_rule`, the exact baseline `RULE_ID` values usable without
runtime activation are:
`aqueous_feiii_phenol_colored_complex`,
`hexamethylbenzene_cold_kmno4_to_mellitic_acid`,
`mellite_ideal_stoichiometry`, and
`mellitic_acid_benzoyl_chloride_to_c12o9`.
The Reference-only empirical-rule IDs are:
`mellitic_acid_p2o5_heating_forms_some_trianhydride`.
A reference-only record is never baseline evidence and cannot receive a
controller activation receipt. Its claim may be cited only when independent
problem evidence supplies every exact applicability condition; the lookup
itself proves none. Never borrow a missing protocol condition from literature.
When a condition is absent, it may nominate a closed-audit candidate but
remains non-premise context for the current reaction.
The dormant Reviewer-requestable bridge IDs are:
`closed_candidate_cryolite_aluminum_production_filter`,
`closed_candidate_feiii_phenol_filter`,
`closed_domain_mellite_terminal_residue_candidate_filter`, and
`directed_reaction_omitted_protocol_candidate_filter`.
This four-ID baseline list is an exact allowlist without activation. An ordinary lookup of a dormant rule is not evidence. A formalization Reviewer may request only one
exact dormant ID for one corresponding blocked bridge; it may not supply rule
text, source, URL, hash, or claim. Accept a dormant rule only through a complete
controller-built activation or next-Review context receipt bound to the exact
target and candidate, after checking every rule/source/review hash, applicability
condition, and exclusion. All applicability conditions are conjunctive and
source-bound: if even one lacks exact evidence, the rule is inapplicable and the
target must remain blocked. Receipt completeness never establishes
applicability. The baseline, reference-only, and dormant lists are
the full empirical-rule inventory. Never guess, enumerate, or probe any other
registry id; an unlisted id fails closed. Never pass a problem
id, question text, URL, or search phrase. The Reviewer must verify each used
lookup through the same `"$ARCHON_CLI_BIN"` grammar and check its returned
dataset version/hash against the bound source contract. The exact TEMPLATE_ID,
POLICY_ID, and RULE_ID lists above are the full supported registries; no other
identifier may be probed.
Problem-stipulated values override the dataset. A pinned nominal value may be
used for an olympiad-style central answer when requested, but check whether
source uncertainty could change the required reported digits or classification.
A generic reaction template does not establish that the current problem
instantiates it.
A contest interpretation receipt is a non-empirical contest-semantics policy,
not a paper or universal chemical law. Accept it only after binding every
required cue to an exact problem locator, confirming that no problem-statement
override applies, and rerunning the exact operation and argument to verify both
`dataset_sha256` and `record_sha256`. A missing or ambiguous cue or a different
substrate must fail closed. The receipt authorizes only its returned domain,
template, stoichiometry, and retention scope; it does not identify the specific
reagent, which must still follow independently from the problem measurements
and separately receipted constants.
A baseline `empirical_rule` receipt, or a dormant rule carried by a complete
current controller activation/context receipt, grounds only the returned claim
under its returned
`authority_kind`, inside every returned applicability condition, and outside
every returned exclusion. For `peer_reviewed_literature`, accept it only as a
source-scoped literature claim, never beyond the cited substrate, reagent, or
conditions. For `contest_semantics_policy`, accept it only as a bounded contest
policy, not a paper or universal empirical law, and require the complete
source-supplied finite candidate set, full structural-feature audit, and
explicit interference exclusions required by the record. The returned
`automatic_problem_instantiation` must be false. Never turn a literature claim
into an inverse classification or the bounded policy into an open-world rule.
The Reviewer must preserve and compare `dataset_sha256`, `record_sha256`,
`base_dataset_sha256`, `pinned_rule_record_sha256`,
`empirical_registry_manifest_sha256`, returned `source.url`, `source.doi`,
`source.locator`, `source.content_sha256`, and the approved review metadata
after rerunning the exact operation and allowed id. A missing or mismatched
hash, source locator, approval, applicability condition, or scope—or a different
substrate or reagent—must fail closed.
A reference-only `empirical_rule` receipt is not covered by that baseline or
dormant grounding permission. Its exact returned claim may be cited only after
independent problem evidence establishes every applicability condition.
Otherwise it cannot fill an omitted condition or ground a source-to-Lean bridge
about the current reaction.

"""


class CampaignError(RuntimeError):
    pass


def _load_script(name: str):
    path = Path(__file__).resolve().with_name(name)
    spec = importlib.util.spec_from_file_location(f"_archon_native_{path.stem}", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_SEED = _load_script("build_answer_blind_solver_seed.py")
_CONFIGURE = _load_script("configure_answer_blind_workspace.py")


def _utcnow() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


@dataclasses.dataclass(frozen=True)
class Config:
    campaign_root: Path
    seed_workspace: Path | None = None
    lake_packages: Path | None = None
    archon_bin: str = "archon"
    max_iterations: int = 100
    review_max_iterations: int = 10
    max_parallel: int = DEFAULT_MAX_PARALLEL
    expected_items: int = EXPECTED_ITEMS
    target_lifecycle: bool = False
    reuse_lake_packages: bool = False
    in_place_index: bool = False
    trusted_prior_result_receipt: Path | None = None
    variant: str = "gpt"

    @property
    def workspace(self) -> Path:
        return self.campaign_root / "workspace"

    @property
    def log_path(self) -> Path:
        return self.campaign_root / "run.log"

    @property
    def index_path(self) -> Path:
        return self.campaign_root / "campaign.json"

    @property
    def private_lake_packages(self) -> Path:
        if self.reuse_lake_packages and self.lake_packages is not None:
            return self.lake_packages
        return self.campaign_root / "lake-packages"


def _target_ids(root: Path, *, expected_items: int = EXPECTED_ITEMS) -> tuple[str, ...]:
    try:
        manifest = json.loads((root / "isolation_manifest.json").read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError("invalid isolation_manifest.json") from exc
    ids = manifest.get("target_ids") if isinstance(manifest, dict) else None
    if (
        not isinstance(ids, list)
        or len(ids) != expected_items
        or len(set(map(str, ids))) != expected_items
    ):
        raise CampaignError(
            f"seed must declare exactly {expected_items} unique target_ids"
        )
    return tuple(map(str, ids))


def _targets(ids: Sequence[str]) -> tuple[str, ...]:
    return tuple(f"IChO2026Problems/problem_{item}.lean" for item in ids)


def _fresh_config(config: Config) -> tuple[Config, tuple[str, ...]]:
    if config.seed_workspace is None or config.lake_packages is None:
        raise CampaignError("fresh preparation requires --seed-workspace and --lake-packages")
    root, seed, packages = map(
        Path.resolve, (config.campaign_root, config.seed_workspace, config.lake_packages)
    )
    if not packages.is_dir():
        raise CampaignError(f"Lake packages directory is missing: {packages}")
    if root == seed or root.is_relative_to(seed) or seed.is_relative_to(root):
        raise CampaignError("campaign root and seed must be disjoint")
    if root.exists() and (not root.is_dir() or any(root.iterdir())):
        raise CampaignError(f"campaign root must be absent or empty: {root}")
    if type(config.max_iterations) is not int or config.max_iterations < 1:
        raise CampaignError("max_iterations must be a positive integer")
    if (
        type(config.review_max_iterations) is not int
        or config.review_max_iterations < 1
    ):
        raise CampaignError("review_max_iterations must be a positive integer")
    if type(config.expected_items) is not int or config.expected_items < 1:
        raise CampaignError("expected_items must be a positive integer")
    if type(config.max_parallel) is not int or not (
        1 <= config.max_parallel <= config.expected_items
    ):
        raise CampaignError(
            f"max_parallel must be between 1 and {config.expected_items}"
        )
    if type(config.target_lifecycle) is not bool:
        raise CampaignError("target_lifecycle must be a boolean")
    if type(config.reuse_lake_packages) is not bool:
        raise CampaignError("reuse_lake_packages must be a boolean")
    if type(config.in_place_index) is not bool:
        raise CampaignError("in_place_index must be a boolean")
    if config.variant not in VARIANTS:
        raise CampaignError(f"variant must be one of: {', '.join(VARIANTS)}")
    try:
        _SEED.validate_seed(seed)
    except Exception as exc:
        raise CampaignError(f"seed validation failed: {exc}") from exc
    resolved = dataclasses.replace(
        config, campaign_root=root, seed_workspace=seed, lake_packages=packages
    )
    return resolved, _target_ids(seed, expected_items=config.expected_items)


def _resume_config(config: Config) -> tuple[Config, tuple[str, ...]]:
    config = dataclasses.replace(config, campaign_root=config.campaign_root.resolve())
    if not config.workspace.is_dir() or not config.index_path.is_file():
        raise CampaignError(f"prepared workspace is missing: {config.workspace}")
    if type(config.max_iterations) is not int or config.max_iterations < 1:
        raise CampaignError("max_iterations must be a positive integer")
    if (
        type(config.review_max_iterations) is not int
        or config.review_max_iterations < 1
    ):
        raise CampaignError("review_max_iterations must be a positive integer")
    if type(config.expected_items) is not int or config.expected_items < 1:
        raise CampaignError("expected_items must be a positive integer")
    if type(config.max_parallel) is not int or not (
        1 <= config.max_parallel <= config.expected_items
    ):
        raise CampaignError(
            f"max_parallel must be between 1 and {config.expected_items}"
        )
    if type(config.target_lifecycle) is not bool:
        raise CampaignError("target_lifecycle must be a boolean")
    if type(config.reuse_lake_packages) is not bool:
        raise CampaignError("reuse_lake_packages must be a boolean")
    if type(config.in_place_index) is not bool:
        raise CampaignError("in_place_index must be a boolean")
    if config.variant not in VARIANTS:
        raise CampaignError(f"variant must be one of: {', '.join(VARIANTS)}")
    ids = _target_ids(config.workspace, expected_items=config.expected_items)
    _check_native_config(
        config.workspace,
        max_iterations=config.max_iterations,
        review_max_iterations=config.review_max_iterations,
        max_parallel=config.max_parallel,
        max_objectives=config.expected_items,
        target_lifecycle=config.target_lifecycle,
        variant=config.variant,
    )
    _validate_native_markers(config.workspace, ids)
    _validate_crnt_project_index(config)
    return config, ids


def _patch_native_config(
    workspace: Path, *, max_iterations: int, review_max_iterations: int,
    max_parallel: int, target_lifecycle: bool,
    max_objectives: int = EXPECTED_ITEMS,
    variant: str = "gpt",
) -> None:
    if variant not in VARIANTS:
        raise CampaignError(f"variant must be one of: {', '.join(VARIANTS)}")
    harness_name = f"answer-blind-{variant}"
    path = workspace / ".archon/config.json"
    try:
        value = json.loads(path.read_text())
        loop = value["loop"]
        harness = value["harnesses"][harness_name]
        domain = loop["domain_profile"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError(
            f"configured workspace lacks the {variant} Archon harness"
        ) from exc
    if not isinstance(domain, dict) or domain.get("name") != "chemistry":
        raise CampaignError("configured workspace lacks the chemistry profile")
    domain["lean_search_packages"] = list(LEAN_SEARCH_PACKAGES)
    model = "gpt-5.6-sol" if variant == "gpt" else "kimi-k3[1m]"
    if variant == "kimi-k3":
        expected_harness = _CONFIGURE.build_archon_config(
            variant=variant,
            max_objectives=max_objectives,
            max_parallel=max_parallel,
        )["harnesses"][harness_name]
        if harness != expected_harness:
            raise CampaignError("configured workspace has an invalid Kimi harness")
        loop.update({
            "harness": harness_name,
            "model": model,
            "max_iterations": max_iterations,
            "formalization_review_max_iterations": review_max_iterations,
            "proof_review_max_iterations": review_max_iterations,
            "parallel": True,
            "max_parallel": max_parallel,
            "max_objectives": max_objectives,
            "formalization_review_gate": True,
            "proof_review_gate": True,
            "deterministic_review": True,
            "review_preflight_jobs": max_parallel,
            "review_preflight_timeout_sec": REVIEW_PREFLIGHT_TIMEOUT_SEC,
            "parallel_target_review_jobs": max_parallel,
            "parallel_formalization_review_jobs": max_parallel,
            "parallel_formalization_review": target_lifecycle,
            "parallel_target_review": target_lifecycle,
            "pipeline_target_review": target_lifecycle,
        })
        shared = loop.get("shared_infrastructure")
        if isinstance(shared, dict):
            shared["enabled"] = False
        path.write_bytes(_json_bytes(value))
        return
    for key in ("base_url_env", "key_env", "wire_api"):
        harness.pop(key, None)
    extra_args = list(harness.get("extra_args") or [])
    live_literature_search = (
        frozenset(_target_ids(workspace, expected_items=max_objectives))
        == LIVE_LITERATURE_TARGET_IDS
    )
    if (
        len(extra_args) % 2 != 0
        or any(
            extra_args[index] != "-c"
            for index in range(0, len(extra_args), 2)
        )
    ):
        raise CampaignError("Codex extra_args must be -c/setting pairs")
    controlled_web_settings = set(
        WEB_SEARCH_DISABLED_SETTINGS + WEB_SEARCH_LIVE_SETTINGS
    )
    filtered_extra_args: list[str] = []
    for index in range(0, len(extra_args), 2):
        setting = extra_args[index + 1]
        if setting not in controlled_web_settings:
            filtered_extra_args.extend(("-c", setting))
    extra_args = filtered_extra_args
    web_settings = (
        WEB_SEARCH_LIVE_SETTINGS
        if live_literature_search
        else WEB_SEARCH_DISABLED_SETTINGS
    )
    for setting in web_settings:
        extra_args.extend(("-c", setting))
    for setting in (
        "features.code_mode=false",
        "features.code_mode.enabled=false",
        "features.shell_snapshot=false",
        "features.shell_tool=true",
        "features.multi_agent=false",
        "features.multi_agent_v2=false",
    ):
        extra_args.extend(("-c", setting))
    harness.update({
        "runner": "codex",
        "model": "gpt-5.6-sol",
        "effort": "max",
        # This host disables unprivileged user namespaces, so Codex's
        # workspace-write sandbox cannot provide its execution host.  The
        # native loop instead runs as a dedicated non-root UID, while answer
        # and controller paths stay root-only; _run_loop enforces that boundary.
        "sandbox": "danger-full-access",
        # Loop-owned deterministic grounding uses hosted LeanExplore for the
        # public Mathlib/Physlib index and the generated local CRNT overlay.
        "lean_explore_backend": "hosted",
        "ignore_user_config": True,
        "ephemeral": True,
        # Keep the native path deliberately small.  Archon's deterministic
        # review preflight and finalizer invoke Lake directly, while Codex can
        # use the workspace shell for intermediate Lean checks.  No separate
        # answer-blind MCP jail is needed in this input-level isolation mode.
        "mcp": [],
        "extra_args": extra_args,
    })
    harness.pop("lean_lsp_mcp_bin", None)
    loop.update({
        "harness": harness_name,
        "model": model,
        "max_iterations": max_iterations,
        "formalization_review_max_iterations": review_max_iterations,
        "proof_review_max_iterations": review_max_iterations,
        "parallel": True,
        "max_parallel": max_parallel,
        "max_objectives": max_objectives,
        "formalization_review_gate": True,
        "proof_review_gate": True,
        "deterministic_review": True,
        "review_preflight_jobs": max_parallel,
        "review_preflight_timeout_sec": REVIEW_PREFLIGHT_TIMEOUT_SEC,
        "parallel_target_review_jobs": max_parallel,
        "parallel_formalization_review_jobs": max_parallel,
        # Target-lifecycle mode reuses Archon's per-target Review scheduler.
        "parallel_formalization_review": target_lifecycle,
        "parallel_target_review": target_lifecycle,
        "pipeline_target_review": target_lifecycle,
    })
    shared = loop.get("shared_infrastructure")
    if isinstance(shared, dict):
        shared["enabled"] = False
    path.write_bytes(_json_bytes(value))


def _write_native_policy_files(workspace: Path) -> None:
    formalize_mode = archon_data_path(
        "prover-modes/chemistry-formalize.md"
    ).read_text(encoding="utf-8")
    payloads = {
        workspace / ".archon/AGENTS.md": NATIVE_AGENTS,
        workspace / "ANSWER_BLIND_PROTOCOL.md": NATIVE_PROTOCOL,
        workspace / ".archon/prover-modes/physics-formalize.md": formalize_mode,
        workspace / ".archon/prover-modes/chemistry-formalize.md": formalize_mode,
        workspace / ".archon/prover-modes/physics.md": NATIVE_PROOF_MODE,
        workspace / ".archon/prover-modes/chemistry.md": NATIVE_PROOF_MODE,
        workspace / ".archon/prompts/plan.md": NATIVE_PLAN_GUIDE,
        workspace / ".archon/prompts/review.md": NATIVE_REVIEW_GUIDE,
        workspace / ".mcp.json": '{"mcpServers": {}}\n',
    }
    for path, text in payloads.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text.rstrip() + "\n", encoding="utf-8")


def _activate_native_review_profile(workspace: Path) -> None:
    path = workspace / ".archon/config.json"
    try:
        value = json.loads(path.read_text())
        domain = value["loop"]["domain_profile"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("cannot activate the native review profile") from exc
    if not isinstance(domain, dict) or domain.get("name") != "chemistry":
        raise CampaignError("prepared workspace lost its chemistry profile")
    domain.update({"name": "chemistry-native", "display_name": "IChO chemistry"})
    path.write_bytes(_json_bytes(value))
    _write_native_policy_files(workspace)


def _detach_strict_source_contract(workspace: Path, ids: Sequence[str]) -> None:
    """Drop strict source metadata while retaining the grounding trigger."""
    chapter_root = workspace / "blueprint/src/chapters"
    for target_id in ids:
        path = chapter_root / f"IChO2026Problems_problem_{target_id}.tex"
        try:
            lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
        except OSError as exc:
            raise CampaignError(f"missing prepared blueprint chapter: {path}") from exc
        marker_indexes = [
            index for index, line in enumerate(lines)
            if line.lstrip().startswith(SOURCE_REPORT_MARKER)
        ]
        if len(marker_indexes) != 1:
            raise CampaignError(f"prepared chapter has an invalid source marker: {path}")
        del lines[marker_indexes[0]]
        physics_indexes = [
            index for index, line in enumerate(lines)
            if line.strip() == PHYSICS_MARKER
        ]
        if len(physics_indexes) != 1:
            raise CampaignError(f"prepared chapter has an invalid domain marker: {path}")
        del lines[physics_indexes[0]]
        chemistry_indexes = [
            index for index, line in enumerate(lines)
            if line.strip() == CHEMISTRY_MARKER
        ]
        if len(chemistry_indexes) != 1:
            raise CampaignError(f"prepared chapter has an invalid chemistry marker: {path}")
        path.write_text("".join(lines), encoding="utf-8")


def _validate_native_markers(workspace: Path, ids: Sequence[str]) -> None:
    """Fail closed unless every live target has only the chemistry trigger."""
    chapter_root = workspace / "blueprint/src/chapters"
    for target_id in ids:
        path = chapter_root / f"IChO2026Problems_problem_{target_id}.tex"
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError as exc:
            raise CampaignError(f"missing native blueprint chapter: {path}") from exc
        physics = sum(line.strip() == PHYSICS_MARKER for line in lines)
        chemistry = sum(line.strip() == CHEMISTRY_MARKER for line in lines)
        source_reports = sum(
            line.lstrip().startswith(SOURCE_REPORT_MARKER.rstrip()) for line in lines
        )
        if physics != 0 or chemistry != 1 or source_reports != 0:
            raise CampaignError(
                f"native chapter has invalid grounding/source markers: {path}"
            )


def _crnt_package_root(config: Config) -> Path:
    root = config.private_lake_packages / CRNT_PACKAGE_REL
    source_dir = root / "CRNT"
    root_module = root / "CRNT.lean"
    if root.is_symlink() or not root.is_dir():
        raise CampaignError(f"private CRNT package is missing or unsafe: {root}")
    if source_dir.is_symlink() or not source_dir.is_dir():
        raise CampaignError(f"private CRNT source directory is missing or unsafe: {source_dir}")
    if root_module.is_symlink() or not root_module.is_file():
        raise CampaignError(f"private CRNT root module is missing or unsafe: {root_module}")
    return root


def _crnt_manifest_pin(config: Config) -> tuple[str, str]:
    path = config.workspace / "lake-manifest.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        packages = payload["packages"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("workspace lake-manifest.json is invalid") from exc
    matches = [
        row for row in packages
        if isinstance(row, dict)
        and str(row.get("name") or "").strip().strip("«»") == "crnt-lean"
    ] if isinstance(packages, list) else []
    if len(matches) != 1:
        raise CampaignError("lake-manifest.json must pin exactly one crnt-lean package")
    row = matches[0]
    revision = str(row.get("rev") or "").strip()
    url = str(row.get("url") or "").strip()
    if row.get("type") != "git" or re.fullmatch(r"[0-9a-f]{40}", revision) is None or not url:
        raise CampaignError("lake-manifest.json has an invalid crnt-lean pin")
    return revision, url


def _crnt_git_value(root: Path, *arguments: str) -> str:
    controller_config = root / ".git/config"
    if controller_config.is_symlink() or not controller_config.is_file():
        raise CampaignError("private CRNT checkout metadata is invalid")
    environment = os.environ.copy()
    environment["GIT_CONFIG_NOSYSTEM"] = "1"
    # Do not use /dev/null as the empty global config sentinel. Git may open it
    # read-write while sanitizing standard descriptors, which is unavailable
    # in a read-only sealed runtime. Reusing the exact controller-owned checkout
    # config is deterministic; Git also loads it normally as the local config.
    environment["GIT_CONFIG_GLOBAL"] = str(controller_config)
    try:
        result = subprocess.run(
            ["git", "-c", f"safe.directory={root}", *arguments],
            cwd=root,
            env=environment,
            stdin=subprocess.PIPE,
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise CampaignError("private CRNT checkout metadata is invalid") from exc
    value = result.stdout.strip()
    if not value:
        raise CampaignError("private CRNT checkout metadata is empty")
    return value


def _validate_crnt_project_index(config: Config) -> dict[str, Any]:
    path = config.workspace / CRNT_INDEX_REL
    if path.is_symlink() or not path.is_file():
        raise CampaignError(f"CRNT LeanExplore overlay index is missing or unsafe: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError("CRNT LeanExplore overlay index is invalid") from exc
    declarations = payload.get("declarations")
    source_files = payload.get("source_files")
    count = payload.get("declaration_count")
    crnt_root = _crnt_package_root(config).resolve()
    pinned_revision, pinned_url = _crnt_manifest_pin(config)
    checkout_revision = _crnt_git_value(crnt_root, "rev-parse", "HEAD")
    checkout_url = _crnt_git_value(crnt_root, "remote", "get-url", "origin")
    if (
        payload.get("schema_version") != 1
        or payload.get("package") != "CRNT"
        or payload.get("project_path") != str(crnt_root)
        or payload.get("commit") != pinned_revision
        or payload.get("repo_url") != pinned_url
        or checkout_revision != pinned_revision
        or checkout_url != pinned_url
        or not isinstance(declarations, list)
        or not declarations
        or isinstance(count, bool)
        or not isinstance(count, int)
        or count != len(declarations)
        or not isinstance(source_files, list)
        or "CRNT.lean" not in source_files
        or not any(
            isinstance(item, str)
            and item.startswith("CRNT/")
            and item.endswith(".lean")
            for item in source_files
        )
        or any(
            not isinstance(item, str)
            or not (item == "CRNT.lean" or (
                item.startswith("CRNT/") and item.endswith(".lean")
            ))
            for item in source_files
        )
    ):
        raise CampaignError("CRNT LeanExplore overlay index has invalid metadata")
    for declaration in declarations:
        if (
            not isinstance(declaration, dict)
            or declaration.get("package") != "CRNT"
            or not isinstance(declaration.get("name"), str)
            or not declaration["name"].strip()
            or not isinstance(declaration.get("module"), str)
            or not declaration["module"].startswith("CRNT.")
        ):
            raise CampaignError(
                "CRNT LeanExplore overlay contains a non-CRNT declaration"
            )
    return payload


def _build_crnt_project_index(config: Config) -> dict[str, Any]:
    root = _crnt_package_root(config)
    try:
        build_project_index(
            root,
            source_roots=(Path("CRNT"), Path("CRNT.lean")),
            package="CRNT",
            output_path=config.workspace / CRNT_INDEX_REL,
        )
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        raise CampaignError(f"cannot build the CRNT LeanExplore overlay: {exc}") from exc
    return _validate_crnt_project_index(config)


def _run_initial_grounding(config: Config, ids: Sequence[str]) -> dict[str, int]:
    """Ground all targets before the first ``--from prover`` iteration."""
    expected = {(config.workspace / target).resolve() for target in _targets(ids)}
    try:
        reports = run_physics_grounding(
            config.workspace,
            backend="hosted",
            packages=LEAN_SEARCH_PACKAGES,
            lean_files=sorted(expected),
            reuse_unchanged=True,
        )
    except Exception as exc:
        raise CampaignError(f"initial LeanExplore grounding crashed: {exc}") from exc

    actual: dict[Path, Any] = {}
    for report in reports:
        lean_file = Path(getattr(report, "lean_file", "")).resolve()
        if lean_file in actual:
            raise CampaignError(f"initial grounding returned a duplicate target: {lean_file}")
        actual[lean_file] = report
    if set(actual) != expected:
        raise CampaignError("initial grounding did not cover the exact blind target set")
    counts = collections.Counter()
    task_results = (config.workspace / ".archon/task_results").resolve()
    for lean_file, report in actual.items():
        report_path = Path(getattr(report, "report_path", ""))
        expected_report = task_results / grounding_report_name(
            config.workspace, lean_file
        )
        if (
            report_path.is_symlink()
            or not report_path.is_file()
            or report_path.resolve() != expected_report
        ):
            raise CampaignError(f"initial grounding report has invalid scope: {report_path}")
        try:
            metadata = set(report_path.read_text(encoding="utf-8").splitlines())
        except OSError as exc:
            raise CampaignError(f"initial grounding report is missing: {report_path}") from exc
        statuses = {
            line.removeprefix("- Grounding status: ")
            for line in metadata
            if line.startswith("- Grounding status: ")
        }
        if statuses not in ({"complete"}, {"incomplete"}):
            raise CampaignError(f"initial grounding report has invalid status: {report_path}")
        status = next(iter(statuses))
        if bool(getattr(report, "is_complete", False)) != (status == "complete"):
            raise CampaignError(f"initial grounding status disagrees with report: {report_path}")
        if not {
            "- Search backend: hosted",
            f"- Packages searched: {', '.join(LEAN_SEARCH_PACKAGES)}",
        }.issubset(metadata) or not any(
            re.fullmatch(r"- Input fingerprint: sha256:[0-9a-f]{64}", line)
            for line in metadata
        ):
            raise CampaignError(f"initial grounding report metadata is invalid: {report_path}")
        counts[status] += 1
    if counts["incomplete"]:
        with config.log_path.open("a", encoding="utf-8") as log:
            log.write(
                f"[{_utcnow()}] warning: initial LeanExplore grounding left "
                f"{counts['incomplete']} target(s) incomplete; continue so the "
                "native loop can synthesize target-local helpers or route "
                "foundational gaps to needs_redraft.\n"
            )
    return dict(sorted(counts.items()))


def _check_native_config(
    workspace: Path, *, max_iterations: int = 100,
    review_max_iterations: int = 10,
    max_parallel: int = DEFAULT_MAX_PARALLEL,
    max_objectives: int = EXPECTED_ITEMS,
    target_lifecycle: bool = False,
    preparation: bool = False,
    variant: str = "gpt",
) -> None:
    if variant not in VARIANTS:
        raise CampaignError(f"variant must be one of: {', '.join(VARIANTS)}")
    harness_name = f"answer-blind-{variant}"
    model = "gpt-5.6-sol" if variant == "gpt" else "kimi-k3[1m]"
    try:
        value = json.loads((workspace / ".archon/config.json").read_text())
        loop = value["loop"]
        harness = value["harnesses"][harness_name]
        blind = value["answer_blind"]
        blind_isolation = blind["isolation"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("prepared Archon config is invalid") from exc
    extra_args = harness.get("extra_args")
    live_literature_search = (
        frozenset(_target_ids(workspace, expected_items=max_objectives))
        == LIVE_LITERATURE_TARGET_IDS
    )
    expected_web_settings = (
        WEB_SEARCH_LIVE_SETTINGS
        if live_literature_search
        else WEB_SEARCH_DISABLED_SETTINGS
    )
    forbidden_web_settings = (
        WEB_SEARCH_DISABLED_SETTINGS
        if live_literature_search
        else WEB_SEARCH_LIVE_SETTINGS
    )
    if isinstance(extra_args, list):
        config_pairs = {
            (extra_args[index], extra_args[index + 1])
            for index in range(0, len(extra_args) - 1, 2)
        }
    else:
        config_pairs = set()
    web_search_valid = variant == "kimi-k3" or (
        all(("-c", setting) in config_pairs for setting in expected_web_settings)
        and all(
            ("-c", setting) not in config_pairs
            for setting in forbidden_web_settings
        )
    )
    expected_kimi_harness = _CONFIGURE.build_archon_config(
        variant="kimi-k3",
        max_objectives=max_objectives,
        max_parallel=max_parallel,
    )["harnesses"]["answer-blind-kimi-k3"]
    harness_valid = (
        harness == expected_kimi_harness
        if variant == "kimi-k3"
        else (
            harness.get("runner") == "codex"
            and harness.get("sandbox") == "danger-full-access"
            and harness.get("lean_explore_backend") == "hosted"
            and harness.get("mcp") == []
            and "lean_lsp_mcp_bin" not in harness
            and not any(key in harness for key in ("base_url_env", "key_env"))
            and "features.shell_tool=true" in (harness.get("extra_args") or [])
            and "features.multi_agent=false" in (harness.get("extra_args") or [])
        )
    )
    if (
        not isinstance(blind, dict)
        or not isinstance(blind_isolation, dict)
        or blind.get("authority") != "problem-only"
        or blind.get("official_answer_seen") is not False
        or blind.get("phase") != "solve"
        or blind.get("protocol") != "icho-answer-blind-v1"
        or blind_isolation.get("filesystem_answer_blind") is not True
        or blind_isolation.get("network_answer_blind") is not False
        or not harness_valid
        or not web_search_valid
        or loop.get("harness") != harness_name
        or loop.get("model") != model
        or (loop.get("domain_profile") or {}).get("name")
        != ("chemistry" if preparation else "chemistry-native")
        or (loop.get("domain_profile") or {}).get("lean_search_packages")
        != list(LEAN_SEARCH_PACKAGES)
        or (loop.get("shared_infrastructure") or {}).get("enabled") is not False
        or loop.get("deterministic_review") is not True
    ):
        raise CampaignError("prepared harness is not native non-root Codex")
    if loop.get("review_preflight_timeout_sec") != REVIEW_PREFLIGHT_TIMEOUT_SEC:
        raise CampaignError(
            "prepared config has unexpected review_preflight_timeout_sec"
        )
    configured_max_iterations = loop.get("max_iterations")
    if (
        type(configured_max_iterations) is not int
        or configured_max_iterations != max_iterations
    ):
        raise CampaignError("prepared config has unexpected max_iterations")
    for key in (
        "formalization_review_max_iterations",
        "proof_review_max_iterations",
    ):
        configured = loop.get(key)
        if type(configured) is not int or configured != review_max_iterations:
            raise CampaignError(f"prepared config has unexpected {key}")
    lifecycle_flags = (
        loop.get("parallel_formalization_review"),
        loop.get("parallel_target_review"),
        loop.get("pipeline_target_review"),
    )
    if any(value is not target_lifecycle for value in lifecycle_flags):
        raise CampaignError(
            "--target-lifecycle must match the prepared workspace config"
        )
    if loop.get("max_objectives") != max_objectives:
        raise CampaignError("prepared config has unexpected max_objectives")
    for key in (
        "max_parallel",
        "review_preflight_jobs",
        "parallel_target_review_jobs",
        "parallel_formalization_review_jobs",
    ):
        if loop.get(key) != max_parallel:
            raise CampaignError(f"prepared config has unexpected {key}")


def _write_all(workspace: Path, ids: Sequence[str]) -> None:
    path = workspace / "IChO2026Problems/All.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    imports = [target.removesuffix(".lean").replace("/", ".") for target in _targets(ids)]
    path.write_text("".join(f"import {item}\n" for item in imports))


def _shared_package_path_overrides(config: Config) -> list[dict[str, Any]]:
    """Map a sealed shared Lake snapshot to local, read-only dependencies.

    Lake probes Git metadata while loading a Git manifest, even when every
    pinned revision is already present. An isolated solver must not be able to
    refresh or delete the controller-owned dependency snapshot. Path
    overrides make that contract explicit: Lake may read the exact manifest
    package directories, but it never treats them as mutable Git checkouts.
    """
    try:
        manifest = json.loads(
            (config.workspace / "lake-manifest.json").read_text(encoding="utf-8")
        )
        packages = manifest["packages"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("workspace lake-manifest.json is invalid") from exc
    if not isinstance(manifest, dict) or not isinstance(packages, list) or not packages:
        raise CampaignError("workspace lake-manifest.json has no packages")
    packages_dir = manifest.get("packagesDir", ".lake/packages")
    if packages_dir != ".lake/packages":
        raise CampaignError("workspace Lake package directory is not canonical")

    root = config.private_lake_packages
    if root.is_symlink() or not root.is_dir():
        raise CampaignError("shared Lake package root must be a plain directory")
    entries: list[tuple[str, dict[str, Any]]] = []
    expected_names: set[str] = set()
    for row in packages:
        if not isinstance(row, dict) or row.get("type") != "git":
            raise CampaignError("shared Lake manifest must contain only Git packages")
        encoded_name = row.get("name")
        if not isinstance(encoded_name, str):
            raise CampaignError("shared Lake manifest has an invalid package name")
        name = encoded_name.strip()
        if name.startswith("«") and name.endswith("»"):
            name = name[1:-1]
        if (
            not name
            or name in {".", ".."}
            or Path(name).name != name
            or "/" in name
            or "\\" in name
            or name in expected_names
        ):
            raise CampaignError("shared Lake manifest has an unsafe package name")
        package = root / name
        if package.is_symlink() or not package.is_dir():
            raise CampaignError(f"shared Lake package is missing or unsafe: {package}")
        expected_names.add(name)
        override: dict[str, Any] = {
            "name": encoded_name,
            "scope": str(row.get("scope") or ""),
            "type": "path",
            "dir": f".lake/packages/{name}",
            "inherited": bool(row.get("inherited", False)),
        }
        for field in ("configFile", "manifestFile"):
            if field in row:
                override[field] = row[field]
        entries.append((name, override))

    try:
        actual_names = {
            path.name
            for path in root.iterdir()
            if not path.name.startswith(".")
        }
    except OSError as exc:
        raise CampaignError("cannot enumerate shared Lake package root") from exc
    if actual_names != expected_names:
        raise CampaignError(
            "shared Lake package snapshot does not exactly match the manifest"
        )
    return [entry for _name, entry in sorted(entries)]


def _write_shared_package_path_overrides(config: Config) -> None:
    path = config.workspace / PACKAGE_OVERRIDES_REL
    if path.exists() or path.is_symlink():
        raise CampaignError("workspace carries a pre-existing Lake package override")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "schemaVersion": "1.2.0",
                "packages": _shared_package_path_overrides(config),
            },
            ensure_ascii=False,
            sort_keys=True,
            indent=2,
        ) + "\n",
        encoding="utf-8",
    )


def _install_trusted_prior_result_receipt(
    workspace: Path,
    source_path: Path | None,
    *,
    controller_uid: int,
) -> dict[str, Any]:
    """Install one controller-owned, immutable A4/A5-to-A6 receipt."""

    if source_path is None:
        return {}
    if (
        type(controller_uid) is not int
        or controller_uid < 0
        or os.geteuid() != controller_uid
    ):
        raise CampaignError(
            "trusted prior-result receipt installation requires the "
            "designated controller UID"
        )
    try:
        root = workspace.resolve(strict=True)
        root_metadata = root.lstat()
    except OSError as exc:
        raise CampaignError("prepared workspace is unavailable") from exc
    if (
        not root.is_dir()
        or root_metadata.st_uid != controller_uid
        or root_metadata.st_mode & 0o022
    ):
        raise CampaignError(
            "prepared workspace is not controller-owned read-only data"
        )

    source = source_path.absolute()
    try:
        before = source.lstat()
    except OSError as exc:
        raise CampaignError("trusted prior-result receipt is missing") from exc
    if (
        source.is_symlink()
        or not source.is_file()
        or before.st_nlink != 1
        or before.st_uid != controller_uid
        or before.st_mode & 0o222
    ):
        raise CampaignError(
            "trusted prior-result receipt source is not controller-owned "
            "immutable data"
        )
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    descriptor = -1
    try:
        descriptor = os.open(source, flags)
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_nlink != 1
            or metadata.st_uid != controller_uid
            or metadata.st_mode & 0o222
            or (metadata.st_dev, metadata.st_ino)
            != (before.st_dev, before.st_ino)
        ):
            raise CampaignError(
                "trusted prior-result receipt source changed during validation"
            )
        payload = b""
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            payload += chunk
    except OSError as exc:
        raise CampaignError("cannot read trusted prior-result receipt") from exc
    finally:
        if descriptor >= 0:
            os.close(descriptor)

    relative = prior_result_dependency_relative_path(
        TRUSTED_PRIOR_RESULT_CONSUMER_ID
    )
    destination = root / relative
    if source.resolve() == destination or destination.exists() or destination.is_symlink():
        raise CampaignError(
            "prepared workspace already contains the A6 prior-result receipt"
        )
    for directory in (root / ".archon", destination.parent):
        try:
            directory.mkdir(mode=0o755, exist_ok=True)
            metadata = directory.lstat()
            if (
                stat.S_ISLNK(metadata.st_mode)
                or not stat.S_ISDIR(metadata.st_mode)
                or metadata.st_uid != controller_uid
            ):
                raise CampaignError(
                    "A6 receipt directory is not controller-owned"
                )
            directory.chmod(0o755)
        except OSError as exc:
            raise CampaignError(
                "cannot prepare the controller-owned A6 receipt directory"
            ) from exc

    output_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    output_flags |= getattr(os, "O_CLOEXEC", 0)
    output_flags |= getattr(os, "O_NOFOLLOW", 0)
    output_descriptor = -1
    try:
        output_descriptor = os.open(destination, output_flags, 0o400)
        view = memoryview(payload)
        while view:
            written = os.write(output_descriptor, view)
            view = view[written:]
        os.fchmod(output_descriptor, 0o444)
        os.fsync(output_descriptor)
    except OSError as exc:
        if destination.exists() and not destination.is_symlink():
            destination.unlink()
        raise CampaignError(
            "cannot install the controller-owned A6 receipt"
        ) from exc
    finally:
        if output_descriptor >= 0:
            os.close(output_descriptor)

    receipt, reason = load_prior_result_dependency_context_checked(
        root,
        TRUSTED_PRIOR_RESULT_CONSUMER_ID,
        controller_uid=controller_uid,
    )
    if reason:
        destination.unlink()
        raise CampaignError(
            "installed A6 prior-result receipt failed checked readback: "
            + reason
        )
    return receipt


def prepare_workspace(config: Config, ids: Sequence[str]) -> None:
    assert config.seed_workspace is not None and config.lake_packages is not None
    config.campaign_root.mkdir(parents=True, exist_ok=True)
    try:
        label = "GPT" if config.variant == "gpt" else "Kimi K3"
        _SEED.copy_seed_to_workspace(config.seed_workspace, config.workspace, label=label)
        _CONFIGURE.configure_answer_blind_workspace(
            config.workspace,
            variant=config.variant,
            max_objectives=len(ids),
            max_parallel=config.max_parallel,
        )
    except Exception as exc:
        raise CampaignError(f"workspace preparation failed: {exc}") from exc
    _patch_native_config(
        config.workspace,
        max_iterations=config.max_iterations,
        review_max_iterations=config.review_max_iterations,
        max_parallel=config.max_parallel,
        max_objectives=len(ids),
        target_lifecycle=config.target_lifecycle,
        variant=config.variant,
    )
    _write_native_policy_files(config.workspace)
    _check_native_config(
        config.workspace,
        max_iterations=config.max_iterations,
        review_max_iterations=config.review_max_iterations,
        max_parallel=config.max_parallel,
        max_objectives=len(ids),
        target_lifecycle=config.target_lifecycle,
        preparation=True,
        variant=config.variant,
    )
    # Lake may refresh package-local Git metadata even for an otherwise clean
    # build.  Give this campaign its own copy so the native workflow cannot
    # mutate (or be invalidated by) a shared cache.
    if config.reuse_lake_packages:
        if config.private_lake_packages.is_symlink() or not config.private_lake_packages.is_dir():
            raise CampaignError("shared Lake package root must be a plain directory")
    else:
        try:
            shutil.copytree(
                config.lake_packages,
                config.private_lake_packages,
                symlinks=True,
            )
        except OSError as exc:
            raise CampaignError(f"cannot create private Lake package copy: {exc}") from exc
    link = config.workspace / ".lake/packages"
    link.parent.mkdir(parents=True, exist_ok=True)
    link.symlink_to(config.private_lake_packages, target_is_directory=True)
    if config.reuse_lake_packages:
        _write_shared_package_path_overrides(config)
    _write_all(config.workspace, ids)
    _build_crnt_project_index(config)


def physics_command(config: Config) -> list[str]:
    return [
        config.archon_bin, "physics-formalize", str(config.workspace),
        "--input-jsonl", str(config.workspace / BUNDLE_REL),
        "--image-root", str(config.workspace / "icho_2026_source/image"),
        "--out-dir", "IChO2026Problems",
        "--report-dir", "reports/icho_2026",
        "--work-dir", ".archon/physics-formalize/full32",
        "--evaluation-mode", "answer-blind",
        "--limit", "-1", "--update-progress",
    ]


def loop_command(config: Config, *, resume: bool) -> list[str]:
    command = [config.archon_bin, "loop", str(config.workspace)]
    command += ["--resume"] if resume else ["--from", "prover"]
    return command + [
        "--parallel", "--max-parallel", str(config.max_parallel),
        "--max-objectives", str(config.expected_items),
        "--max-iterations", str(config.max_iterations),
        "--formalization-review-max-iterations",
        str(config.review_max_iterations),
        "--proof-review-max-iterations", str(config.review_max_iterations),
        "--review", "--formalization-review-gate", "--proof-review-gate",
        "--no-dashboard", "--no-blueprint-web",
    ]


def _private_git_packages(config: Config) -> tuple[Path, ...]:
    root = config.private_lake_packages
    if root.is_symlink() or not root.is_dir():
        raise CampaignError(f"private Lake package root is not a real directory: {root}")
    try:
        entries = sorted(root.iterdir(), key=lambda path: path.name)
    except OSError as exc:
        raise CampaignError(f"cannot enumerate private Lake packages: {root}") from exc

    packages: list[Path] = []
    for entry in entries:
        if entry.is_symlink() or not entry.is_dir():
            raise CampaignError(f"invalid private Lake package entry: {entry}")
        git_dir = entry / ".git"
        if not git_dir.exists():
            continue
        if git_dir.is_symlink() or not git_dir.is_dir():
            raise CampaignError(f"invalid private Lake package Git directory: {git_dir}")
        packages.append(entry)
    if not packages:
        raise CampaignError(f"private Lake package root contains no Git packages: {root}")
    return tuple(packages)


def _resolved_archon_bin(config: Config, environment: Mapping[str, str]) -> Path:
    raw = Path(config.archon_bin)
    if raw.is_absolute() or raw.parent != Path("."):
        return raw.absolute()
    located = shutil.which(config.archon_bin, path=environment.get("PATH"))
    if not located:
        raise CampaignError(
            f"cannot resolve configured Archon binary: {config.archon_bin}"
        )
    return Path(located).resolve()


def _valid_chemistry_constant_smoke(
    result: subprocess.CompletedProcess,
) -> bool:
    if result.returncode != 0:
        return False
    try:
        payload = json.loads(result.stdout)
    except (TypeError, json.JSONDecodeError):
        return False
    return bool(
        isinstance(payload, Mapping)
        and payload.get("dataset_version") == DATASET_VERSION
        and payload.get("dataset_sha256") == DATASET_SHA256
    )


def _run(command: Sequence[str], *, config: Config) -> tuple[int, float]:
    started = time.monotonic()
    # The campaign-local dependency checkout is controller-owned and read-only.
    # Git otherwise rejects it when Archon/Lean runs as the dedicated solver
    # user, which Lake misleadingly reports as a changed remote URL.  Limit the
    # ownership exceptions to this fresh workspace and the exact Git package
    # directories in this campaign. Git does not expand safe.directory globs.
    safe_directories = (config.workspace, *_private_git_packages(config))
    environment = os.environ.copy()
    archon_bin = _resolved_archon_bin(config, environment)
    old_path = environment.get("PATH", "")
    environment["PATH"] = str(archon_bin.parent) + os.pathsep + old_path
    environment["GIT_CONFIG_COUNT"] = str(len(safe_directories))
    for index, path in enumerate(safe_directories):
        environment[f"GIT_CONFIG_KEY_{index}"] = "safe.directory"
        environment[f"GIT_CONFIG_VALUE_{index}"] = str(path)
    with config.log_path.open("a", encoding="utf-8") as log:
        log.write(f"\n[{_utcnow()}] $ {shlex.join(command)}\n")
        log.flush()
        try:
            if len(command) > 1 and command[1] == "loop":
                smoke = subprocess.run(
                    [
                        str(archon_bin),
                        "chemistry-constant",
                        "atomic_weight",
                        "C",
                    ],
                    cwd=config.workspace,
                    capture_output=True,
                    text=True,
                    check=False,
                    env=environment,
                    timeout=30,
                )
                if not _valid_chemistry_constant_smoke(smoke):
                    log.write(
                        "configured Archon binary failed the pinned offline "
                        "chemistry-constant smoke check\n"
                    )
                    return 126, time.monotonic() - started
            result = subprocess.run(
                list(command), cwd=config.workspace, stdout=log,
                stderr=subprocess.STDOUT, text=True, check=False,
                env=environment,
            )
            code = result.returncode
        except OSError as exc:
            log.write(f"failed to start: {exc}\n")
            code = 127
    return code, time.monotonic() - started


def validate_physics_metadata(workspace: Path, ids: Sequence[str]) -> None:
    try:
        latest = workspace / ".archon/physics-formalize/latest.json"
        value = json.loads(latest.read_text())
        entries = value["entries"]
        summary = value["work_dir"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("invalid physics-formalize metadata") from exc
    summary_path = Path(str(summary)) / "summary.jsonl"
    if not summary_path.is_absolute():
        summary_path = workspace / summary_path
    try:
        records = [json.loads(line) for line in summary_path.read_text().splitlines() if line.strip()]
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError("invalid physics-formalize summary.jsonl") from exc
    if (
        value.get("command") != "physics-formalize"
        or value.get("evaluation_mode") != "answer_blind"
        or value.get("official_answer_seen") is not False
        or not isinstance(entries, list)
        or {str(row.get("id")) for row in entries if isinstance(row, dict)} != set(ids)
        or not isinstance(records, list)
        or {str(row.get("rel_lean")) for row in records if isinstance(row, dict)}
        != set(_targets(ids))
    ):
        raise CampaignError("physics-formalize did not prepare the exact blind target set")


def _gate_counts(path: Path, expected: set[str]) -> tuple[dict[str, int], bool]:
    try:
        targets = json.loads(path.read_text()).get("targets", {})
    except (OSError, json.JSONDecodeError, AttributeError):
        targets = {}
    normalized = {
        str(key).replace("\\", "/").lstrip("./"): row
        for key, row in targets.items()
    } if isinstance(targets, dict) else {}
    statuses = [
        str(normalized[rel].get("status", "missing"))
        if isinstance(normalized.get(rel), dict) else "missing"
        for rel in expected
    ]
    return (
        dict(sorted(collections.Counter(statuses).items())),
        set(normalized) == expected,
    )


def _latest_build(workspace: Path) -> tuple[bool | None, int | None]:
    metas = []
    for path in (workspace / ".archon/logs").glob("iter-*/meta.json"):
        number = path.parent.name.removeprefix("iter-")
        if number.isdigit():
            metas.append((int(number), path))
    # A newer interrupted iteration invalidates an older terminal snapshot.
    # Do not scan past it and silently reuse stale Lake/sorry evidence.
    for _number, path in sorted(metas, reverse=True)[:1]:
        try:
            value = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            return None, None
        if not value.get("completedAt"):
            return None, None
        lake = value.get("finalize", {}).get("lake", {})
        return lake.get("ok"), value.get("sorry_count")
    return None, None


def native_summary(workspace: Path, ids: Sequence[str]) -> dict[str, Any]:
    expected = set(_targets(ids))
    state = workspace / ".archon"
    formal, formal_exact = _gate_counts(
        state / "formalization-review-gate.json", expected
    )
    proof, proof_exact = _gate_counts(state / "proof-review-gate.json", expected)
    build_ok, sorry_count = _latest_build(workspace)
    complete = (
        formal_exact and proof_exact
        and formal.get("passed") == len(expected)
        and proof.get("solved") == len(expected)
        and build_ok is True and sorry_count == 0
    )
    return {
        "formalization_review": formal,
        "proof_review": proof,
        "lake_build_ok": build_ok,
        "sorry_count": sorry_count,
        "complete": complete,
    }


def _write_index(config: Config, value: Mapping[str, Any]) -> None:
    if config.in_place_index:
        # A Landlock-confined per-target worker may have write authority to the
        # exact pre-created state file but not to its parent directory.  The
        # isolated full32 controller owns the atomic aggregate index.
        with config.index_path.open("wb") as stream:
            stream.write(_json_bytes(value))
            stream.flush()
            os.fsync(stream.fileno())
        return
    temporary = config.index_path.with_name(".campaign.json.tmp")
    temporary.write_bytes(_json_bytes(value))
    os.replace(temporary, config.index_path)


def _base_index(config: Config, ids: Sequence[str]) -> dict[str, Any]:
    bundle = config.workspace / BUNDLE_REL
    return {
        "schema_version": SCHEMA_VERSION,
        "pipeline": PIPELINE,
        "workspace": str(config.workspace),
        "row_count": len(ids),
        "bundle_sha256": hashlib.sha256(bundle.read_bytes()).hexdigest(),
        "max_iterations": config.max_iterations,
        "review_max_iterations": config.review_max_iterations,
        "max_parallel": config.max_parallel,
        "target_lifecycle": config.target_lifecycle,
        "variant": config.variant,
        "status": "preparing",
        "updated_at": _utcnow(),
    }


def run_fresh(config: Config, *, start_loop: bool) -> dict[str, Any]:
    config, ids = _fresh_config(config)
    prepare_workspace(config, ids)
    if (
        config.trusted_prior_result_receipt is not None
        and TRUSTED_PRIOR_RESULT_CONSUMER_ID not in ids
    ):
        raise CampaignError(
            "trusted prior-result receipt requires the A6 consumer target"
        )
    _install_trusted_prior_result_receipt(
        config.workspace,
        config.trusted_prior_result_receipt,
        controller_uid=0,
    )
    index = _base_index(config, ids)
    _write_index(config, index)
    code, seconds = _run(physics_command(config), config=config)
    index.update(phase="physics-formalize", returncode=code, duration_seconds=round(seconds, 3))
    if code == 0:
        try:
            validate_physics_metadata(config.workspace, ids)
        except CampaignError as exc:
            code, index["error"] = 1, str(exc)
    if code != 0:
        index.update(status="failed", updated_at=_utcnow())
        _write_index(config, index)
        return index
    _detach_strict_source_contract(config.workspace, ids)
    _validate_native_markers(config.workspace, ids)
    _activate_native_review_profile(config.workspace)
    _check_native_config(
        config.workspace,
        max_iterations=config.max_iterations,
        review_max_iterations=config.review_max_iterations,
        max_parallel=config.max_parallel,
        max_objectives=config.expected_items,
        target_lifecycle=config.target_lifecycle,
        variant=config.variant,
    )
    _validate_crnt_project_index(config)
    grounding = _run_initial_grounding(config, ids)
    index.update(
        status="prepared",
        grounding=grounding,
        native=native_summary(config.workspace, ids),
    )
    _write_index(config, index)
    if not start_loop:
        return index
    return _run_loop(config, ids, index, resume=False)


def _run_loop(
    config: Config, ids: Sequence[str], index: dict[str, Any], *, resume: bool
) -> dict[str, Any]:
    if os.geteuid() == 0:
        raise CampaignError(
            "refusing to start the model loop as root; use the dedicated non-root solver UID"
        )
    index.update(status="running", phase="resume" if resume else "loop", updated_at=_utcnow())
    _write_index(config, index)
    code, seconds = _run(loop_command(config, resume=resume), config=config)
    native = native_summary(config.workspace, ids)
    index.update(
        returncode=code,
        duration_seconds=round(seconds, 3),
        native=native,
        status=(
            "succeeded" if code == 0 and native["complete"]
            else "failed" if code != 0
            else "incomplete"
        ),
        updated_at=_utcnow(),
    )
    _write_index(config, index)
    return index


def resume_campaign(config: Config) -> dict[str, Any]:
    config, ids = _resume_config(config)
    try:
        index = json.loads(config.index_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError("invalid campaign.json") from exc
    if index.get("pipeline") != PIPELINE:
        raise CampaignError("campaign.json belongs to a different pipeline")
    receipt_variant = index.get("variant", "gpt")
    if receipt_variant != config.variant:
        raise CampaignError(
            "--variant must match the prepared campaign value "
            f"({receipt_variant})"
        )
    receipt_max_iterations = index.get("max_iterations")
    if (
        type(receipt_max_iterations) is not int
        or receipt_max_iterations != config.max_iterations
    ):
        raise CampaignError(
            "--max-iterations must match the prepared campaign value "
            f"({receipt_max_iterations})"
        )
    receipt_review_max_iterations = index.get("review_max_iterations")
    if (
        type(receipt_review_max_iterations) is not int
        or receipt_review_max_iterations != config.review_max_iterations
    ):
        raise CampaignError(
            "--review-max-iterations must match the prepared campaign value "
            f"({receipt_review_max_iterations})"
        )
    if index.get("max_parallel") != config.max_parallel:
        raise CampaignError(
            "--max-parallel must match the prepared campaign value "
            f"({index.get('max_parallel')})"
        )
    receipt_target_lifecycle = index.get("target_lifecycle", False)
    if type(receipt_target_lifecycle) is not bool:
        raise CampaignError("campaign.json has invalid target_lifecycle")
    if receipt_target_lifecycle is not config.target_lifecycle:
        raise CampaignError(
            "--target-lifecycle must match the prepared campaign value "
            f"({receipt_target_lifecycle})"
        )
    # Receipts produced by the original r6 controller predate this explicit
    # mode marker.  Their workspace config already proves the historical False
    # mode, so normalize the in-memory receipt and persist it with this resume.
    index["target_lifecycle"] = receipt_target_lifecycle
    validate_physics_metadata(config.workspace, ids)
    native = native_summary(config.workspace, ids)
    if native["complete"]:
        # Keep the native Archon state terminal too.  Without this, a later
        # direct `archon loop` would see the old prover stage and start Plan.
        from archon.state.progress import write_stage

        write_stage(config.workspace / ".archon" / "PROGRESS.md", "complete")
        index.update(
            status="succeeded",
            phase="complete",
            returncode=0,
            native=native,
            updated_at=_utcnow(),
        )
        _write_index(config, index)
        return index
    # A prepare-only run has no Archon iteration to resume.  Treat the first
    # follow-up invocation as a normal start; after that, delegate recovery to
    # Archon's native --resume machinery.
    return _run_loop(
        config,
        ids,
        index,
        resume=index.get("status") != "prepared",
    )


def dry_run(config: Config, *, include_loop: bool) -> dict[str, Any]:
    config, ids = _fresh_config(config)
    return {
        "status": "dry-run",
        "row_count": len(ids),
        "workspace": str(config.workspace),
        "commands": [physics_command(config)]
        + ([loop_command(config, resume=False)] if include_loop else []),
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign-root", required=True, type=Path)
    parser.add_argument("--seed-workspace", type=Path)
    parser.add_argument("--lake-packages", type=Path)
    parser.add_argument("--archon-bin", default="archon")
    parser.add_argument(
        "--variant",
        choices=VARIANTS,
        default="gpt",
        help="model harness variant; repeat the prepared value on resume",
    )
    parser.add_argument(
        "--trusted-prior-result-receipt",
        type=Path,
        help=(
            "install one controller-owned read-only A4/A5 receipt for A6 "
            "before physics-formalize"
        ),
    )
    parser.add_argument("--max-iterations", type=int, default=100)
    parser.add_argument(
        "--review-max-iterations",
        type=int,
        default=10,
        help=(
            "maximum attempts within each formalization/proof Review cycle; "
            "repeat the prepared value on resume (default: 10)"
        ),
    )
    parser.add_argument(
        "--expected-items",
        type=int,
        default=EXPECTED_ITEMS,
        help=("exact number of target IDs required in the seed; repeat the "
              "prepared value on resume (default: 32)"),
    )
    parser.add_argument(
        "--max-parallel",
        type=int,
        default=DEFAULT_MAX_PARALLEL,
        help=(
            "maximum concurrent Archon lanes; repeat the prepared value on resume "
            f"(at most --expected-items, default: {DEFAULT_MAX_PARALLEL})"
        ),
    )
    parser.add_argument(
        "--target-lifecycle",
        action="store_true",
        help=(
            "opt in to Archon's per-target formalize/review/prove/review lifecycle; "
            "repeat this flag on resume"
        ),
    )
    parser.add_argument(
        "--reuse-lake-packages",
        action="store_true",
        help="link an existing controller-owned read-only package snapshot",
    )
    parser.add_argument(
        "--in-place-index",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument("--run", action="store_true", help="prepare and start the loop")
    actions.add_argument("--resume", action="store_true", help="resume the existing loop")
    actions.add_argument("--dry-run", action="store_true", help="validate and print commands only")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    config = Config(
        campaign_root=args.campaign_root,
        seed_workspace=args.seed_workspace,
        lake_packages=args.lake_packages,
        archon_bin=args.archon_bin,
        max_iterations=args.max_iterations,
        review_max_iterations=args.review_max_iterations,
        max_parallel=args.max_parallel,
        expected_items=args.expected_items,
        target_lifecycle=args.target_lifecycle,
        reuse_lake_packages=args.reuse_lake_packages,
        in_place_index=args.in_place_index,
        trusted_prior_result_receipt=args.trusted_prior_result_receipt,
        variant=args.variant,
    )
    try:
        if args.resume:
            result = resume_campaign(config)
        elif args.dry_run:
            result = dry_run(config, include_loop=True)
        else:
            result = run_fresh(config, start_loop=args.run)
    except CampaignError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0 if result.get("status") in {"prepared", "succeeded", "dry-run"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
