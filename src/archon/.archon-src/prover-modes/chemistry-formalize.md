---
name: chemistry-formalize
description: "Formalize chemistry problem chapters into faithful, compiling Lean declaration stubs with sorry bodies."
compatible_stages:
  - autoformalize
read_blueprint: true
dispatcher_notes: |
  Use for chemistry-domain projects prepared by `archon physics-formalize`.
  Read every source image, preserve chemical and quantitative semantics, and
  create statements only; proof filling belongs to the `chemistry` mode.
---

## Your goal

Translate the assigned chemistry blueprint chapter into a compiling Lean file.
Create faithful definitions, structures, theorem statements, and `by sorry`
proof bodies. This pass formalizes the problem; it does not solve proofs.

## Required workflow

1. Read `PROGRESS.md`, the assigned blueprint chapter, and the source report
   linked by `% archon:source-report`.
   If the report declares `evaluation_mode: answer_blind`, treat that mode as
   a hard integrity boundary: no official answer, marking scheme, solution
   image/PDF, explanation, old formalization, or grader artifact is an
   admissible input. If any such artifact is visible, stop and report an
   integrity failure without reading or using it.
2. Read every path in `entry.image_paths` (or the legacy `entry.image_path`).
   Images may carry different pages of a table, molecular structure, spectrum,
   graph, apparatus, or reaction scheme. Do not silently use only the first.
3. Inventory the source contract before writing Lean:
   - species, isotopes, phases, reactions, structures, and named samples;
   - quantities, units, signs, significant/error bounds, and conditions;
   - supplied empirical data and governing chemical or mathematical laws;
   - previous-part conclusions that are explicitly reusable;
   - every conclusion requested by the current subquestion.
4. Write an explicit assumption/target split. Derive a candidate output from
   the problem contract, then state and prove a specification for that
   candidate; do not copy a recorded answer into a premise, structure field,
   definition, selected case, search bound, or opaque predicate that makes the
   theorem true by unfolding. In answer-blind mode there is no recorded answer
   to consult, even for validation.
5. Search before inventing APIs. Read `lean_search_packages` from the source
   report or `.archon/config.json`, pass that exact configured package list to
   LeanExplore, and search natural-language concepts plus likely Lean names.
   A typical chemistry project searches Mathlib, Physlib, and a configured
   chemistry library such as CRNT, together with project-local chemistry
   modules. Use only names whose signatures you verified.
6. Reuse existing project-local shared chemistry modules. If a reusable API is
   genuinely absent, keep the smallest faithful local interface needed for
   this target and report the proposed cross-target declaration/module; do not
   edit another file from this target-scoped lane.
7. Compile the assigned file. Stop only when it elaborates with expected
   `sorry` warnings and no name/import/type errors.

## Trusted offline chemistry reference

When the problem does not print a routine atomic weight or isotope mass, use
the closed, version-pinned CLI instead of inventing a value or declaring the
problem underdetermined:

```text
"$ARCHON_CLI_BIN" chemistry-constant atomic_weight <ELEMENT>
"$ARCHON_CLI_BIN" chemistry-constant isotope_mass <ISOTOPE>
"$ARCHON_CLI_BIN" chemistry-constant molar_mass <FORMULA>
"$ARCHON_CLI_BIN" chemistry-constant reaction_template <TEMPLATE_ID>
"$ARCHON_CLI_BIN" chemistry-constant contest_interpretation <POLICY_ID>
"$ARCHON_CLI_BIN" chemistry-constant empirical_rule <RULE_ID>
```

Angle-bracket names above are grammar placeholders, not literal tokens. For
`atomic_weight`, `isotope_mass`, and `molar_mass` only, these grammar lines and
examples are illustrative, not an allowlist: any structurally valid element,
canonical isotope, or chemical formula supported by the pinned CLI dataset is
permitted. Do not infer that an unshown element or formula is unavailable.

`reaction_template` has the exact `TEMPLATE_ID` allowlist:

- `binary_two_fragment_electrophilic_addition`

`contest_interpretation` has the exact `POLICY_ID` allowlist:

- `analogous_halogen_addition`

`empirical_rule` has the exact allowed `RULE_ID` inventory for baseline
rules usable without runtime activation:

- `aqueous_feiii_phenol_colored_complex`
- `hexamethylbenzene_cold_kmno4_to_mellitic_acid`
- `mellite_ideal_stoichiometry`
- `mellitic_acid_benzoyl_chloride_to_c12o9`

Reference-only empirical-rule IDs are:

- `mellitic_acid_p2o5_heating_forms_some_trianhydride`

This record is never baseline evidence and cannot receive a controller
activation receipt. It may be inspected as source-scoped literature context
for candidate enumeration. Its returned claim may be cited only when
independent problem evidence supplies every returned applicability condition;
the lookup itself proves none of those conditions. Never borrow a missing
protocol condition from literature. When a condition is absent, the record may
nominate a candidate for a closed audit but is non-premise context and cannot
ground a source-to-Lean bridge about the current reaction.

Dormant Reviewer-requestable bridge IDs are:

- `closed_candidate_cryolite_aluminum_production_filter`
- `closed_candidate_feiii_phenol_filter`
- `closed_domain_mellite_terminal_residue_candidate_filter`
- `directed_reaction_omitted_protocol_candidate_filter`

This four-ID list is an exact allowlist for baseline rules. The dormant records
may be returned by the sealed CLI, but they are not active
evidence in an initial formalization or from an ordinary lookup. Use one only
when this exact immediate-redraft prompt contains its complete controller-built
activation receipt bound to the assigned target and current candidate. A bare
rule id, lookup receipt, candidate citation, or Reviewer paraphrase never
activates it. All applicability conditions are conjunctive and source-bound: if
even one lacks exact evidence, the rule is inapplicable and the target must
remain blocked. Receipt completeness never establishes applicability. At lookup level these are the full supported registries: the
baseline, reference-only, dormant, template, and policy lists form the complete
inventory. Never guess, enumerate, or probe other rule ids, policy ids, or
template ids. An unlisted id must fail closed.

The command accepts exactly one enumerated operation and one corresponding
token. Never send a problem id, question text, source text, URL, search phrase,
or other free text. It performs no network access and returns machine-readable
JSON bound to
`ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1`
and its data SHA-256. Each successful lookup also carries `record_sha256`,
which binds the exact operation, query, result, source metadata, and dataset
identity.
Record both hashes in the candidate-domain derivation when used. A Reviewer
must verify every used lookup through the same
`"$ARCHON_CLI_BIN"` grammar and check that returned version/hash against the
pinned dataset; prompt examples never define the supported inventory.

When a required chemistry bridge is absent from the problem and offline
registry, public Web Search is allowed. Search by generic species, reaction,
or property only—never by olympiad problem id, exact question wording,
official answer, solution, rubric, marking scheme, or prior-run text. Prefer
primary literature or an authoritative reference. Record the title, DOI or
stable URL, exact locator, exact scoped claim, and applicability conditions.
Use the source only within that scope; it cannot invent an omitted problem
condition or establish candidate uniqueness by itself.

A candidate-local `axiom`, `def`, `theorem`, structure field, or predicate is
never a trusted chemistry rule merely because it has a plausible name, is
fully qualified, or compiles. It may encode a bridge only after the decisive
chemical implication is derived from an exact problem locator, an exact
offline lookup receipt within its stated scope, or a declaration whose origin
is verified in a configured sealed pinned library. A proved local wrapper is
acceptable only when its proof reduces to those authorities; its name alone is
not provenance.

An accepted `contest_interpretation` receipt is a versioned contest-language
policy, not a paper, empirical chemistry fact, or universal inverse
classification theorem. Before using one, list every required activation cue
from the returned record and bind each cue to an exact problem-text locator.
Check the exact `dataset_sha256` and `record_sha256`; the policy id or a local
wrapper name is insufficient. Apply only the candidate domain, reaction
template, stoichiometry, and retention stated by that record. Problem wording
always overrides the policy. If any cue is missing, ambiguous, on a different
substrate, or contradicted by the problem, fail closed. The policy does not
identify the specific reagent: prove that identity independently from the
problem measurements and pinned constants.

An accepted baseline `empirical_rule` receipt, or a dormant rule carried by a
complete current controller activation receipt, grounds only the returned
claim under the returned `authority_kind`, within every returned
`applicability_conditions` entry, and outside every returned `exclusions`. For
`peer_reviewed_literature`, treat it only as a source-scoped literature claim,
never beyond the cited substrate, reagent, or conditions. For
`contest_semantics_policy`, treat it as a bounded contest policy—not a paper or
universal empirical law. Keep `SourceFact` distinct from
`AuthorizedCandidate`. A current activation may construct a finite candidate
domain only when the rule explicitly authorizes it, each nominee has an exact
pinned `CandidateOrigin`, and a complete permitted-authority manifest records
every considered record and its source-bound include/exclude reason. Freeze
that domain before filtering. The receipt and manifest may nominate and filter
only. Even listing every permitted registry record is authority-inventory
complete, not proof that the problem's admissible domain is exhaustive.
Apply every independent problem constraint and every returned exclusion
uniformly. A determinate identification is allowed when the Reviewer confirms
that the candidate domain is justified by problem evidence or auditable
chemistry evidence, every candidate is filtered uniformly, and exactly one
candidate survives. A separate finite-exhaustive Lean theorem is optional
and is never a passing prerequisite.
`automatic_problem_instantiation` must be false; bind each
applicability condition to exact problem evidence and never turn a literature
claim into an inverse classification, a candidate into a problem fact, or the
bounded policy into an open-world rule. When using one, preserve and cite
`dataset_sha256`, `record_sha256`, `base_dataset_sha256`,
`pinned_rule_record_sha256`, `empirical_registry_manifest_sha256`, and the
returned `source.url`, `source.doi`, `source.locator`, and
`source.content_sha256`, together with the approved review metadata. The
Reviewer must rerun that exact operation and allowed id and compare every one
of those values. A missing or mismatched hash, locator, approval, condition, or
scope—or a different substrate or reagent—must fail closed.

A reference-only `empirical_rule` receipt is not covered by the baseline or
dormant grounding permission above. Its exact returned claim may be cited only
after independent problem evidence establishes every returned applicability
condition. Otherwise it may provide literature context for enumerating a
candidate, but it cannot fill an omitted condition or ground a source-to-Lean
bridge about the current reaction.

Before auditing any depicted or stated transformation, classify its use as
`quantitative_material_stage` or `qualitative_named_transform_only`. Use the
quantitative class whenever the conclusion needs a yield, completeness,
sole-product or absence claim, coefficient or phase amount, cross-stage atom or
mass balance, loss/residue amount, or an omitted stream to be empty. Enumerate
every permitted species, formula, phase, volatile output, and external input;
expose complete atom, charge, mass, and measured-interval ledgers; and forbid
anonymous or catch-all material streams.

Use `qualitative_named_transform_only` only for an explicit source arrow or
exact named-final cue acting as a non-exclusive compatibility constraint for an
identify/draw/give-structure output. It need not assert a finite open-world
candidate universe. Bind the named roles, direction, and source locator. Keep
every omitted protocol, coefficient, phase, byproduct, and stream unknown. This
mode may check a candidate's own formula, charge/valence, structure, primitive
stoichiometry, pinned-weight interval, and compatibility, but cannot prove
yield, completeness, sole-product status, absence of material, or a quantitative
stage balance. A receipt may authorize candidate construction only as its exact
rule says; it cannot supply a `SourceFact` or invent streams.

For source verbs identify, draw, or give a structure, emit a concrete candidate
when the source-first constraints and applicable authorities support it, and
give nontrivial carriers checking every decisive constraint. Audit the
provenance and uniform coverage of every finite candidate domain actually used.
Do not demand a global enumeration or global uniqueness proof unless the source
says unique, all, every, or equivalent. A named output carrier is not answer
smuggling merely because it names the candidate; reject it when the candidate is
injected into a premise, singleton/answer-shaped domain, opaque predicate, or
reflexive theorem. Fail closed when a real conflicting candidate remains or a
decisive bridge lacks an applicable trusted source.

Problem-stipulated values override the pinned dataset. A pinned nominal value
may be used for an olympiad-style central
answer when requested, but check whether source uncertainty could change the
required reported digits or classification. Do not substitute standard weights
when the problem explicitly requests integer mass numbers or a named isotope.
A reaction-template result is only a generic semantic contract: it never
establishes that the current reaction is an instance. Supply problem evidence
or a trusted general classification rule, or a qualifying exact
`contest_interpretation` receipt with all activation cues, before using its
stoichiometry or retention consequences.

## Opt-in image component accounting

When a controller semantic-DAG `requested_output` node contains
`audit_requirements: ["image_component_accounting"]`, perform this audit before
any formula, mass, charge, count, or other quantitative calculation for that
output. The marker is controller-owned and cannot be declared not applicable.

1. Inspect every bound source image relevant to the output and identify the
   complete assembled object, not merely the formula printed beside one unit.
2. Make an explicit component ledger. For each visually distinct component,
   record a source-local label, a formula or unambiguous visual descriptor, a
   positive integer multiplicity, and exactly one role from `core`,
   `repeat_unit`, `linker`, `substituent`, `terminal_group`, `guest`, `adduct`,
   `leaving_group`, or `product_fragment`.
3. Write the full assembly expression, including every repeated unit,
   linker/substituent/terminal or extra group, and ion/adduct. Recombine it into
   one formula or quantity before doing downstream arithmetic.
4. Give the assembly and recombination named, nontrivial Lean carriers and
   record the ledger and inspected image paths in the assigned task result.
   Cross-check that carrier independently against the submitted output.

The structured `composition_accounting` object is written only by Reviewers in
their Review certificate. Never add that object, topology nodes/edges, ledger,
or any extra field to the target `.answer.json`; its output entries keep exactly
`id`, `kind`, `raw_value`, `display_value`, and `unit`. For numeric display use
plain decimal or ASCII `e` notation (for example `7.03e12`), not superscript
digits.

If a component, multiplicity, attachment, or added group is unreadable or
ambiguous, report the output as blocked instead of silently using a single-unit
shortcut. Outputs without this exact controller marker keep the normal workflow.

## Chemistry modeling rules

- Preserve conservation equations, stoichiometric coefficients, charge,
  nonnegativity/positivity conditions, domains of logarithms and roots, and
  approximation or uncertainty bounds whenever the source uses them.
- Distinguish chemical entities from scalar readouts. Moles, concentrations,
  masses, energies, potentials, rates, and dimensionless ratios may be modeled
  numerically when that is the source's abstraction; do not erase species,
  phase, reaction, or sample identity when it affects the conclusion.
- Empirical constants and chemical facts are not mathematical axioms supplied
  by Lean. Use sourced data from the problem, a result from the trusted offline
  chemistry reference above, a verified library declaration, or an explicit
  hypothesis. Preserve the reference version and data hash as provenance when
  using the offline table. Never invent atomic masses, equilibrium
  constants, spectra, colors, structures, or reaction products.
- Encode a governing relation strongly enough to derive the target. An opaque
  `Prop` with no equations, inequalities, or elimination theorem is not an
  adequate bridge.
- Treat `previous_parts` according to each `dependency_policy`. A natural
  language prerequisite may be restated as an explicit hypothesis; do not
  import another generated problem file when the policy forbids it.
- Preserve alternatives and branches (species assignment, stereochemistry,
  sign, oxidation state, root, pathway) rather than selecting one branch in a
  definition before it has been derived.
- In answer-blind mode, compute quantitative results end to end from the raw
  source inputs without intermediate rounding. State the reporting rule before
  choosing the displayed result: use precision explicitly requested by the
  problem, otherwise the project policy recorded in the source report. Keep a
  theorem for the raw value as well as the final reported value.
- A numerical tolerance is admissible only when its width is mechanically
  derived from a displayed measurement quantum, a source-specified uncertainty,
  or a previously declared reporting cell. Never widen a tolerance after seeing
  which decimal would make a target provable.
- Every finite candidate set, charge/count bound, structural case split, and
  image readout must name its provenance (`problem_text`, `problem_image`,
  `problem_stated_fallback`,
  `trusted_general_law`, `derived_theorem`, or
  `activated_candidate_construction_rule`). The last provenance requires an
  exact current activation receipt and complete permitted-authority manifest;
  it constructs only an authority-relative `AuthorizedCandidate` domain, not a
  `SourceFact`. If a finite candidate domain is actually used, the Reviewer must
  audit its provenance and the uniform application of every decisive constraint.
  For identify/draw/give-structure outputs, a concrete evidence-supported
  witness does not require an open-world finite enumeration or global uniqueness
  proof unless the source requests unique, all, every, or equivalent. A finite
  exhaustive theorem may be recorded when available but is optional. If the
  supplied facts leave a real unresolved choice between candidates, formalize
  that underdetermination instead of silently importing an official-answer table.
- In this run, previous-part certificates are not yet controller-bound. Derive
  any needed earlier result inline from the problem-only material, or use only
  a fallback value explicitly printed in the current problem. A previous
  question alone is not its answer, and an unbound frozen proof is not an
  admissible dependency.
- Do not replace the requested result with `True`, a reflexive equality, an
  existence witness disconnected from the chemistry, or an unrelated numeric
  tautology.

## Write scope and task result

Edit only the assigned `.lean` file and its task-result report. Do not edit the
blueprint, source report, `PROGRESS.md`, shared modules, or dependency files.
For an answer-blind source report, also write exactly one machine-readable
`blind_candidates/<entry.id>.json` record. It is part of the solve artifact,
not a grader result, and must contain:

- `schema_version: 1`, `protocol: icho-answer-blind-v1`, `phase: solve`,
  `evaluation_mode: answer_blind`, and `official_answer_seen: false`;
- the source report's exact `id` and `blind_record_sha256`;
- `result_kind` (`numeric`, `symbolic`, `classification`, or
  `underdetermined`), raw and reported results, units, and Lean declaration
  names;
- `reporting_rule_source`, `tolerance_provenance`, and
  `candidate_domain_provenance`.
- `lean_result_contracts`, exactly two objects in `raw_result` then
  `reported_result` order. Each object has `role`, an exact fully-qualified
  `declaration`, `expected_type`, SHA-256 of its whitespace-normalized type in
  `expected_type_sha256`, and `result_payload_sha256`. The payload digest is
  computed by the pipeline helper over the exact candidate fields for that
  role. `lean_declarations` must be the same two names in the same order.

For a numeric result, put a fully-qualified source-derived raw `ℝ` expression
in `raw_result.lean_expression`, a fully-qualified problem-specific `Prop` in
`raw_result.derivation_spec`, and exact `lower`/`upper` strings in
`raw_result.certified_interval`. The raw theorem proves that derivation spec
together with both non-degenerate interval bounds; it must expose the unrounded formula or
governing relation, not define a constant to be the submitted decimal. The
reported contract proves `IChO2026Chem.Reporting.ReportsAtQuantum` for that
same raw expression. The interval supports irrational/transcendental raw
expressions without falsely equating them to a finite decimal, while
`raw_result.value` is only a certified decimal/rational reference (an interval
witness) lying inside the interval, never a claim that the raw carrier equals
that finite value.
Copy the complete source `reporting_policy` object into `reporting_rule_source`,
copy its `final_precision` object into `reported_result.precision`, use its
`tie_rule`, and include the complete source `measurement_policy` under
`tolerance_provenance.measurement_policy`.  Set
`candidate_domain_provenance.candidate_domain_policy` to the source report's
complete candidate-domain policy and give a nonempty structured `derivation`
explaining every bound/case. For a nonnumeric result, both
`lean_expression` fields must be fully-qualified problem-specific `Prop`
declarations; the generated exact type includes the role payload digest and
that semantic proposition. A theorem of `True`, a reflexive result disconnected
from the problem, or an unrelated tautology is not a result contract.

Use `result_kind: numeric` only when the current subquestion has exactly one
scalar numerical output. If it requests several numbers, a number together
with a classification/formula/structure, or any other mixed output, use one
`result_kind: symbolic` record whose problem-specific raw and reported `Prop`
declarations are conjunctions or structures covering every requested output.
The Review `requested_outputs` audit must map every source requirement to a
field/conjunct of those declarations. Never discard secondary outputs merely
to fit the scalar numeric schema. Each numeric field inside such a symbolic
result must still include an exact unrounded equality and its own
`ReportsAtQuantum` proposition; human-readable candidate text is not a proof.
The source report's `requested_outputs` list is a controller-fixed inventory.
Cover every item, in order, and use that item's own `reporting_policy`: an
exact formula/classification/integer is not rounded, while each numeric output
uses only its own declared decimal-place or significant-figure rule.

Compute hashes exactly as UTF-8 lowercase SHA-256. Normalize an
`expected_type` with Unicode NFKC and collapse every whitespace run to one
ASCII space before hashing. For a role payload, serialize the following object
as UTF-8 JSON with keys sorted, no whitespace, and `ensure_ascii=false`: common
fields `schema_version`, `protocol`, `id`, `blind_record_sha256`, `result_kind`,
and `role`, plus `raw_result` for the raw role; for the reported role also add
`reported_result`, `reporting_rule_source`, and `tolerance_provenance`. Hash
those bytes with no trailing newline. The reported-role payload also includes
`candidate_domain_provenance`. If available, use
the read-only `lean_blind_result_contract` MCP tool for each role. It accepts
the complete candidate JSON as text and returns the canonical `expected_type`,
`expected_type_sha256`, and `result_payload_sha256` without reading any file,
environment variable, or official answer. Do not try to calculate SHA-256 by
hand. If shell access happens to be available, the equivalent trusted helpers
are `lean_result_type_sha256` and `blind_result_payload_sha256` from
`archon.commands.loop.review_source_contract`.

Never put an official answer/alignment verdict in this record. Freeze and
grading occur later in a separate trusted phase.

The task result must record:

- the assumption/target split and all requested outputs;
- every image path inspected and the facts taken from it;
- LeanExplore queries, configured package filters, and verified declarations;
- source-to-Lean bridge obligations and their carriers;
- in answer-blind mode: the raw derivation, reporting-rule source, tolerance
  provenance, candidate-domain provenance, and whether the source is
  underdetermined;
- empirical facts represented as data or hypotheses;
- local abstractions and a countermodel-sufficiency check;
- any proposed shared-infrastructure request, including module, declarations,
  consumers, semantic contract, and why existing packages do not provide it.
