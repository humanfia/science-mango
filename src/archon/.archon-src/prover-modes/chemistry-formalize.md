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
2. Read every path in `entry.image_paths` (or the legacy `entry.image_path`).
   Images may carry different pages of a table, molecular structure, spectrum,
   graph, apparatus, or reaction scheme. Do not silently use only the first.
3. Inventory the source contract before writing Lean:
   - species, isotopes, phases, reactions, structures, and named samples;
   - quantities, units, signs, significant/error bounds, and conditions;
   - supplied empirical data and governing chemical or mathematical laws;
   - previous-part conclusions that are explicitly reusable;
   - every conclusion requested by the current subquestion.
4. Write an explicit assumption/target split. The recorded answer may guide
   validation, but the current answer must not be copied into a premise,
   structure field, definition, or opaque predicate that makes the theorem
   true by unfolding.
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

## Chemistry modeling rules

- Preserve conservation equations, stoichiometric coefficients, charge,
  nonnegativity/positivity conditions, domains of logarithms and roots, and
  approximation or uncertainty bounds whenever the source uses them.
- Distinguish chemical entities from scalar readouts. Moles, concentrations,
  masses, energies, potentials, rates, and dimensionless ratios may be modeled
  numerically when that is the source's abstraction; do not erase species,
  phase, reaction, or sample identity when it affects the conclusion.
- Empirical constants and chemical facts are not mathematical axioms supplied
  by Lean. Use sourced data from the problem, a verified library declaration,
  or an explicit hypothesis. Never invent atomic masses, equilibrium
  constants, spectra, colors, structures, or reaction products.
- Encode a governing relation strongly enough to derive the target. An opaque
  `Prop` with no equations, inequalities, or elimination theorem is not an
  adequate bridge.
- Treat `previous_parts` according to each `dependency_policy`. A natural
  language prerequisite may be restated as an explicit hypothesis; do not
  import another generated problem file when the policy forbids it.
- Preserve alternatives and branches (species assignment, stereochemistry,
  sign, oxidation state, root, pathway) rather than selecting the recorded
  answer in a definition.
- Do not replace the requested result with `True`, a reflexive equality, an
  existence witness disconnected from the chemistry, or an unrelated numeric
  tautology.

## Write scope and task result

Edit only the assigned `.lean` file and its task-result report. Do not edit the
blueprint, source report, `PROGRESS.md`, shared modules, or dependency files.

The task result must record:

- the assumption/target split and all requested outputs;
- every image path inspected and the facts taken from it;
- LeanExplore queries, configured package filters, and verified declarations;
- source-to-Lean bridge obligations and their carriers;
- empirical facts represented as data or hypotheses;
- local abstractions and a countermodel-sufficiency check;
- any proposed shared-infrastructure request, including module, declarations,
  consumers, semantic contract, and why existing packages do not provide it.
