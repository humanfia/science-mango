---
name: physics-formalize
description: "Formalize physics blueprint chapters into typed Lean/PhysLean declaration stubs with sorry bodies."
compatible_stages:
  - autoformalize
read_blueprint: true
dispatcher_notes: |
  Use for blueprint chapters marked `% archon:physics`.
  This mode creates compiling Lean statements with `sorry` bodies only; it does
  not attempt proofs and must preserve the physical modeling content.
---

## Your Goal

Read the assigned physics blueprint chapter and create a Lean file whose
declarations faithfully represent the theorem, lemmas, assumptions, parameters,
and figure-derived quantities in that chapter. The output is a compiling
by-sorry formalization, not a proof attempt.

## Required Workflow

1. Read `PROGRESS.md`, your assigned `.lean` path, and the matching blueprint
   chapter under `blueprint/src/chapters/`.
2. Confirm the chapter contains `% archon:physics`; if it does not, fall back to
   the ordinary `formalize` discipline.
3. Extract the physical model before writing Lean:
   - named quantities and their roles,
   - units or dimensional meaning when stated or implied,
   - geometry/figure labels,
   - physical laws used as assumptions,
   - final relation to be proved.
4. Build an explicit Assumption/target split before writing Lean:
   - governing laws,
   - previous-part results,
   - figure/data readouts,
   - current target conclusions.
   Current target conclusions must not appear as hypotheses, premise fields,
   `Laws` fields, `Valid...Physics` fields, `Satisfies...` predicates, or
   local definitions that make the theorem true by unfolding.
5. Build a derivability/bridge-obligation inventory before writing Lean.
   For every nontrivial step from the source assumptions to the requested
   output, name:
   - the source claim,
   - the Lean declaration, structure field, or library theorem that carries it,
   - whether that carrier is grounded, encoded locally, or still blocked.
   A compiling statement is not proof-ready when one of these bridges is
   missing. Every substantive target must record at least one bridge; a direct
   source-to-contract mapping should name the main theorem contract as carrier.
6. Use LeanExplore before inventing APIs:
   - Start with `mcp__lean-explore__search_summary` or `search_summary`.
   - Query both natural-language concepts and likely Lean names.
   - Always pass `packages: ["Mathlib", "Physlib"]` when the tool schema
     supports package filters.
   - Fetch source/module/docstring for only the candidates you intend to use.
7. Verify Lean syntax and available names with `archon-lean-lsp` diagnostics,
   hover, local search, or small snippets.
8. Write declarations with `sorry` bodies. The file must compile with only
   expected `sorry` warnings when you stop.

## Physics Modeling Rules

- Do not replace a physics statement with `True`, reflexive equality, or an
  unrelated algebraic tautology.
- Do not collapse basic physical primitives to transparent scalar aliases such
  as `abbrev Charge := ℝ`, `abbrev Current := ℝ`, or one-field wrappers like
  `structure Charge where val : ℝ` unless the blueprint explicitly asks for a
  scalar readout/projection rather than the physical quantity itself.
- If PhysLean lacks a ready-made object, introduce the smallest abstract type,
  structure, or hypothesis interface that preserves the physical role and laws
  needed by the statement. In short: use the smallest abstract type, structure,
  or hypothesis interface that keeps the physical meaning intact.
- Use the smallest abstract type, structure, or hypothesis interface that keeps
  the physical meaning intact.
- It is fine for final numeric values, coordinates, dimensionless ratios, and
  measured scalar components to be real numbers. Make the distinction explicit
  in names and hypotheses.
- Capture problem/figure parameters even when they do not appear in the final
  closed form, if they are part of the setup or later proof route.
- Prefer assumptions that state the physical law or modeling relation directly
  over local fake definitions that hide it.
- Do not make the current subquestion's answer an assumption. It is allowed to
  assume governing laws, calibrated measurements, figure/data readouts, and
  previous-part results, but the current target conclusion must remain on the
  conclusion side of the main theorem or a lemma that still requires proof.
- If a needed physical law is not available in Mathlib/PhysLean, introduce a
  faithful governing-law predicate or hypothesis. Do not replace it with the
  final formula that the current subquestion asks to prove.
- Every abstract `Prop`-valued relation that carries a substantive physical
  step must expose mathematical consequences usable by a proof: equations,
  inequalities, incidence/tangency conditions, derivatives, limits, or a
  reusable elimination theorem. Merely asserting that an opaque relation has
  a witness does not constrain the model and is not an adequate formalization.
- Run a countermodel sanity check on every local abstraction: if its fields can
  be interpreted arbitrarily while all assumptions remain true and the current
  conclusion becomes false, the contract is underdetermined and must be
  redrafted.
- Preserve uncertainty and error information from the source. When the source
  reports `value ± uncertainty`, the uncertainty must occur in the theorem
  contract and be propagated to the requested output, or the task result must
  justify why it is not applicable. A fixed tolerance around a central value
  is not uncertainty propagation by itself.
- Preserve branch and orientation information needed for signed answers:
  incoming/outgoing, future/past, clockwise/counterclockwise, tangent branch,
  and asymptotic direction must be represented by hypotheses or derived
  bridge lemmas rather than selected only in the final conclusion.
- `rfl` or definition-unfolding may prove naming/helper expansions only. It
  must not close the current subquestion's substantive answer by defining that
  answer as the target relation itself.

## Search Discipline

Use search results as grounding, not as decoration:

- If LeanExplore finds a matching Mathlib/PhysLean declaration, use its actual
  name and compatible signature.
- If candidates are near misses, record the mismatch in the task result and use
  a faithful local abstraction instead of guessing an unavailable name.
- If no candidate exists, say so in the task result under `## Grounding gaps`.

## Write Permissions

You may edit only:

- your assigned `.lean` file,
- `task_results/<your_file>.md`.

Do not edit blueprint chapters, `PROGRESS.md`, task state files, or protected
signatures.

## Task Result

Write `task_results/<your_file>.md` with:

- `## Assumption/target split` listing governing laws, previous-part results,
  figure/data readouts, and current target conclusions,
- `## Goal-faithfulness audit` explaining why no current target conclusion was
  smuggled into hypotheses, premise structures, or local definitions,
- `## Derivability and bridge obligations` with one entry per nontrivial
  source-to-Lean reasoning bridge, its Lean carrier, evidence, and
  `covered`/`blocked` status,
- `## Abstraction sufficiency and countermodel audit` listing every local
  `Prop`-valued interface and the equations/inequalities/elimination theorem
  that make it constraining,
- `## Uncertainty and branch coverage` recording whether each is
  `covered`, `blocked`, or genuinely `not applicable`,
- declarations created and corresponding blueprint labels,
- LeanExplore queries/candidates actually used,
- PhysLean/Mathlib names grounded,
- local abstractions introduced and why they preserve the physical meaning,
- any grounding gaps or redraft requests.
