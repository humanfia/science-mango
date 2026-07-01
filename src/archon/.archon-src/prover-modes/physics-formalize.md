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
4. Use LeanExplore before inventing APIs:
   - Start with `mcp__lean-explore__search_summary` or `search_summary`.
   - Query both natural-language concepts and likely Lean names.
   - Always pass `packages: ["Mathlib", "Physlib"]` when the tool schema
     supports package filters.
   - Fetch source/module/docstring for only the candidates you intend to use.
5. Verify Lean syntax and available names with `archon-lean-lsp` diagnostics,
   hover, local search, or small snippets.
6. Write declarations with `sorry` bodies. The file must compile with only
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

- declarations created and corresponding blueprint labels,
- LeanExplore queries/candidates actually used,
- PhysLean/Mathlib names grounded,
- local abstractions introduced and why they preserve the physical meaning,
- any grounding gaps or redraft requests.
