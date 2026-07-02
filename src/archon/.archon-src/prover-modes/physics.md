---
name: physics
description: "Fill physics/PhysLean sorry placeholders while preserving the auto-formalized statement."
compatible_stages:
  - prover
read_blueprint: true
dispatcher_notes: |
  Use for Lean files generated from blueprint chapters marked `% humanizephysics:physics`
  or by `humanizephysics physics-formalize`.
  This mode assumes the theorem signatures are the physics formalization
  contract; prove the existing statement, and report redraft needs instead of
  weakening or rewriting the formalization.
---

## Your goal

Fill `sorry` placeholders in an auto-formalized physics Lean file. The Lean
statement is the contract produced from the original text/image problem; keep that contract fixed and prove the body.

## Physics proof workflow

1. Read `PROGRESS.md`, then read the blueprint chapter named in the objective.
2. Read the Formalizer report linked from `PROGRESS.md` if one exists. For
   native `humanizephysics dag --physics` projects, read the physics blueprint chapter
   and `references/` files instead; those are the source of truth.
3. Inspect the assigned `.lean` file and identify every theorem/lemma with a
   `sorry`.
4. For each target, first try to prove the current statement exactly. Do not
   rename declarations, change hypotheses, weaken conclusions, replace a
   physical claim by `True`, or swap in a reflexive placeholder.
   Do not rename declarations, change hypotheses, weaken conclusions.
5. Prefer existing Mathlib/PhysLean APIs. Use the grounding names in the report
   and blueprint as search seeds.
6. When the proof is algebraic or numeric, reduce the physical assumptions to
   the stated formula and use standard arithmetic tactics (`norm_num`,
   `ring_nf`, `linarith`, `nlinarith`) as appropriate.
7. If the statement is not provable because the formalization is semantically
   wrong or misses a required physical law, keep the signature unchanged, leave
   a focused `sorry`, and record a redraft request in `task_results/<file>.md`.

**Write permissions**: only your assigned `.lean` file and
`task_results/<your_file>.md`. Do not edit the Formalizer report, blueprint
chapter, `PROGRESS.md`, or protected signatures.

## PhysLean and search protocol

- Search order: local Lean environment, PhysLean/Mathlib names from the
  Formalizer report or physics blueprint, LeanExplore semantic search, then
  Loogle-style type search.
- When using the official LeanExplore MCP, start with `search_summary`, pass
  `packages: ["Mathlib", "PhysLean"]` when the tool accepts package filters,
  and fetch source/module/docstring only for candidates you intend to use.
- Treat PhysLean modules as domain infrastructure, not as axioms. If a physical
  law is only present as a local hypothesis in the generated statement, use
  that hypothesis directly.
- If an imported PhysLean name is unavailable in this project, do not rewrite
  the theorem to avoid it. Record the missing import/name and the exact Lean
  error in the task result.

## Signature discipline

The declaration header is frozen. You may edit only the proof body after
`:= by`. You may edit only the proof body after `:= by`. If the theorem statement needs a redraft, report it under
`## Redraft needed` in the task result with:

- original problem id and report path,
- theorem name,
- why the current statement is not provable or is physically wrong,
- the smallest statement change that would make it faithful and provable.

## Completion criteria

Your task is complete only when:

1. Every assigned `sorry` you can soundly close is replaced by a proof.
2. The file compiles.
3. No axioms or `sorryAx`-style laundering were introduced.
4. Any remaining `sorry` has a specific blocker recorded in
   `task_results/<your_file>.md`.
