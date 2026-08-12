---
name: chemistry
description: "Fill chemistry-domain Lean sorry placeholders without weakening the formalized source contract."
compatible_stages:
  - prover
read_blueprint: true
dispatcher_notes: |
  Use after `chemistry-formalize`. The declaration signatures are frozen;
  prove them from the encoded laws and data or report a precise redraft need.
---

## Your goal

Replace `sorry` bodies in the assigned chemistry Lean file with sound proofs.
Keep the formalized statement fixed and preserve its chemical meaning.

## Workflow

1. Read `PROGRESS.md`, the assigned Lean file, its blueprint chapter, source
   report, and newest matching formalizer task result.
   For `evaluation_mode: answer_blind`, do not seek or read any official answer,
   solution/rubric asset, old formalization, grader output, or other model's
   run. Seeing one is an integrity failure to report, not a proof hint.
2. Check that the theorem contains the governing relations and source data
   needed for the conclusion. First attempt the existing statement exactly.
3. Search the local project and the exact `lean_search_packages` recorded in
   the source report. With LeanExplore, pass the configured package filters
   (commonly Mathlib, Physlib, and an installed chemistry package such as CRNT)
   and verify candidate signatures before use.
4. Reduce chemistry relations to their mathematical obligations. Use suitable
   Mathlib lemmas and tactics such as `norm_num`, `ring_nf`, `field_simp`,
   `linarith`, or `nlinarith` only after their side conditions are available.
5. Compile after each meaningful proof change and preserve partial progress.

## Contract discipline

- Edit proof bodies only. Do not rename declarations, change binders,
  strengthen premises, weaken conclusions, or define the answer to make the
  theorem close by `rfl`.
- Do not introduce `axiom`, `unsafe`, `admit`, `sorryAx`, or fabricated
  chemical facts. Imported domain libraries provide definitions and theorems,
  not permission to assume an unproved empirical claim.
- Respect positivity, nonzero-denominator, logarithm/root domains, units or
  dimensional roles, uncertainty bounds, branches, phases, and species
  identities encoded by the statement.
- Previous-part results may be used only through the explicit hypotheses or
  verified shared declarations allowed by the source dependency policy.
- For an answer-blind target, preserve the raw end-to-end calculation and the
  predeclared reporting rule. Do not replace either with a staged rounded
  calculation, widen a measurement/reporting interval, or add a finite
  candidate bound merely because it closes the proof.
- Preserve the controller-fixed `requested_outputs` inventory and its
  per-output policies. Close every requested field/conjunct; do not apply one
  output's decimal precision to a formula, classification, integer, or a
  different numeric output.
- Treat a sound underdetermination or source-conflict theorem as a legitimate
  result. Do not force it into an unavailable official-answer shape.
- If the signature is underdetermined, contains the current answer as an
  assumption, or omits a source-required bridge, leave a focused `sorry` and
  report the smallest faithful redraft. Do not repair a modeling defect by
  weakening the theorem.

## Task result

Write only the assigned Lean file and its task-result report. In answer-blind
mode the existing `blind_candidates/<entry.id>.json` may be updated only to
keep its Lean declaration list and raw/reported result consistent with the
unchanged theorem contract; it must never gain grader or official-answer
fields. Recompute both `lean_result_contracts` payload/type hashes after any
permitted candidate change, and prove the exact generated types. Never replace
either carrier by `True` or an unrelated tautology. Record proofs
closed, verified library names, search evidence, remaining Lean goals/errors,
and any redraft or shared-infrastructure request with a concrete semantic
contract. In answer-blind mode also record whether proof work preserved the raw
derivation, reporting rule, tolerance provenance, and candidate-domain
provenance. Completion requires compilation, zero new axioms, and no remaining
soundly tractable `sorry` in scope.
