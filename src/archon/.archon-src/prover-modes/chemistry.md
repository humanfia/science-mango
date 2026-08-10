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
- If the signature is underdetermined, contains the current answer as an
  assumption, or omits a source-required bridge, leave a focused `sorry` and
  report the smallest faithful redraft. Do not repair a modeling defect by
  weakening the theorem.

## Task result

Write only the assigned Lean file and its task-result report. Record proofs
closed, verified library names, search evidence, remaining Lean goals/errors,
and any redraft or shared-infrastructure request with a concrete semantic
contract. Completion requires compilation, zero new axioms, and no remaining
soundly tractable `sorry` in scope.
