# Iteration 022 Plan

## Batch contract

- Preserve exactly the three loop-selected Current Objectives below, in their
  existing order. All are mandatory proof-Review retries with 2/3 reviewed
  attempts used; no `proof_review_exhausted` target is scheduled.
- Eligibility shortfall: 29. Dispatch all three distinct eligible targets and
  leave 29 of the desired `max_parallel = 32` lanes unfilled; do not scan for,
  add, remove, reorder, or substitute objectives.
- This is each target's third and final reviewed attempt. Preserve every
  theorem statement and physical hypothesis. Test only consequences of the
  frozen assumptions; if a noted premise is genuinely absent, retain the
  single honest `sorry` and report the target as irreducibly blocked rather
  than introducing an escape hatch.
- The supplied excerpts expose no concrete blueprint strategy defect, so no
  listed blueprint chapter is edited. The three gaps are Lean-local missing
  hypotheses and must not be disguised by changing the supported physical
  account.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0909.lean` (retry; 2/3 used).**
   Normalize the force, Newton-law, and velocity-update equalities componentwise
   and use positive electron mass to derive the exact acceleration and exit
   velocity formulas. Close the vertical component by `eq_div_iff` followed by
   ring normalization. For the horizontal component, audit the existing
   hypotheses for an explicit consequence that the electric field's
   `xAxis` component is zero and rewrite with it if present. Otherwise stop:
   the displayed horizontal formula contains a generally nonzero
   `q E_x t / m` term, so horizontal-velocity preservation does not follow
   from the frozen hypotheses; keep the gap honest.

2. **`PhyXMiniProblems/problem_phyx_mini_0967.lean` (retry; 2/3 used).**
   Preserve the completed reverse-triangle estimate: rewrite the actual
   torque magnitude as the actual vector norm, use the remainder
   decomposition, and discharge its norm bound. Then audit only the supplied
   `SatisfiesFiniteApparatusTorqueApproximation` fields for an equality between
   the stored ideal scalar magnitude and the norm of the ideal torque vector.
   If such an equality is available, rewrite it and finish with
   `vector_norm_error`; otherwise the scalar is unconstrained because the
   needed identification belongs to the absent
   `SatisfiesMagneticDipoleTorqueLaw` hypothesis, so retain the final gap
   rather than importing that unassumed law.

3. **`PhyXMiniProblems/problem_phyx_mini_0971.lean` (retry; 2/3 used).**
   Keep the certified fixed-separation exponential integral, including the
   negative decay rate and all nonzero parameter side conditions. Before
   constructing actual-force integrability, audit the frozen assumptions for
   either signed-force `AEStronglyMeasurable` data or a pointwise sign branch
   that converts measurability of the absolute error into measurability of the
   signed error. If found, combine it with fixed-force measurability and the
   integrable error bound, then complete the integral comparison and limiting
   argument. If neither is present, stop at the isolated regularity lemma:
   integrability/measurability of an absolute error does not determine the
   measurability of its signed function, so the remaining claim is not
   derivable without strengthening the frozen hypotheses.
