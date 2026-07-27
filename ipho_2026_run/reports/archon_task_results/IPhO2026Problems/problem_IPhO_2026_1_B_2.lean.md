# Prover result: IPhO 2026 problem 1, B.2

## Status

Partial. The assigned file compiles, with one focused `sorry` remaining in the
local lemma `signed_deflection_formula`.

The theorem signature and all physical hypotheses were preserved. A
theorem-scoped heartbeat budget was added because the exact algebraic and
transcendental certificate exceeds Lean's default budget.

## Formal progress

The proof now establishes:

- the initial speed from the individual angular momentum;
- the initial energy and total angular momentum;
- the hyperbolic eccentricity `orbit.eccentricity = 7 / 2`;
- convergence of the polar cosine, and of the normalized displacement's
  periapsis-axis component, to `2 / 7`;
- the exact numerical enclosure
  `3319 * π / 36000 ≤ arcsin (2 / 7) ≤ 3321 * π / 36000`;
- consequently,
  `16.595 ≤ arcsin (2 / 7) * 180 / π ≤ 16.605`, so the negative angle is
  strictly negative and rounds to `-83 / 5 = -16.60`.

The numerical enclosure is proved internally from `Real.sin_bound`,
`Real.cos_bound`, and repeated double-angle formulas. It first certifies
`3.1415 < π < 3.1416`; it does not rely on an unproved floating-point
evaluation.

## Remaining blocker

The supplied conic laws determine the asymptotic **position** axis component,
but expose no governing-law projection identifying the nonzero limiting
relative velocity with the clockwise outgoing branch of that conic. The
remaining focused goal is

```lean
signedDeflectionDegrees motion frame uInfinity =
  -Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi
```

Once this branch identity is available, the now-complete sign and
nearest-hundredth proof closes the theorem immediately.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_1_B_2.lean`: exit code 0.
- Source scan: exactly one `sorry`; no `admit`, declared `axiom`,
  `native_decide`, or explicit `sorryAx`.
- Axiom verification reports `sorryAx` from that remaining placeholder, plus
  the standard `propext`, `Classical.choice`, and `Quot.sound`.
- No `/- USER: ... -/` hint was present.

## Blueprint status

The target proof environment is not ready for `\leanok`, because the focused
branch-identification `sorry` remains. The prover did not edit the blueprint;
the deterministic synchronization phase owns `\leanok`.

## Redraft needed

- Original problem: `IPhO_2026_1`, part `B.2`.
- Source report:
  `reports/ipho_2026/problem_IPhO_2026_1_B_2.source.json`.
- Theorem:
  `IPhO2026Problems.IPhO2026_1_B_2.IPhO_2026_1_B_2`.
- Reason: the governing-law record supplies a polar locus and the theorem
  supplies a limiting velocity, but no stated outgoing-asymptote branch law
  connects their signed directions.
- Smallest faithful repair: add a governing-law hypothesis, parameterized by
  the nonzero limiting relative velocity, stating the standard hyperbolic
  outgoing-asymptote relation

  ```lean
  (frame.orientation.oangle
      (velocitySI motion .positron 0) uInfinity).toReal =
    -Real.arcsin (1 / orbit.eccentricity)
  ```

  under the existing unbound and limiting-velocity hypotheses. This contains
  no problem-specific decimal; the existing proof derives
  `orbit.eccentricity = 7 / 2` and certifies the `-16.60°` rounding.
