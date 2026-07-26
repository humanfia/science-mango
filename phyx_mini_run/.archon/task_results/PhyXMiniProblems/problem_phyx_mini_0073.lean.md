# Prover result: `problem_phyx_mini_0073.lean`

## Status

Complete. The sole `sorry` was replaced by a sound proof without changing the
declaration header or any supporting definition.

## Proof summary

- Rear-face Snell's law, positivity, and principal-branch sine injectivity show
  that violet's rear incidence is zero. Prism geometry therefore makes its
  entrance refraction exactly `30°`.
- The violet and red entrance Snell laws, together with the `2%` dispersion
  relation, force the red entrance-refraction sine to equal `51 / 100`.
- Writing the red rear incidence as `x`, prism geometry turns this into
  `sin (π / 6 + x) = 51 / 100`. Elementary `sin_bound`/`cos_bound` estimates
  and sine monotonicity prove `π / 360 < x < π / 240`.
- The glass-index hypotheses give `1 < n_red < 99 / 50`. Rear-face Snell's law
  and the double-angle identity then bound the emerged red angle `φ` by
  `π / 360 < φ.toReal < π / 120`, i.e. strictly between `0.5°` and `1.5°`.
  This proves rounding to `1°` and makes choice C strictly closer than choices
  A, B, and D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0073.lean`: passed with no
  output.
- `lake build`: passed.
- Source scan: no `sorry`, `admit`, `sorryAx`, added `axiom`, or
  `native_decide`.
- `lean_verify` reports only the standard dependencies `propext`,
  `Classical.choice`, and `Quot.sound`; its suspicious-source scan is clean.

## Blueprint readiness

`PhyXMiniProblems.ProblemPhyXMini0073.redLightEmergenceAngle_is_choiceC` is
fully proved and ready for proof-block `\leanok`. The blueprint was not edited
because prover permissions reserve marker synchronization for the deterministic
`sync_leanok` phase.

## Redraft needed

None.
