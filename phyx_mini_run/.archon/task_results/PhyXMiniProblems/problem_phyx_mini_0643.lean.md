# Prover result: `problem_phyx_mini_0643.lean`

## Outcome

All seven assigned declarations are proof-closed with their frozen signatures
unchanged. No new declarations or axioms were introduced, and no redraft is
needed.

## `adjacent_fringe_spacing_micrometers_eq`

- **Approach:** Specialize linear figure calibration to micrometres, rewrite
  the five raster/scale-bar readouts, and solve the resulting linear equation.
- **Result:** RESOLVED — the spacing is `925 / 14 μm`.

## `matter_wavelength_femtometers_eq`

- **Approach:** Derive metre/nanometre/micrometre-to-femtometre conversion
  identities from the `Dimensionful` unit-coherence field, specialize the
  paraxial fringe law to femtometres, and substitute the calibrated values.
- **Result:** RESOLVED — the wavelength is `185 / 98 fm`.

## `neutron_speed_meters_per_second_eq`

- **Approach:** Convert the derived wavelength to metres, substitute the
  neutron mass and ordinary Planck action in the de Broglie law, and cancel the
  nonzero numeric denominator.
- **Result:** RESOLVED — the exact speed expression in the statement follows.

## `neutron_speed_in_physically_supported_interval`

- **Approach:** Prove `3.14 < π < 3.145` from the imported `Real.cos_bound`,
  five repeated double-angle identities, and cosine sign lemmas; combine these
  bounds with the exact speed expression.
- **Result:** RESOLVED — the speed is strictly between `209000000` and
  `210000000 m/s`.

## `neutron_speed_rounds_to_two_hundred_million`

- **Approach:** Use the speed interval to show that the relevant floor in
  `round_eq` is exactly `2`, with digit `2` and decimal exponent `8`.
- **Result:** RESOLVED — the speed rounds to `200000000 m/s` at one
  significant figure.

## `no_displayed_speed_matches`

- **Approach:** Show that any positive one-significant-figure report at most
  `300` would force the modeled speed below `450 m/s`, contradicting the
  physical interval; discharge all four answer-choice cases.
- **Result:** RESOLVED.

## `problem_phyx_mini_0643`

- **Approach:** Assemble the six proved intermediate conclusions.
- **Result:** RESOLVED.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0643.lean` passed.
- Lean LSP diagnostics contain only unused-variable warnings for the frozen
  contextual hypotheses `h_physical` in the exact-speed lemma and
  `h_scenario` in the final theorem.
- Source scan found no `sorry`, `admit`, introduced `axiom`, `sorryAx`,
  `native_decide`, or unsafe proof device.
- Axiom verification of the final theorem reports only standard dependencies:
  `propext`, `Classical.choice`, and `Quot.sound`.

## Source and blueprint readiness

- Original problem: `phyx_mini_0643`.
- Source report:
  `reports/phyx_mini/problem_phyx_mini_0643.source.json`.
- All seven proof environments in
  `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0643.tex` are
  ready for deterministic `\leanok` synchronization.
- The blueprint chapter was not edited because prover write permissions permit
  changes only to the assigned Lean file and this task-result file.
- The requested `.archon/AGENTS.md` was absent; the available
  `.archon/prover-modes/physics.md` role instructions were followed.

## Summary

- Sorry count: **7 → 0**.
- Closed:
  `adjacent_fringe_spacing_micrometers_eq`,
  `matter_wavelength_femtometers_eq`,
  `neutron_speed_meters_per_second_eq`,
  `neutron_speed_in_physically_supported_interval`,
  `neutron_speed_rounds_to_two_hundred_million`,
  `no_displayed_speed_matches`, and
  `problem_phyx_mini_0643`.
- Sorries still open: none.
- Adjacent sorries beyond the assigned declarations: none existed in this file.
- New declarations needing blueprint entries: none.

## Why I stopped

Real progress: all seven assigned sorries were closed, reducing the file from
seven sorries to zero; the file compiles and the final theorem passes the axiom
and source scan.
