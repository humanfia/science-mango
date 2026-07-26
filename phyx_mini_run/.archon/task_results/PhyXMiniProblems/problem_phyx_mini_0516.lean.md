# Prover result: problem_phyx_mini_0516.lean

## Status

Complete. Both `sorry` placeholders were replaced by sound proofs, and the
assigned Lean file compiles.

## Proof summary

- `planck_constant_eq_charge_mul_fitted_slope`: evaluated the fitted-line
  form of Einstein's photoelectric equation at frequencies zero and one, then
  subtracted the resulting polynomial equalities to identify
  `h = e * fittedSlope`.
- `problem_phyx_mini_0516`: proved the Physlib unit conversion
  `wavelength_nm = 10^9 * wavelength_m`, used `λ f = c` and the rounded
  `c = 3 * 10^8 m/s` calibration to obtain the frequency of every table row,
  explicitly enumerated all six rows, and reduced the least-squares slope to
  the exact rational
  `278242157280470045475267 /
  67659078620283277055000000000000000000`.
  Multiplication by the supplied `e = 1.6 * 10^-19 C` calibration gives
  approximately `6.57986276 * 10^-34 J s`. Exact rational arithmetic proves
  agreement with `6.58 * 10^-34 J s` at the stated half-unit tolerance and
  excludes choices A, B, and C.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0516.lean` exits with
  code 0.
- The only diagnostics are unused-hypothesis linter warnings for the frozen
  signature's `hphysical`, `hscenario`, and `hplot` arguments.
- The theorem-level axiom/source scan reports only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx`, `sorry`, `admit`, new
  axiom, or escape hatch remains.

## Environment notes

- The requested `.archon/AGENTS.md` does not exist in this project checkout.
  The supplied prover objective and `.archon/PROGRESS.md` were followed.
- The blueprint environments were not marked `\leanok` because this prover
  task's write permissions explicitly allow edits only to the assigned Lean
  file and this result file.
