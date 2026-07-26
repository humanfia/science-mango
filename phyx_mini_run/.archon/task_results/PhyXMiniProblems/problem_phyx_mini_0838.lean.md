# Prover result: `problem_phyx_mini_0838.lean`

## Outcome

Complete. All four assigned proof obligations were closed without changing any
declaration signature:

- `requiredFieldStrength_eq_energyFormula`
- `requiredFieldStrength_numeric`
- `minimumPlateSpacing_eq_oneFourthHoleSeparation`
- `problem_phyx_mini_0838`

The field-strength proof derives `a Δt = -2 w` from the return-to-plate
condition. The perpendicular entry/exit velocity condition and positivity then
give equality of the positive tangential and normal entry speeds. Combining
this with the kinetic-energy and electric-force laws yields
`q E L = 2 K`, and hence `E = 2 K / (q L)`.

The numerical lemma proves the Physlib readout conversion
`centimeters = 100 * meters`, converts the stated `1 cm` separation to
`1/100 m`, and substitutes the kinetic-energy and elementary-charge
calibrations.

For the spacing result, the proof constructs a dimensionful length with SI
readout `L/4`. It rewrites the whole normal trajectory as
`w s (Δt - s) / Δt`, proves this lies between `0` and `L/4` throughout
transit, and constructs a dimensionful midpoint time where the height is
exactly `L/4`. Thus every adequate alternative spacing is at least `L/4`.
The final theorem converts `L/4` to `5/2 mm` and checks that D is the unique
matching displayed choice.

## Verification

- Lean language-server diagnostics: no errors. The sole warning is the
  intentionally retained frozen hypothesis `hScenario`, which the conclusion
  does not need.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0838.lean`: exit code 0.
- Root `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, `sorryAx`, or
  equivalent escape hatch.
- Axiom verification of the final theorem reports only Lean/Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint status

The proof environments for all three supporting lemmas and the final theorem
are ready for deterministic `\leanok` synchronization. The blueprint was not
edited because the prover role permits writes only to the assigned Lean file
and this result file.

## Redraft needed

None.

## Infrastructure note

The run-local `.archon/AGENTS.md` and the advertised `archon` executable were
absent. As directed by `.archon/PROGRESS.md`, the identical-SHA canonical
archive copy of `AGENTS.md` was read. No dependency-graph lemma was required
for this self-contained kinematics and algebra proof. The assigned file's
`/- USER: ... -/` comment only records that the source file was initially
absent and supplied no additional proof hint.
