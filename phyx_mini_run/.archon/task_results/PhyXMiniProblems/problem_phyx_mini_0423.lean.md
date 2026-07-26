# Prover result: `problem_phyx_mini_0423.lean`

## Outcome

Closed all four proof obligations without changing any declaration signature:

- `cycle_work_input_in_joules`
- `cold_reservoir_heat_absorbed_in_joules`
- `refrigerator_coefficient_of_performance_exact`
- `refrigerator_coefficient_of_performance`

The proof derives zero work on both isochoric legs from the figure process
classifications and the cycle laws. Thus the signed adiabatic work readouts
give a cycle work input of `-(-119 + 78) = 41 J`.

For the cold-reservoir heat, the proof uses zero heat on the adiabatic legs,
zero work on the isochoric legs, the `-105 J` heat into the system on the left
isochore, the first law on every leg, and closure of internal energy over the
cycle. These relations give `64 J` of heat entering on the right isochore.

The COP law then gives `COP * 41 = 64`, hence `COP = 64 / 41`. Direct rational
arithmetic proves that this value rounds to `1.6` under
`RoundsToDisplayedTenth` and is strictly closer to answer D than to A, B, or C.

## Verification

- Lean language-server diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0423.lean`: exit code 0.
- `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, added `axiom`, `native_decide`, or
  `sorryAx`-style escape hatch.
- Axiom verification of the final theorem reports only Lean/Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint status

The theorem environments for all four declarations are ready for deterministic
`\leanok` synchronization. The blueprint was not edited because the prover
role permits writes only to the assigned Lean file and this result file.

## Redraft needed

None.

## Infrastructure note

The run-local `.archon/AGENTS.md` and the advertised `archon` executable were
absent. As directed by `.archon/PROGRESS.md`, the canonical archive copy of
`AGENTS.md` was read; no dependency-graph lemma was needed for this
self-contained algebraic proof.
