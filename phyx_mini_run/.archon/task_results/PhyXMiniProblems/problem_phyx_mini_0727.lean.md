# Prover result: `problem_phyx_mini_0727.lean`

## Completed

- Replaced the sole `sorry` in
  `PhyXMiniProblems.ProblemPhyXMini0727.earthSunDistanceInLightYears`.
- Used `SatisfiesAstronomicalDefinitions.astronomicalUnitIsEarthSunDistance`
  and `MatchesReportedAstronomicalData.oneAstronomicalUnitReadout` to obtain
  the one-AU calibration for the Earth--Sun distance.
- Applied the `Dimensionful` coherence property between the AU and light-year
  unit choices to derive the exact readout
  `LengthUnit.astronomicalUnits.val / LengthUnit.lightYears.val`.
- Discharged the stated approximation tolerance and all three competing
  answer-choice inequalities by exact `norm_num` arithmetic on Physlib's AU
  and light-year definitions.

## Verification

- `archon-lean-lsp` diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0727.lean`: exit code 0.
- Source scan: no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Theorem axiom report contains only the standard imported foundations
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint note

The target blueprint environment was not marked `\leanok` because the current
prover write permissions explicitly restrict edits to the assigned Lean file
and this result file. The marker-sync or blueprint-maintenance stage should
add it.

## Project instruction note

The requested `.archon/AGENTS.md` is absent in this workspace. I followed the
available `.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, and the
current task instructions.

## Redraft needed

None.
