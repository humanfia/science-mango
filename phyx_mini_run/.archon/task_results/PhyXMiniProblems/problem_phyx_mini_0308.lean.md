# Prover result: `problem_phyx_mini_0308.lean`

## Status

Archon iteration 017, mandatory proof-review retry 2.

The frozen Lean declaration is proof-complete: its existing proof is sound,
compiles, and contains no placeholders.  The iteration-015 and iteration-016
proof reviews nevertheless correctly marked the target `blocked`, because the
declaration itself is weaker than the source and blueprint.  That semantic
defect cannot be repaired under the prover lane's rule that only the proof
body after `:= by` may be edited.

No change was made to the already valid proof body during this retry.

## Proof

- Unfolded the water-delay, air-calibrated delay-distance, and interpreted
  bearing-geometry hypotheses.
- Eliminated the common interaural delay to prove the cross-multiplied
  relation between the water-speed and air-speed path differences.
- Rewrote the actual submerged path difference with the bounded far-field
  residual identity.
- Reduced the target error to the absolute value of air speed times the
  stored residual, then applied the residual bound using positivity of the
  air-calibration speed.

This proves exactly the frozen residual-aware symbolic conjunction.  It does
not prove that the apparent angle is `13°` or that answer D is uniquely
closest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0308.lean`: exit code 0.
- Lean LSP diagnostics: no errors.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0308.lean`: exit
  code 0.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no
  warnings.

## Blueprint status

The target must not yet be marked `\leanok`: although the current Lean theorem
is closed, it does not implement the blueprint's numerical answer target.  The
blueprint was not edited because this prover lane permits changes only to the
assigned Lean file and this result file.

## Workflow note

The requested `.archon/AGENTS.md` is absent from this checkout. I read
`.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, the blueprint
chapter, and the source report instead. The file-specific `USER:` comment
states only that the source file did not exist when autoformalization began.

## Redraft needed

- Original problem: `phyx_mini_0308`.
- Source report: `reports/phyx_mini/problem_phyx_mini_0308.source.json`.
- Theorem:
  `PhyXMiniProblems.ProblemPhyXMini0308.submergedSound_interpretedAngle_is_thirteen_degrees`.
- Why: the conclusion is only a residual-aware speed-weighted identity and
  error bound.  It does not mention degree conversion, `13`, answer D, or
  unique closest-choice selection.  Moreover, the Lean file omits the
  blueprint declarations `radiansToDegrees`, `MatchesSoundSpeedData`,
  `MatchesIntendedSideOnArrival`,
  `SatisfiesExactSideOnSourceGeometry`, and `IsClosestAngleChoice`.  Therefore
  the `20°C` premise and answer-choice metadata cannot influence the result.
- Smallest faithful repair: restore those blueprint declarations; supply the
  `344 m/s` air and `1482 m/s` fresh-water readouts and the intended exact
  side-on/maximal-delay premise; include exact side-on geometry in
  `SatisfiesSoundLocalizationPhysics`; and change the target conclusion to
  state that `.D` is the unique closest displayed choice to
  `radiansToDegrees setup.interpretedBearingRadians`.  The proof can then
  derive
  `setup.interpretedBearingRadians = Real.arcsin (344 / 1482)` and certify with
  explicit bounds that its degree readout is closer to `13` than to `4`, `7`,
  or `10`.
