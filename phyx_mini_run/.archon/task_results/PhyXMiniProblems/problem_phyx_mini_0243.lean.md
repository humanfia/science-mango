# Prover result: `problem_phyx_mini_0243.lean`

## Status

Complete. Both `sorry` placeholders were replaced with proofs of their frozen
statements.

## Proofs

- `angleDuringWaveTravel_massRatio` uses the figure equality between orbit
  radius and cord length together with the density, centripetal-tension,
  transverse-wave, travel-time, and constant-angular-speed laws. Positivity
  justifies the square-root identity and denominator clearing; after squaring,
  the cord length and angular speed cancel to give
  `theta = sqrt (cordMass / blockMass)`.
- `angleDuringWaveTravel_matches_recordedAnswerD` substitutes the stated masses
  into the derived ratio and proves that `sqrt (8 / 1125)` lies within
  `1 / 20000` rad of `843 / 10000` rad by comparing exact squares.

## Verification

- Lean LSP diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0243.lean`: exit code 0.
- `git diff --check`: exit code 0.
- Source scan: no `sorry`, `admit`, new `axiom`, `sorryAx`, or
  `native_decide`.
- Axiom audit: only standard imported axioms `propext`, `Classical.choice`,
  and `Quot.sound`.

## Blueprint status

The target theorem and supporting lemma are proof-closed and ready for
automatic `\leanok` synchronization. The blueprint was not edited because the
prover lane permits writes only to the assigned Lean file and this result file.

## Workflow note

The requested `.archon/AGENTS.md` is absent from this checkout. I read
`.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, the complete blueprint
chapter, grounding log, references summary, and source report instead. No
file-specific `USER:` comment was present. The prompt also advertised `archon`
on `PATH`, but that executable was unavailable, so the optional dependency-graph
query could not run.

## Redraft needed

None.
