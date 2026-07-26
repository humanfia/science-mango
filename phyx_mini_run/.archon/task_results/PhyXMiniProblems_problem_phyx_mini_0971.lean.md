# Prover result: `problem_phyx_mini_0971.lean`

## Status

Partial. The assigned file compiles and the existing proof completes the RC
impulse calculation, speed limit, ballistic height limit, and identification
of answer B. One focused `sorry` remains at
`hactualForceAEStronglyMeasurable`; it is not derivable from the frozen
hypotheses.

## Redraft needed

- Original problem: `phyx_mini_0971`
- Source report: `reports/phyx_mini/problem_phyx_mini_0971.source.json`
- Blocked theorem:
  `PhyXMiniProblems.ProblemPhyXMini0971.horizontal_kick_speed_tends_to_capacitor_impulse`
- Consequently affected target:
  `PhyXMiniProblems.ProblemPhyXMini0971.problem_phyx_mini_0971`

`SatisfiesNegligibleDisplacementAsymptotics.forceErrorIntegrable` assumes
integrability only of

```lean
fun elapsedSeconds =>
  |actualForce elapsedSeconds -
    fixedSeparationForcePerLengthSI setup elapsedSeconds|
```

This gives a.e. strong measurability of the absolute error, but not of the
signed error or the actual force. Nonnegativity of the two force magnitudes
does not recover the missing sign branch: around a positive measurable
reference force `f`, an actual force
`f * (1 + a(ratio) * s)` can use a nonmeasurable
`s : ℝ → {-1, 1}` while its absolute error is the measurable integrable
function `a(ratio) * f`. Taking `a(ratio) → 0` also satisfies the required
vanishing-error limit. Thus the actual force need not be Bochner measurable;
its Lean integral can then be zero, so the asserted positive impulse limit
does not follow.

The smallest faithful change is to make `forceErrorIntegrable` assert
`IntegrableOn` for the signed difference rather than its absolute value:

```lean
forceErrorIntegrable : ∀ ratio wire, 0 < ratio →
  MeasureTheory.IntegrableOn
    (fun elapsedSeconds : ℝ =>
      coherentSIValue
          (setup.forcePerLengthAtRatioSeconds ratio wire elapsedSeconds) -
        fixedSeparationForcePerLengthSI setup elapsedSeconds)
    (Set.Ioi 0)
```

For a real-valued function, this includes the missing a.e. strong
measurability and still implies integrability of the absolute error.
Equivalently, add an `IntegrableOn` premise for the actual force.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0971.lean` exited with
  code `0`.
- Lean reports only the expected declaration-uses-`sorry` warning plus unused
  lints for `hscenario` and `hfigure`.
- The source contains exactly one focused `sorry`; no axiom, `admit`,
  `native_decide`, or other proof escape hatch was introduced.

## Project notes

- The requested run-local `.archon/AGENTS.md` is absent, as
  `.archon/PROGRESS.md` also notes. The objective prompt and
  `.archon/prover-modes/physics.md` supplied the active role instructions.
- The blueprint chapter and `references/summary.md` were read. The blueprint
  was not edited because this prover lane explicitly restricts writes to the
  assigned Lean file and this task-result file; the unresolved intermediate
  theorem also prevents marking its dependency chain `\leanok`.
