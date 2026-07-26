# Prover result: `problem_phyx_mini_0127.lean`

## Status

Blocked by the frozen physical contract. The existing theorem proof is
complete and compiles, but the governing-law field has the wrong parse and
makes the scenario hypotheses inconsistent. No permitted edit to a proof body
after `:= by` can repair this declaration signature.

The assigned Lean file is byte-for-byte identical to the iteration-016
baseline, so no Lean edit was made.

## Review retry analysis

The field currently written as

```lean
∀ thicknessNm : ℝ, 0 < thicknessNm →
  setup.constructivelyReflectsGreenAtThicknessNm thicknessNm ↔
    ∃ order : ℕ, ...
```

parses as

```lean
∀ thicknessNm : ℝ,
  (0 < thicknessNm →
    setup.constructivelyReflectsGreenAtThicknessNm thicknessNm) ↔
      ∃ order : ℕ, ...
```

At `thicknessNm = 0`, the implication on the left is true, so the field forces
an order satisfying

```lean
0 = (2 * (order : ℝ) + 1) * 540
```

after applying the wavelength readout. No natural order satisfies that
equation. Therefore `MatchesSoapBubbleFigure setup` and
`ObeysThinFilmReflectionLaws setup` cannot be jointly instantiated, and the
theorem is physically vacuous.

The completed proof itself uses the law only at positive thicknesses. Its
order-zero calculation of `100 nm`, arbitrary-order lower bound, and
application to the actual positive thickness are algebraically correct.

## Redraft needed

- Original problem id: `phyx_mini_0127`
- Source report: `reports/phyx_mini/problem_phyx_mini_0127.source.json`
- Theorem:
  `PhyXMiniProblems.ProblemPhyXMini0127.smallestGreenFilmThickness_isRecordedChoiceC`
- Faulty declaration:
  `PhyXMiniProblems.ProblemPhyXMini0127.ObeysThinFilmReflectionLaws.constructiveReflectionIffOddQuarterWave`
- Why redraft is required: the current law quantifies an equivalence at every
  real thickness and is impossible at zero, so the theorem's setup has no
  physical model.
- Smallest faithful change: parenthesize the intended equivalence after the
  positivity premise:

```lean
∀ thicknessNm : ℝ, 0 < thicknessNm →
  (setup.constructivelyReflectsGreenAtThicknessNm thicknessNm ↔
    ∃ order : ℕ,
      4 * setup.refractiveIndex .soapFilm * thicknessNm =
        (2 * (order : ℝ) + 1) *
          nanometersValue setup.greenWavelengthInAir)
```

This signature change was not applied because prover permissions freeze
declaration headers and permit edits only to proof bodies. After an authorized
redraft, the theorem proof must supply the positivity premise before using the
resulting equivalence's `.1` or `.2` direction.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0127.lean` completed with
  exit code 0 and no diagnostics.
- The source scan found no `sorry`, `admit`, `native_decide`, `sorryAx`, user
  axiom, or `/- USER: ... -/` hint.
- The target theorem's axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The assigned file SHA-256 equals the iteration-016 baseline SHA-256:
  `aea9b8a4bb604f18c01c4b43d9c7edd8763cbc7a0099f9c7a42c198b2a14dec9`.

## Blueprint status

The blueprint was not edited, as prover write permissions exclude chapter
files. The theorem proof is syntactically closed, but the governing-law
contract must be redrafted before the physics target is ready to be marked
complete.
