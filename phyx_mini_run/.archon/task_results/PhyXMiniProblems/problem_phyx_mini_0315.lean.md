# Prover result: `problem_phyx_mini_0315.lean`

## Status

Complete. Both assigned placeholders were replaced by sound proofs, and the
file contains no remaining `sorry` or `admit`.

## Proof summary

- `pathDifference_eq_pi_sub_two_mul_radius` unfolds the centimeter instance
  of the general path-difference and semicircular-geometry laws. Positivity of
  the radius and the strict inequality `2 < π` remove the absolute value, and
  ring normalization gives `ΔL = (π - 2) r`.
- `smallestRadius_selects_answerD` constructs a physical radius by scaling the
  supplied dimensionful wavelength by the positive `NNReal` factor
  `1 / (2 * (π - 2))`. Its centimeter readout is therefore
  `20 / (π - 2)`.
- The order-zero branch of the destructive-interference equivalence proves
  that this radius produces a detector minimum in every length unit.
- For any other positive minimum, the natural interference order is
  nonnegative, so its path difference is at least half the `40 cm`
  wavelength. Dividing by the positive factor `π - 2` proves universal
  minimality.
- The frozen imports expose only coarse built-in bounds on `π`. The proof
  derives `3.14 < π < 3.1416` locally from the imported sine error estimate,
  half-angle formula, and nested-square-root series. These bounds prove that
  the exact radius lies within `0.05 cm` of `17.5 cm`, selecting recorded
  choice D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0315.lean`: exit code 0.
- Lean LSP diagnostics: no errors. The sole warning is that frozen hypothesis
  `hFigure` is not explicitly referenced; the figure predicate contains no
  numerical radius data needed after the governing-law hypotheses are given.
- Source scan: no `sorry`, `admit`, `sorryAx`, new `axiom`, `native_decide`,
  metaprogramming, or unsafe declaration.
- `git diff --check`: no whitespace errors.
- `lean_verify` reports only `propext`, `Classical.choice`, and `Quot.sound`
  for both proved declarations, with no source warnings.

## Blueprint handoff

The proved target is
`PhyXMiniProblems.ProblemPhyXMini0315.smallestRadius_selects_answerD`, blueprint
label `thm:physics:phyx_mini_0315:target`. The helper lemma
`pathDifference_eq_pi_sub_two_mul_radius` is also proved. The orchestrator
should add the corresponding `\leanok` markers: prover permissions explicitly
allow edits only to the assigned Lean file and this task-result file, and
forbid editing the blueprint chapter directly.

## Redraft needed

None. Original problem id: `phyx_mini_0315`. Source report:
`reports/phyx_mini/problem_phyx_mini_0315.source.json`.

## Environment notes

The requested `.archon/AGENTS.md` is absent from this workspace and from
`HEAD`; `.archon/prover-modes/physics.md` was read as the available project
role document. The assigned Lean file has no file-specific `USER:` comment.
