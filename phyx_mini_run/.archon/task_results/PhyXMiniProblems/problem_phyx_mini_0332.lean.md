# Prover result: `problem_phyx_mini_0332.lean`

## Status

Complete. Both `sorry` placeholders were replaced by proofs of the frozen
declarations.

## Proof

- `temperatureRiseInKelvins_eq_eighty` unfolds the temperature-rise
  definition, rewrites the final and initial Celsius readouts to `100` and
  `20`, and proves the resulting arithmetic equality.
- `problem_phyx_mini_0332` combines the calorimetry law with the problem-data
  equality identifying the reacted spray's specific heat with water's,
  substitutes `4190 J/(kg K)` and the derived `80 K` rise, and evaluates the
  heat of reaction as `335200 J/kg`.
- The unique-closest-answer claim is proved by cases on the four displayed
  choices. The distance from `335200` to A's `340000` is strictly smaller than
  the distances to B, C, and D; the A-versus-A case contradicts the required
  inequality of labels.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0332.lean`: exit code 0.
- Lean language-server diagnostics: none.
- `git diff --check`: exit code 0.
- Source scan: no `sorry`, `admit`, new `axiom`, `sorryAx`, or
  `native_decide`.
- Axiom audit for both proved declarations: only standard imported axioms
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint status

The lemma and target theorem are proof-closed and ready for automatic
`\leanok` synchronization. The blueprint was not edited because this prover
lane permits writes only to the assigned Lean file and this result file.

## Workflow note

The requested `.archon/AGENTS.md` is absent from this checkout, as documented
in `.archon/PROGRESS.md`. I read the available
`.archon/prover-modes/physics.md`, progress log, blueprint chapter, source
report, and physics-grounding report instead. The file-specific `USER:`
comment only records that the assigned Lean source did not exist when
autoformalization began.

## Redraft needed

None.
