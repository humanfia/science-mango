# Prover result: `problem_phyx_mini_0651.lean`

## Status

Complete. All three `sorry` placeholders were replaced by sound proofs without changing any declaration signature.

## Closed declarations

- `PhyXMiniProblems.ProblemPhyXMini0651.peakAmplitude_sq_eq_three`
  - Uses `MemHS` integrability, confinement support, normalization, and explicit integration of the rising and falling triangular branches.
- `PhyXMiniProblems.ProblemPhyXMini0651.firstQuarterProbability_eq_one_div_thirtySix`
  - Applies the Born rule on `[0, 1/4]`, integrates the squared rising branch, and substitutes the normalized peak-amplitude result.
- `PhyXMiniProblems.ProblemPhyXMini0651.problem_phyx_mini_0651`
  - Reuses the exact probability lemma and proves the thousandth rounding and unique closest answer choice by exact rational arithmetic.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0651.lean` — passed.
- `lake build` — passed.
- Source audit found no `sorry`, `admit`, `sorryAx`, `native_decide`, or added `axiom`.

## Blueprint markers

The theorem and both lemma proof environments are ready for `\leanok`. Per prover write restrictions, the blueprint chapter was not edited; the deterministic marker-sync phase should apply the markers.

## Redraft needed

None.
