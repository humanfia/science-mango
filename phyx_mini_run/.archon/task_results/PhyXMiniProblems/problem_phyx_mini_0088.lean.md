# Prover result (Archon iteration 015)

## Status

Blocked by a frozen contract defect. The assigned Lean file already contains
closed, substantial proofs of
`firstMinimum_hasHalfWavelengthOpticalPath` and
`phaseDifferenceAtTwelveHundredNm_isChoiceC`; it has no remaining `sorry`.
There was therefore no sound proof-body edit to make in this retry.

The existing proof follows the intended optical argument rather than using an
explicit contradiction:

1. The figure readout gives the first minimum at
   `(5/6) * 900 nm = 750 nm`.
2. Positivity and the cosine interference law calibrate the linear phase to
   `π` at that first minimum.
3. The optical-path increment is linear in material length, so scaling from
   `750 nm` to `1200 nm` gives `(1200/750) * (1/2) λ = (4/5) λ`.
4. The phase law then gives `2π * (4/5) = 8π/5`.

The source image was inspected and does place the first minimum at the fifth
of six horizontal grid cells, consistent with the `750 nm` readout.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0088.lean` exits with
  status 0 and no output.
- Lean LSP diagnostics are empty.
- `lean_verify` reports no source warnings for either declaration. Its axiom
  lists contain only the standard imported axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `/- USER: ... -/` hint occurs in the assigned Lean file.
- The requested run-local `.archon/AGENTS.md` is absent, as
  `.archon/PROGRESS.md` itself records.

## Redraft needed

- Original problem id: `phyx_mini_0088`.
- Source report:
  `reports/phyx_mini/problem_phyx_mini_0088.source.json`.
- Theorem:
  `PhyXMiniProblems.ProblemPhyXMini0088.phaseDifferenceAtTwelveHundredNm_isChoiceC`.
- Affected intermediate lemma:
  `PhyXMiniProblems.ProblemPhyXMini0088.firstMinimum_hasHalfWavelengthOpticalPath`.
- Why the current statement is semantically wrong:
  `IsFirstStrictMinimumAfterZero` defines its strict-earlier-points condition
  as `∀ y ∈ Set.Ioc 0 x, f x < f y`. The interval `Set.Ioc 0 x` includes
  `x`, while the same predicate establishes `0 < x`; specializing at `y = x`
  therefore requires `f x < f x`. Consequently every
  `MatchesIntensityFigure experiment` premise is uninhabited, making both
  declarations vacuous contracts despite their non-ex-falso proof scripts.
- Smallest faithful change: in the body of
  `IsFirstStrictMinimumAfterZero`, replace `Set.Ioc 0 x` with
  `Set.Ioo 0 x`. Then change the existing witness supplied to
  `hMinimumIsFirst firstPiLength` from
  `⟨hFirstPiLengthPositive, hFirstPiLtMinimum.le⟩` to
  `⟨hFirstPiLengthPositive, hFirstPiLtMinimum⟩`.

That definition edit is outside the authorized surface: the task freezes every
declaration header and permits edits only after `:= by`. Editing it would
violate signature discipline, so the file was left unchanged.

## Blueprint handoff

The blueprint was read but not edited because this prover lane grants write
permission only for the assigned Lean file and this result file. In particular,
no `\leanok` marker was added while the contract remains semantically blocked.
