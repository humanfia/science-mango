# Prover result — Archon iteration 014

## Outcome

- Closed both placeholders in
  `PhyXMiniProblems/problem_phyx_mini_0137.lean`.
- `apparent_depth_index_relation` derives
  `n_water * d' = n_air * d` by differentiating the exact eventual Snell-law
  equality at the optical axis, transferring the derivative across the
  eventual equality between `thetaTwo` and `thetaTwoPrime`, and using
  derivative uniqueness.
- Because the frozen imports expose `Real.sin_bound` but not Mathlib's
  packaged `HasDerivAt.sin` theorem, the proof establishes
  `HasDerivAt Real.sin 1 0` directly from that Taylor remainder bound. It then
  composes the little-o remainder with each angle profile and scales it by the
  appropriate refractive index.
- Positivity of the real and apparent depth readouts supplies the nonzero
  denominators needed to cross-multiply the slope identity soundly.
- `problem_phyx_mini_0137` specializes the index relation to metres, rewrites
  `n_water = 4/3`, `n_air = 1`, and `d = 1.0 m`, and proves
  `d' = 0.75 m`; unfolding the answer table proves displayed choice C.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0137.lean` succeeded with
  no diagnostics.
- `lake build` succeeded (`Build completed successfully (4 jobs)`).
- Lean LSP diagnostics report no errors or warnings.
- Source scan found no `sorry`, `admit`, `axiom`, `sorryAx`,
  `native_decide`, or `/- USER: ... -/` marker.
- Axiom verification for both
  `PhyXMiniProblems.ProblemPhyXMini0137.apparent_depth_index_relation` and
  `PhyXMiniProblems.ProblemPhyXMini0137.problem_phyx_mini_0137` reports only
  the standard imported axioms `propext`, `Classical.choice`, and
  `Quot.sound`, with no source warnings.

## Redraft needed

None. Both frozen statements are faithful and provable from their stated
physics hypotheses.

## Blueprint status

The proof declarations are ready for `\leanok`. The explicit prover
write-permission block makes the blueprint chapter read-only in this task, so
the project synchronization/blueprint agent should apply the markers. The
existing autoformalization note below also records that the chapter's
generated topology prose should be refreshed to describe the local derivative
contract rather than the superseded global linearized equalities.

## Environment note

The requested `.archon/AGENTS.md` is absent in this project state. The
available `.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, physics
blueprint chapter, source report, references summary, and existing grounding
report were read and followed.

# Autoformalization result: `problem_phyx_mini_0137.lean`

## Assumption/target split

### Governing laws

- `SatisfiesExactWaterAirSnellLaw` requires the exact relation
  `n_water * sin θ₁(x) = n_air * sin θ₂'(x)` for every sufficiently
  near-axis ray, in every selected length unit. It does not linearize either
  sine.
- `SatisfiesParaxialApparentDepthLaws` is now a genuinely local first-order
  contract. All angle profiles vanish at zero lateral offset, and
  `HasDerivAt` records the slopes `1/d` for `θ₁` and `1/d'` for the apparent
  backward angle `θ₂`. By Mathlib's definition, each `HasDerivAt` statement
  includes a little-o remainder at the optical axis.
- `MatchesPoolGogglesFigure.backProjectionAngle` identifies `θ₂` and `θ₂'`
  near the axis because the emerging ray and its backward extension are the
  same line measured from parallel vertical normals. This is exact geometry,
  not a small-angle approximation.
- `HasPhysicalApparentDepthParameters` gives positivity of refractive indices
  and of the three physical lengths in every unit readout, selecting the
  physical apparent-depth branch.

### Previous-part results

- None. The source report has `previous_parts: []`, and this item is a
  standalone multiple-choice problem.

### Figure/data readouts

- `PoolGogglesDiagram` stores dimensionful `d`, `d'`, and the depicted common
  offset `x`; dimensionless refractive indices; the offset-indexed angle
  profiles carrying the printed labels `θ₁`, `θ₂`, and `θ₂'`; and the viewing
  regime.
- `MatchesPoolGogglesFigure` records the source value `d = 1.0 m`, straight-down
  viewing, and the backward-extension geometry visible in
  `phyx_data/test_image/137.png`.
- `RayPathLabel` retains the two solid physical rays and the dashed apparent
  back-projection shown in the raster.
- `UsesStandardWaterAirIndices` makes the auxiliary textbook index model
  explicit: `n_water = 4/3` and `n_air = 1`. These numbers are not claimed to
  be printed in the source; they are the standard idealized water/air data
  needed for its recorded `0.75 m` answer.
- `displayedApparentDepthMetres` records all four answer-choice readouts from
  the source.

### Current target conclusions

- `apparent_depth_index_relation` concludes, rather than assumes,
  `n_water * d' = n_air * d` in any length unit by differentiating exact
  near-axis Snell refraction and combining the local geometric slopes.
- `problem_phyx_mini_0137` concludes that the metre readout of the first-order
  apparent depth is exactly `0.75` and that it agrees with displayed choice C.

## Goal-faithfulness audit

- `PoolGogglesDiagram.apparentDepth` is an unconstrained dimensionful input.
  It is not defined as `0.75 m`, as an index ratio, or from an answer choice.
- No premise contains the derived index/depth equality or the requested
  numerical value. The derivative fields separately tie independently named
  angle profiles to `d` and `d'`; exact Snell law must still be differentiated
  and the two ray profiles related before the intermediate theorem follows.
- The numeric inputs `d = 1`, `n_water = 4/3`, and `n_air = 1` do not determine
  `d'` without the exact optical law and local derivative geometry.
- The answer table contains `C ↦ 0.75` only as source metadata and is not a
  theorem hypothesis. The theorem's first conjunct is the substantive
  optical conclusion; the second conjunct connects that result to the printed
  answer label.
- The rejected global fields `n_water θ₁ = n_air θ₂`, `x = d θ₁`, and
  `x = d' θ₂'` were removed. The revised model therefore does not assert a
  finite-angle approximation as an exact operating-ray equality.

## Declarations and blueprint labels

- `PhyXMiniProblems.ProblemPhyXMini0137.problem_phyx_mini_0137` corresponds to
  `thm:physics:phyx_mini_0137:target`.
- `apparent_depth_index_relation` corresponds to
  `lem:physics:phyx-mini-0137:phyxminiproblems-problemphyxmini0137-apparent-depth-index-relation`.
- The supporting declarations retained from the chapter topology are
  `DimLength`, `lengthReadout`, `lengthInMetres`, `OpticalMedium`,
  `RayPathLabel`, `FigureAngleLabel`, `ViewingRegime`, `PoolGogglesDiagram`,
  `MatchesPoolGogglesFigure`, `UsesStandardWaterAirIndices`,
  `HasPhysicalApparentDepthParameters`, `SatisfiesExactWaterAirSnellLaw`,
  `SatisfiesParaxialApparentDepthLaws`, `AnswerChoice`,
  `displayedApparentDepthMetres`, and `IsDisplayedApparentDepthAnswer`.

## LeanExplore queries/candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `Snell law refraction refractive index optical
  interface` returned no relevant geometrical-optics API. The returned
  `PolynomialLaw.*`, tactic-interface, and ideal-gas declarations were
  incompatible and were not used.
- Natural-language/likely-name query `HasDerivAt derivative at a point real
  functions` returned `HasDerivAt` (id `124761`), `deriv`,
  `DifferentiableAt.hasDerivAt`, and derivative lemmas. The source, module,
  and docstring of `HasDerivAt` were fetched; it is the local remainder
  contract used in the revised model.
- Natural-language query `dimensionful physical length unit metres readout`
  returned `Dimensionful` (id `394284`), `Dimension.L𝓭` (id `394324`),
  `CarriesDimension.toDimensionful`, and `UnitExamples.meters400`. Source,
  module, and docstrings were fetched for `Dimensionful` and `Dimension.L𝓭`.
- Likely-name query `Real.sin` returned `Real.sin` (id `128819`); its source,
  module, and docstring were fetched before using it in exact Snell law.
- Likely-name query `Filter.Eventually` returned `Filter.Eventually`
  (id `284497`) and `Filter.EventuallyEq`; source, module, and docstring were
  fetched for `Filter.Eventually`, which underlies the `∀ᶠ` near-axis laws.
- Likely-name query `LengthUnit.meters` returned nearby Physlib length units
  but not the exact declaration. Its actual signature and import module were
  verified with Lean LSP hover and the installed Physlib source.

## Physlib/Mathlib names grounded

- Mathlib: `HasDerivAt` from
  `Mathlib.Analysis.Calculus.Deriv.Basic`, `Real.sin`,
  `Filter.Eventually`/`∀ᶠ`, and the neighborhood notation `𝓝` under the
  `Topology` scope.
- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices`,
  `UnitChoices.SI`, `LengthUnit`, and `LengthUnit.meters`.
- Lean LSP hover confirmed the exact signatures of `HasDerivAt`,
  `Dimensionful`, and `LengthUnit.meters` in the compiled file.

## Local abstractions introduced

- `OpticalMedium`, `RayPathLabel`, `FigureAngleLabel`, and `ViewingRegime`
  preserve the media, ray, printed-angle, and observation roles without
  collapsing physical objects into undifferentiated real scalars.
- `PoolGogglesDiagram` uses Physlib dimensionful lengths. Its real-valued
  fields are only dimensionless refractive-index/radian readouts and scalar
  coordinates supplied after a `LengthUnit` is selected.
- The offset-indexed angle family is the smallest local addition needed to
  state exact near-axis Snell refraction and first-order geometry honestly.
- `SatisfiesExactWaterAirSnellLaw` and
  `SatisfiesParaxialApparentDepthLaws` remain local abstractions because
  LeanExplore found no compatible Mathlib/Physlib Snell-law or apparent-depth
  object. They state physical laws and local asymptotics, not the answer.

## Source/law/answer audit

- Source/figure evidence: `d = 1.0 m`, straight-down viewing, the labels
  `x`, `d'`, `θ₁`, `θ₂`, `θ₂'`, the physical/back-projected rays, and answer
  choices A--D were checked against the source JSON and raster.
- Governing/tabulated model: exact Snell refraction, local ray derivatives,
  positive physical branches, and idealized water/air indices are explicit
  premises rather than silently embedded definitions.
- Answer: `0.75 m`, choice C, appears only in answer metadata and in the final
  target conclusion.

## Grounding gaps and redraft requests

- No reusable Snell-law, refractive-index, or apparent-depth optics API was
  found in Mathlib/Physlib, so faithful local predicates were necessary.
- The checked-in blueprint chapter still describes the superseded global
  linearized equalities in its generated declaration-topology prose. The
  explicit write permissions prohibit editing blueprint chapters in this
  task, so the plan/synchronization agent should refresh that prose and add
  `\leanok` after accepting the revised local-derivative declarations.
- The requested `.archon/AGENTS.md` is absent; the available
  `.archon/prover-modes/physics-formalize.md` and `.archon/PROGRESS.md` were
  followed. The `archon` executable is also absent from `PATH`, so the DAG
  query could not be run.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0137.lean` exits with code
  `0` and reports only the expected two `declaration uses sorry` warnings.
- Lean LSP diagnostics report success, the same two warnings, and no failed
  dependencies.
