# Autoformalization result: `problem_phyx_mini_0632.lean`

## Assumption/target split

### Governing laws

- `SatisfiesConstantExpansionAndSphericalArcLaws.constantRadialExpansion` states the symbolic constant-rate law `R(t) = R₀ + v (t - t₀)` for every compatible length/time unit choice. It does not contain the four-year substitution or an answer value.
- `SatisfiesConstantExpansionAndSphericalArcLaws.sphericalMinorArcLength` states the minor surface-arc law `D(t) = R(t) θ`, where `θ` is the dimensionless radian readout. It does not contain the requested numerical distance.
- `HasPhysicalExpandingUniverseParameters` supplies positivity, nonnegative expansion, chronological order, and `0 < θ < π`, selecting the pictured physical minor-arc branch without asserting the answer.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesExpandingUniverseProblemData` records the stated intrinsic spatial dimension `2`, creation time `0 s`, initial radius `500 m`, expansion rate `1 μm/s`, observation four 365-day problem years after creation, and angular separation `60° = π/3 rad`.
- `problemYear` is `365 * TimeUnit.days`; Physlib defines a day as `24 * 60 * 60` seconds. `fourProblemYearsInSeconds` records the scalar conversion used by the exact-readout conclusion.
- The primary bitmap `phyx_data/test_image/632.png` was inspected directly. It shows Nibiru and Xibalba on the circular boundary, the magenta surface arc `D(t)`, two dashed center-to-society radii defining `θ`, and a center-to-boundary radius arrow `R(t)`. It is schematic and has no numerical scale.
- `MatchesSuppliedExpandingUniverseFigure` records only those qualitative labels, roles, and topological facts.
- The source choices are A `656 m`, B `626 m`, C `636 m`, and D `646 m`; the dataset metadata records A. These are presentation metadata, not physical-law assumptions.

### Current target conclusions

- `distanceAfterFourYears_exact_readout` concludes
  `D(t_obs) = (500 + 10⁻⁶ * (4 * 365 * 24 * 60 * 60)) * (π / 3)` in metres.
- `problem_phyx_mini_0632` concludes that the observed physical surface distance rounds to `656 m` and that recorded choice A is the unique displayed choice matching under nearest-metre rounding.

## Goal-faithfulness audit

- `radiusAt` and `interSocietySurfaceDistanceAt` are independent dimensionful observables in `ExpandingSphericalUniverseSetup`. Neither is defined using a governing formula or answer choice; the separate law premise relates them.
- The exact substituted expression, rounding-to-`656 m`, and uniqueness of A appear only in theorem conclusions. No data, figure, physical-parameter, or governing-law field asserts any of them.
- `AnswerChoice.distanceInMeters` and `recordedDatasetAnswer` are literal source metadata. They do not assert that a choice matches the physical distance.
- `RoundsToNearestMeter`, `MatchesAnswerChoice`, and `IsUniqueMatchingAnswerChoice` are parameterized reporting predicates. They do not make the current conclusion true merely by unfolding.
- Length, time, speed, radius, and distance use Physlib dimensionful quantities. Reals occur only at explicitly named unit readouts, for the dimensionless angle representative, and for supplied/displayed scalar data.
- The figure predicate has no calibrated scale and therefore cannot encode the requested numerical distance.
- Independent numerical audit: four problem years are `126144000 s`; radial growth is `126.144 m`; the radius is `626.144 m`; and the minor arc is approximately `655.696463496442 m`. Thus nearest-metre rounding gives `656`, uniquely A among the four displayed values.

## Declarations and blueprint labels

Iteration 003 was an evidence-only retry. The exact gate reason said the revised physical model lacked a genuine post-formalization report, so the final retry protocol required preserving its statement unless an audit found a real defect. No declarations were added, removed, or changed.

The declarations present in the assigned file correspond to the following blueprint labels:

- `LengthQuantity` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-lengthquantity`
- `TimeQuantity` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-timequantity`
- `lengthReadout` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-lengthreadout`
- `timeReadout` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-timereadout`
- `speedReadout` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-speedreadout`
- `lengthInMeters` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-lengthinmeters`
- `timeInSeconds` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-timeinseconds`
- `speedInMetersPerSecond` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-speedinmeterspersecond`
- `problemYear` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-problemyear`
- `fourProblemYearsInSeconds` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-fourproblemyearsinseconds`
- `Society` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-society`
- `FigureQuantityLabel` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-figurequantitylabel`
- `FigureQuantityRole` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-figurequantityrole`
- `ExpandingSphericalUniverseFigure` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-expandingsphericaluniversefigure`
- `ExpandingSphericalUniverseSetup` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-expandingsphericaluniversesetup`
- `MatchesExpandingUniverseProblemData` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-matchesexpandinguniverseproblemdata`
- `MatchesSuppliedExpandingUniverseFigure` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-matchessuppliedexpandinguniversefigure`
- `HasPhysicalExpandingUniverseParameters` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-hasphysicalexpandinguniverseparameters`
- `SatisfiesConstantExpansionAndSphericalArcLaws` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-satisfiesconstantexpansionandsphericalarclaws`
- `AnswerChoice` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-answerchoice`
- `AnswerChoice.distanceInMeters` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-answerchoice-distanceinmeters`
- `recordedDatasetAnswer` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-recordeddatasetanswer`
- `RoundsToNearestMeter` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-roundstonearestmeter`
- `MatchesAnswerChoice` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-matchesanswerchoice`
- `IsUniqueMatchingAnswerChoice` — `def:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-isuniquematchinganswerchoice`
- `distanceAfterFourYears_exact_readout` — `thm:physics:phyx-mini-0632:phyxminiproblems-problemphyxmini0632-distanceafterfouryears-exact-readout`
- `problem_phyx_mini_0632` — `thm:physics:phyx_mini_0632:target`

The blueprint was not edited with `\leanok` because the explicit write permissions allow changes only to the assigned Lean file and this task-result file.

## LeanExplore queries and candidates actually used

Every query passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language quantity query: `dimensionful physical quantity with units length time speed`.
- Likely-name quantity query: `Dimensionful WithDim LengthUnit TimeUnit DimSpeed`.
- Angle queries: `Real.Angle radians toReal`.
- Geometry query: `spherical minor arc length radius times central angle`.
- Unit queries: `LengthUnit meters micrometers`, `TimeUnit seconds days scale`, and `WithDim L𝓭 T𝓭 UnitChoices.SI`.
- Exact-name checks: `WithDim`, `LengthUnit.meters`, and `TimeUnit.scale`.
- Expansion-law query: `constant radial expansion initial radius plus speed times elapsed time`.

Source code, module, and docstring were fetched for the candidates retained in the model:

- `Dimensionful` (id `394284`), module `Physlib.Units.Basic`;
- `WithDim` (id `394425`), module `Physlib.Units.WithDim.Basic`;
- `DimSpeed` (id `394481`), module `Physlib.Units.WithDim.Speed`;
- `UnitChoices.SI` (id `394270`), module `Physlib.Units.Basic`;
- `LengthUnit.micrometers` (id `393158`), module `Physlib.SpaceAndTime.Space.LengthUnit`;
- `TimeUnit.scale` (id `393624`), `TimeUnit.seconds` (id `393630`), and `TimeUnit.days` (id `393640`), module `Physlib.SpaceAndTime.Time.TimeUnit`;
- `Real.Angle.toReal` (id `146503`), module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`.

The geometry search surfaced `Circle.angleDiff`, `Cosmology.SpatialGeometry.Spherical`, chord/radius angle results, and metric-sphere declarations. None of the summaries provided a unit-independent, arbitrary-radius minor surface-distance law compatible with this setup. The expansion search surfaced general constant-speed and FLRW declarations, but no compatible dimensionful law for the hypothetical radius observable. Those near matches were not used.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimensionful`, `WithDim`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.meters`, `LengthUnit.micrometers`, `TimeUnit`, `TimeUnit.scale`, `TimeUnit.seconds`, `TimeUnit.days`, and `DimSpeed`.
- Mathlib: `NNReal`/`ℝ≥0`, `Real.Angle`, `Real.Angle.toReal`, `Real.pi`, real absolute value, finite inductive derivations, ordered-field operations, and exponentiation.
- Retrieved source confirms that `Dimensionful` is a unit-choice-indexed quantity satisfying a dimension-scaling predicate; `WithDim` tags an underlying value with a physical dimension; `DimSpeed` has dimension `L𝓭 * T𝓭⁻¹`; `LengthUnit.micrometers` is `10⁻⁶` metres; `TimeUnit.days` is `86400` seconds; and `Real.Angle.toReal` selects a representative in `(-π, π]`.
- The exact Lean file compiled, independently confirming all used names and signatures in the installed Mathlib/Physlib environment.

## Local abstractions introduced and preserved

- `LengthQuantity` and `TimeQuantity` specialize Physlib's `Dimensionful (WithDim ... NNReal)` infrastructure at the length and time dimensions. They are not scalar aliases; real values are exposed only through named unit readouts.
- `ExpandingSphericalUniverseSetup` is the smallest local setup retaining independent radius and surface-distance observables, dimensionful initial radius/rate/times, angular separation, intrinsic dimension, and primary-figure evidence.
- `Society`, `FigureQuantityLabel`, `FigureQuantityRole`, and `ExpandingSphericalUniverseFigure` preserve named objects and qualitative geometry from the bitmap without inventing a pixel scale.
- `SatisfiesConstantExpansionAndSphericalArcLaws` is a local governing-law interface because the searches did not find compatible dimensionful arbitrary-radius arc or expanding-radius laws.
- The answer-choice and rounding declarations preserve the multiple-choice presentation separately from physical data and laws.

## Grounding gaps and redraft requests

- No matching Mathlib/Physlib declaration was found for dimensionful spherical surface arc length `D = R θ` at arbitrary physical radius or for constant radial expansion of this hypothetical universe. The local law structure preserves these physical roles without assuming the current answer.
- The closest library hits concern a unit-circle angular difference, abstract metric spheres, chords/inscribed angles, generic constant speed, or FLRW curvature/evolution; none directly models this elementary two-dimensional expanding spherical surface.
- The chapter has `% archon:physics`, but its proof text is only the generic autoformalization instruction rather than the promised informal derivation. A plan-agent redraft should state `R(t) = R₀ + v(t-t₀)`, `D(t) = R(t)θ`, the 365-day convention, and the `655.696... m` rounding calculation.
- The auxiliary caption describes a right triangle and a hypotenuse, while the primary bitmap shows two center-to-society radii and no society-to-society chord. The Lean model follows the primary bitmap; the caption should be corrected.
- The requested project-local `.archon/AGENTS.md` is absent. The injected prover role and `.archon/PROGRESS.md` supplied the applicable workflow.
- The assigned Lean file contains no `/- USER: ... -/` hints.
- Although the prompt says `archon` is on `PATH`, `command -v archon` found nothing and both optional DAG queries failed with `command not found`. The source report independently establishes that there are no previous parts.

## Review-gate resolution

- Exact retry reason: no genuine post-formalization task result existed for target 0632. This report now records the actual searches and fetched candidates from iteration 003, grounded declarations, local abstractions, grounding gaps, source/figure/law/answer split, and goal-faithfulness audit.
- No semantic defect was found, so the revised Lean statement was preserved exactly as the final retry protocol requires for evidence-only failures.

## Verification

Prover iteration 018 closed both assigned proof obligations:

- `distanceAfterFourYears_exact_readout` uses the `Dimensionful`
  change-of-units law to convert `1 μm/s` to `10⁻⁶ m/s` and four
  `problemYear` units to `4 * 365 * 24 * 60 * 60` seconds. Substitution into
  the radial-expansion and spherical-arc hypotheses gives the exact target.
- `problem_phyx_mini_0632` uses `Real.pi_gt_d4` and `Real.pi_lt_d4` to prove
  that the exact distance lies strictly within half a metre of `656`.
  Disjoint half-metre intervals then rule out choices B, C, and D.

Checks:

- `archon-lean-lsp` diagnostics report no errors and no `sorry` warnings.
  The only messages are harmless unused-hypothesis lints for `hPhysical` in
  the exact-readout helper and `hFigure` in the final theorem; their frozen
  signatures were preserved.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0632.lean` exits `0`.
- Source scanning finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- Axiom checks for both the helper and final theorem report only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Redraft needed

No Lean statement redraft is needed. The blueprint theorem environments were
not edited with `\leanok` because this prover task's explicit write
permissions allow changes only to the assigned Lean file and this result
file; an authorized blueprint synchronization step should mark both proved
theorems.
