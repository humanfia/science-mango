# Autoformalization result: `problem_phyx_mini_0923.lean`

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was used.  The assigned Lean file did not exist at the start of the task and
therefore contained no file-specific `/- USER: ... -/` comments.

## Assumption/target split

### Governing laws

- `SatisfiesHubbleLaw.bestFitLineLaw` states Hubble's law `v = H r` for the
  graph's blue best-fit line in every selected length/time unit system.
- `HubbleRateHasAlwaysBeenConstant.constantOnCosmicHistory` states that the
  rate at every modeled elapsed time from the big bang through the present age
  equals the present Hubble rate.
- `SatisfiesHubbleTimeAgeModel.ageTimesPresentRate` states the elementary
  age-estimation rule used in the problem, `H * age = 1`, in every time unit.
  This is the general Hubble-time governing relation, not a numerical answer.
- `HasPhysicalExpansionParameters` records positivity of the marked distance,
  marked speed, present Hubble rate, and universe age.

### Previous-part results

- None.  The source report has an empty `previous_parts` array.
- `speedOfLight_in_lightYearsPerJulianYear` is a local unit-conversion helper,
  not a previous question result.  It states that Physlib's exact speed of
  light reads as one light-year per locally defined Julian year.

### Figure/data readouts

- `MatchesHubblePlotFigure` records both printed axes, the red scatter, blue
  best-fit straight line, horizontal/vertical dashed guides, and that the
  marked point lies on the best-fit line.
- Its distance readout is exactly `(53 / 10) * 10^9` light-years.
- Its speed readout is exactly `(2 / 5)` times Physlib's speed of light, in
  every compatible length/time unit system.
- These values were confirmed from the primary image `phyx_data/test_image/923.png`.

### Current target conclusions

`universeAge_from_hubblePlot` concludes all of the following:

- the universe-age readout is exactly `(53 / 4) * 10^9` Julian years in the
  elementary model (`13.25 * 10^9` years);
- it rounds to `13` billion years;
- it agrees with displayed answer C to the nearest-billion-year precision.

## Goal-faithfulness audit

No hypothesis or premise field states `(53 / 4) * 10^9`, the rounded value
`13 * 10^9`, or agreement with choice C.  `UniverseExpansionSetup.universeAge`
is an unknown dimensionful duration.  The figure premises constrain only the
independently displayed distance and speed.  The governing-law premises state
unit-generic physical laws and contain no numerical age.

`recordedAnswerChoice := .C` is dataset metadata and is not a theorem premise.
`displayedAgeInYears` merely transcribes the printed options.  Neither unfolds
to the physical universe age.  The substantive numerical and rounding claims
remain exclusively in the conclusion of `universeAge_from_hubblePlot`, whose
body is `by sorry` as required at the autoformalization stage.

The source renders B as `1.3 * 10^10` years and C as `13 * 10^9` years, which
are mathematically equal.  Consequently the theorem honestly establishes
that C agrees with the inferred age but does not make a false uniqueness claim.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0923:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0923.universeAge_from_hubblePlot`.
- Dimensionful types: `LengthQuantity`, `TimeQuantity`, `SpeedQuantity`, and
  `HubbleRateQuantity`.
- Unit/readout infrastructure: `unitsWithLength`, `unitsWithTime`,
  `unitsForSpeed`, `lengthReadout`, `timeReadout`, `speedReadout`,
  `hubbleRateReadout`, and `julianYears`.
- Grounded helper lemma: `speedOfLight_in_lightYearsPerJulianYear`.
- Figure/model declarations: `PlotAxisLabel`, `PlotFeature`, `HubblePlot`,
  `UniverseExpansionSetup`, `MatchesHubblePlotFigure`,
  `HasPhysicalExpansionParameters`, `SatisfiesHubbleLaw`,
  `HubbleRateHasAlwaysBeenConstant`, and `SatisfiesHubbleTimeAgeModel`.
- Answer declarations: `AnswerChoice`, `displayedAgeInYears`,
  `recordedAnswerChoice`, `RoundsToNearestBillionYears`, and
  `MatchesDisplayedBillionYearPrecision`.

The blueprint theorem environment was not edited or marked `\leanok` because
the task's explicit write permissions forbid editing blueprint chapters.  A
plan/orchestration agent with blueprint write permission should add `\leanok`.

## LeanExplore queries and candidates

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query: `hubble law recession velocity distance Hubble
  constant age universe`.
  - Inspected `Cosmology.FLRW.FriedmannEquation.hubbleConstant` from
    `Physlib.Cosmology.FLRW.Basic`.
  - It is defined as `(d_t a) / a` for an FLRW scale factor and returns `ℝ` at
    a time.  It does not supply the dimensionful graph law or the elementary
    Hubble-time interface needed here, so it was not used.
- Likely-name query: `HubbleConstant HubbleLaw`.
  - It again found the FLRW declaration but no reusable Hubble-law predicate.
- Natural-language/API query: `physical dimensions length time velocity speed
  units light year`.
  - Used `DimSpeed.speedOfLight`, `LengthUnit.lightYears`, `Dimension`,
    `Dimension.L𝓭`, and `Dimension.T𝓭`.
  - Inspected `UnitExamples.SpeedEq`; it documents the dimensioned relation
    `speed = distance / time` but is an example over individual `WithDim`
    values, not a unit-independent Hubble-law abstraction, so it was not used.

Sources/modules/docstrings were fetched only for the candidates assessed for
use: the FLRW Hubble constant, speed of light, light-year unit, foundational
dimension and its length/time generators, and `UnitExamples.SpeedEq`.

## Physlib/Mathlib names grounded

- `Dimensionful` and `WithDim` for unit-independent dimensional quantities.
- `Dimension.L𝓭` and `Dimension.T𝓭`, including products and inverses for
  speed (`L T^-1`) and Hubble rate (`T^-1`).
- `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, and `TimeUnit` for explicit
  scalar readouts.
- `LengthUnit.lightYears`, `TimeUnit.days`, and `TimeUnit.scale` for the graph
  distance and Julian-year convention.
- `DimSpeed.speedOfLight` for the exact physical light speed.
- Mathlib real arithmetic notation, powers, absolute value, inequalities, and
  `NNReal`-free real-valued readouts are available through the Physlib import.

## Local abstractions introduced

- `HubbleRateQuantity` is a Physlib `Dimensionful (WithDim T𝓭⁻¹ ℝ)`, rather
  than a scalar alias, so the inverse-time role of the Hubble rate is retained.
- `HubblePlot` distinguishes physical distance/speed quantities from their
  graph labels and stores the fitted speed as a function of physical distance.
- The three governing predicates separate Hubble's law, time constancy, and
  the Hubble-time age rule.  This keeps the model explicit and prevents a
  numerical answer from being hidden in a setup definition.
- `julianYears` is local because the pinned Physlib version provides seconds,
  days, and weeks but no named year unit.  Defining it as `365.25` days matches
  the standard light-year calibration used by `LengthUnit.lightYears`.
- The rounding/precision predicates make the approximate displayed answer
  separate from the exact model output.

## Grounding gaps and redraft requests

- LeanExplore found no ready-made graph-level Hubble-law predicate or typed
  Hubble-time age theorem.  The FLRW `hubbleConstant` is a near miss with a
  different model and scalar signature, so faithful local predicates were
  introduced.
- Physlib has no named year `TimeUnit` in this pinned revision; `julianYears`
  was constructed from `TimeUnit.days`.
- The answer-choice text has missing trailing unit markup and duplicates the
  numerical values of B and C.  If unique multiple-choice selection is
  intended, the blueprint/source should be redrafted with the missing units or
  corrected option text.  The present formalization avoids claiming uniqueness.
- The requested `.archon/AGENTS.md` file is absent in this checkout.  The full
  available `.archon/prover-modes/physics-formalize.md`, the task prompt, and
  the relevant `PROGRESS.md` entry supplied the operative role instructions.
- The prompt says `archon` is on `PATH`, but the executable was unavailable in
  this runtime, so the optional dependency-graph query could not be performed.

## Validation

- Lean language-server diagnostics reported exactly two expected `sorry`
  warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0923.lean` exited with code
  0 and emitted only those same two expected warnings.
