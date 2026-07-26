import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0923

open Dimension

/-!
# Age of the universe from a Hubble plot

The supplied figure plots a best-fit recession speed against distance.  The
dashed guides read `r = 5.3 * 10^9 ly` and `v = 0.40 c` from that fitted line.
The physical quantities below use Physlib's unit-independent dimensional API;
real numbers occur only as readouts in explicitly selected units or as
dimensionless ratios.

The age estimate uses the elementary Hubble-time model requested by the
problem: Hubble's law holds, the Hubble rate is constant throughout the modeled
history, and the age is the reciprocal expansion timescale.  The numerical age
and its answer-choice rounding occur only in the final theorem.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A physical distance, independent of the unit in which it is read. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical duration, independent of the unit in which it is read. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical speed, carrying length-per-time dimension. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A Hubble expansion rate, carrying inverse-time dimension. -/
abbrev HubbleRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Unit choices used to read a length in the selected length unit. -/
noncomputable def unitsWithLength (unit : LengthUnit) : UnitChoices :=
  { UnitChoices.SI with length := unit }

/-- Unit choices used to read a duration or inverse-time rate. -/
noncomputable def unitsWithTime (unit : TimeUnit) : UnitChoices :=
  { UnitChoices.SI with time := unit }

/-- Unit choices used to read a speed in `lengthUnit / timeUnit`. -/
noncomputable def unitsForSpeed
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : UnitChoices :=
  { UnitChoices.SI with length := lengthUnit, time := timeUnit }

/-- Real readout of a physical distance in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (distance : LengthQuantity) : ℝ :=
  (distance (unitsWithLength unit)).val

/-- Real readout of a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  (duration (unitsWithTime unit)).val

/-- Real readout of a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit)
    (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  (speed (unitsForSpeed lengthUnit timeUnit)).val

/-- Real readout of a Hubble rate in inverse selected time units. -/
def hubbleRateReadout
    (timeUnit : TimeUnit) (rate : HubbleRateQuantity) : ℝ :=
  (rate (unitsWithTime timeUnit)).val

/-- A Julian year (`365.25` days), the year used by the light-year unit. -/
noncomputable def julianYears : TimeUnit :=
  TimeUnit.scale 365.25 TimeUnit.days

/-- Physlib's exact light speed is one light-year per Julian year. -/
lemma speedOfLight_in_lightYearsPerJulianYear :
    speedReadout LengthUnit.lightYears julianYears
      DimSpeed.speedOfLight = 1 := by
  have hLength :
      LengthUnit.meters / LengthUnit.lightYears =
        (1 / 9460730472580800 : NNReal) := by
    apply NNReal.eq
    norm_num [LengthUnit.div_eq_val, LengthUnit.lightYears, LengthUnit.scale,
      LengthUnit.meters]
    rfl
  have hTime :
      TimeUnit.seconds / julianYears =
        (1 / 31557600 : NNReal) := by
    apply NNReal.eq
    norm_num [TimeUnit.div_eq_val, julianYears, TimeUnit.days, TimeUnit.scale,
      TimeUnit.seconds]
    rfl
  simp [speedReadout, unitsForSpeed, DimSpeed.speedOfLight,
    CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale,
    hLength, hTime, NNReal.smul_def, NNReal.rpow_neg_one]
  norm_num

/-! ## Figure labels and physical setup -/

/-- The two axis labels printed on the graph. -/
inductive PlotAxisLabel where
  | distanceRInBillionsOfLightYears
  | recessionSpeedV
  deriving DecidableEq, Repr

/-- Visually distinct features of the supplied graph. -/
inductive PlotFeature where
  | redGalaxyScatter
  | blueBestFitStraightLine
  | horizontalDashedReadoutGuide
  | verticalDashedReadoutGuide
  deriving DecidableEq, Repr

/--
Typed content of the graph.  `bestFitSpeedAt` is the speed represented by the
blue fitted line at a physical distance; it is not a raw scalar graph slope.
-/
structure HubblePlot where
  horizontalAxisLabel : PlotAxisLabel
  verticalAxisLabel : PlotAxisLabel
  featureShown : PlotFeature → Prop
  bestFitSpeedAt : LengthQuantity → SpeedQuantity
  markedDistance : LengthQuantity
  markedBestFitSpeed : SpeedQuantity

/--
The unknown universe age and expansion quantities used by the problem.
`hubbleRateAt` records the rate throughout elapsed cosmic time, allowing the
stated time-independence assumption to be represented explicitly.
-/
structure UniverseExpansionSetup where
  plot : HubblePlot
  presentHubbleRate : HubbleRateQuantity
  hubbleRateAt : TimeQuantity → HubbleRateQuantity
  universeAge : TimeQuantity

/-! ## Figure/data readouts and governing assumptions -/

/--
Primary-image evidence: the axes, scatter, best-fit line, dashed guides, and
their intersection at `5.3 * 10^9 ly` and `0.40 c`.
-/
structure MatchesHubblePlotFigure
    (setup : UniverseExpansionSetup) : Prop where
  horizontalAxis :
    setup.plot.horizontalAxisLabel = .distanceRInBillionsOfLightYears
  verticalAxis : setup.plot.verticalAxisLabel = .recessionSpeedV
  redPoints : setup.plot.featureShown .redGalaxyScatter
  blueLine : setup.plot.featureShown .blueBestFitStraightLine
  horizontalGuide :
    setup.plot.featureShown .horizontalDashedReadoutGuide
  verticalGuide : setup.plot.featureShown .verticalDashedReadoutGuide
  markedPointIsOnBestFitLine :
    setup.plot.markedBestFitSpeed =
      setup.plot.bestFitSpeedAt setup.plot.markedDistance
  markedDistanceReadout :
    lengthReadout LengthUnit.lightYears setup.plot.markedDistance =
      (53 / 10 : ℝ) * 10 ^ 9
  markedSpeedReadout :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.plot.markedBestFitSpeed =
        (2 / 5 : ℝ) *
          speedReadout lengthUnit timeUnit DimSpeed.speedOfLight

/-- Positivity conditions for the distance, fitted speed, rate, and age. -/
structure HasPhysicalExpansionParameters
    (setup : UniverseExpansionSetup) : Prop where
  positiveMarkedDistance :
    0 < lengthReadout LengthUnit.lightYears setup.plot.markedDistance
  positiveMarkedSpeed :
    0 < speedReadout LengthUnit.lightYears julianYears
      setup.plot.markedBestFitSpeed
  positivePresentHubbleRate :
    0 < hubbleRateReadout julianYears setup.presentHubbleRate
  positiveUniverseAge :
    0 < timeReadout julianYears setup.universeAge

/--
Hubble's law `v = H r` for the blue best-fit line, stated in every compatible
choice of length and time units.
-/
structure SatisfiesHubbleLaw
    (setup : UniverseExpansionSetup) : Prop where
  bestFitLineLaw :
    ∀ (distance : LengthQuantity)
      (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
          (setup.plot.bestFitSpeedAt distance) =
        hubbleRateReadout timeUnit setup.presentHubbleRate *
          lengthReadout lengthUnit distance

/--
The problem's assumption that the Hubble rate has had its present value at
every modeled elapsed time from the big bang through the present age.
-/
structure HubbleRateHasAlwaysBeenConstant
    (setup : UniverseExpansionSetup) : Prop where
  constantOnCosmicHistory :
    ∀ elapsed : TimeQuantity,
      0 ≤ timeReadout julianYears elapsed →
      timeReadout julianYears elapsed ≤
          timeReadout julianYears setup.universeAge →
      setup.hubbleRateAt elapsed = setup.presentHubbleRate

/--
The elementary Hubble-time inference used by the question: under the stated
constant-rate model, the universe age is the reciprocal expansion timescale.
This is a governing relation in arbitrary time units, not the requested
numerical age.
-/
structure SatisfiesHubbleTimeAgeModel
    (setup : UniverseExpansionSetup) : Prop where
  ageTimesPresentRate :
    ∀ timeUnit : TimeUnit,
      hubbleRateReadout timeUnit setup.presentHubbleRate *
          timeReadout timeUnit setup.universeAge = 1

/-! ## Answer display and current target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The year count printed beside each answer choice in the source. -/
def displayedAgeInYears : AnswerChoice → ℝ
  | .A => (53 / 10 : ℝ) * 10 ^ 9
  | .B => (13 / 10 : ℝ) * 10 ^ 10
  | .C => 13 * 10 ^ 9
  | .D => (212 / 100 : ℝ) * 10 ^ 9

/-- Dataset metadata; this definition is not used as a premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The age rounds to a given whole number of billions of Julian years. -/
def RoundsToNearestBillionYears
    (age : TimeQuantity) (billionsOfYears : ℕ) : Prop :=
  ((billionsOfYears : ℝ) - 1 / 2) * 10 ^ 9 ≤
      timeReadout julianYears age ∧
    timeReadout julianYears age <
      ((billionsOfYears : ℝ) + 1 / 2) * 10 ^ 9

/-- A displayed answer agrees with the age to the nearest billion years. -/
def MatchesDisplayedBillionYearPrecision
    (age : TimeQuantity) (choice : AnswerChoice) : Prop :=
  |timeReadout julianYears age - displayedAgeInYears choice| ≤
    (1 / 2 : ℝ) * 10 ^ 9

/--
The graph gives an exact elementary-model estimate of `13.25 * 10^9` Julian
years, which rounds to `13 * 10^9` years and hence agrees with recorded choice
C at the displayed billion-year precision.

Blueprint label: `thm:physics:phyx_mini_0923:target`.
-/
theorem universeAge_from_hubblePlot
    (setup : UniverseExpansionSetup)
    (figureData : MatchesHubblePlotFigure setup)
    (physical : HasPhysicalExpansionParameters setup)
    (hubbleLaw : SatisfiesHubbleLaw setup)
    (constantRate : HubbleRateHasAlwaysBeenConstant setup)
    (ageModel : SatisfiesHubbleTimeAgeModel setup) :
    timeReadout julianYears setup.universeAge =
        (53 / 4 : ℝ) * 10 ^ 9 ∧
      RoundsToNearestBillionYears setup.universeAge 13 ∧
      MatchesDisplayedBillionYearPrecision setup.universeAge .C := by
  have hSpeed :
      speedReadout LengthUnit.lightYears julianYears
          setup.plot.markedBestFitSpeed = (2 / 5 : ℝ) := by
    rw [figureData.markedSpeedReadout LengthUnit.lightYears julianYears,
      speedOfLight_in_lightYearsPerJulianYear]
    norm_num
  have hLaw := hubbleLaw.bestFitLineLaw setup.plot.markedDistance
    LengthUnit.lightYears julianYears
  rw [← figureData.markedPointIsOnBestFitLine,
    figureData.markedDistanceReadout, hSpeed] at hLaw
  have hRate :
      hubbleRateReadout julianYears setup.presentHubbleRate =
        (4 : ℝ) / (53 * 10 ^ 9) := by
    norm_num at hLaw ⊢
    linarith
  have hAgeModel := ageModel.ageTimesPresentRate julianYears
  rw [hRate] at hAgeModel
  have hAge :
      timeReadout julianYears setup.universeAge =
        (53 / 4 : ℝ) * 10 ^ 9 := by
    norm_num at hAgeModel ⊢
    linarith
  refine ⟨hAge, ?_, ?_⟩
  · norm_num [RoundsToNearestBillionYears, hAge]
  · norm_num [MatchesDisplayedBillionYearPrecision, displayedAgeInYears, hAge]

end PhyXMiniProblems.ProblemPhyXMini0923
