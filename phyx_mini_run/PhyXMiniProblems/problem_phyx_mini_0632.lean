import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0632

open Dimension

/-!
# Surface distance in an expanding spherical universe

Nibiru and Xibalba are fixed societies on a two-dimensional spherical
universe. Their central angular separation is `60 degrees`. The physical
radius, time, expansion speed, and surface distance are represented by
unit-independent Physlib quantities. Real numbers occur only at explicitly
named unit-readout boundaries, for the dimensionless angle in radians, and for
the displayed answer values.

The requested distance is an independent observable in the setup. It is
related to the radius by the separate spherical arc-length law below; it is not
defined to be the recorded `656 m` answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout
    (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical time in a selected Physlib time unit. -/
def timeReadout
    (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  ((time {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in selected compatible length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout of a physical time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-!
The multiple-choice calculation uses the elementary convention that one
problem year has `365` twenty-four-hour days. This is a unit convention, not
an assumption about the requested distance.
-/
def problemYear : TimeUnit :=
  TimeUnit.scale 365 TimeUnit.days

/-- The scalar number of seconds in the four problem years. -/
def fourProblemYearsInSeconds : ℝ :=
  4 * 365 * 24 * 60 * 60

/-! ## Society roles and primary-figure vocabulary -/

/-- The two societies named on the boundary of the spherical universe. -/
inductive Society where
  | nibiru
  | xibalba
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels visible in the supplied figure. -/
inductive FigureQuantityLabel where
  | distanceDOfT
  | radiusROfT
  | angleTheta
  deriving DecidableEq, Fintype, Repr

/-- Physical role denoted by each symbolic label in the figure. -/
inductive FigureQuantityRole where
  | interSocietySurfaceDistanceAtTime
  | universeRadiusAtTime
  | centralAngularSeparation
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from image `632.png`. The raster is
schematic: it gives topology, labels, and the central-angle construction but
no numerical spatial scale.
-/
structure ExpandingSphericalUniverseFigure where
  societyPointShown : Society → Bool
  societyLabelText : Society → String
  quantityLabelShown : FigureQuantityLabel → Bool
  quantityLabelText : FigureQuantityLabel → String
  quantityRole : FigureQuantityLabel → FigureQuantityRole
  circularBoundaryShown : Bool
  twoDashedCenterToSocietyRadiiShown : Bool
  radiusArrowFromCenterToBoundaryShown : Bool
  magentaDistanceArcConnectsSocieties : Bool
  thetaMarkedBetweenSocietyRadii : Bool
  hasQuantitativeScale : Bool

/-! ## Independent physical setup -/

/-!
The time-dependent radius `R(t)` and the Nibiru--Xibalba surface distance
`D(t)` are independent observables. The governing laws below relate them.
-/
structure ExpandingSphericalUniverseSetup where
  intrinsicSpatialDimension : ℕ
  creationTime : TimeQuantity
  observationTime : TimeQuantity
  initialRadius : LengthQuantity
  radiusAt : TimeQuantity → LengthQuantity
  expansionRate : DimSpeed
  angularSeparation : Real.Angle
  interSocietySurfaceDistanceAt : TimeQuantity → LengthQuantity
  figure : ExpandingSphericalUniverseFigure

/-! ## Scenario data, figure evidence, and governing laws -/

/-!
Numerical readouts stated in the problem: a `500 m` initial radius, constant
rate magnitude `1 micrometre/second`, a four-year observation time, and a
`60 degree = pi/3 radian` central separation. No distance answer occurs here.
-/
structure MatchesExpandingUniverseProblemData
    (setup : ExpandingSphericalUniverseSetup) : Prop where
  surfaceIsTwoDimensional : setup.intrinsicSpatialDimension = 2
  creationTimeIsZero : timeInSeconds setup.creationTime = 0
  initialRadiusInMeters : lengthInMeters setup.initialRadius = 500
  expansionRateInMicrometersPerSecond :
    speedReadout LengthUnit.micrometers TimeUnit.seconds
      setup.expansionRate = 1
  observationIsFourProblemYearsAfterCreation :
    timeReadout problemYear setup.observationTime -
        timeReadout problemYear setup.creationTime = 4
  angularSeparationIsSixtyDegrees :
    setup.angularSeparation.toReal = Real.pi / 3

/-- Direct qualitative evidence from the supplied raster image. -/
structure MatchesSuppliedExpandingUniverseFigure
    (setup : ExpandingSphericalUniverseSetup) : Prop where
  nibiruText : setup.figure.societyLabelText .nibiru = "Nibiru"
  xibalbaText : setup.figure.societyLabelText .xibalba = "Xibalba"
  everySocietyPointIsShown :
    ∀ society : Society, setup.figure.societyPointShown society = true
  everyQuantityLabelIsShown :
    ∀ label : FigureQuantityLabel,
      setup.figure.quantityLabelShown label = true
  distanceLabelText :
    setup.figure.quantityLabelText .distanceDOfT = "D(t)"
  radiusLabelText :
    setup.figure.quantityLabelText .radiusROfT = "R(t)"
  angleLabelText :
    setup.figure.quantityLabelText .angleTheta = "theta"
  distanceLabelRole :
    setup.figure.quantityRole .distanceDOfT =
      .interSocietySurfaceDistanceAtTime
  radiusLabelRole :
    setup.figure.quantityRole .radiusROfT = .universeRadiusAtTime
  angleLabelRole :
    setup.figure.quantityRole .angleTheta = .centralAngularSeparation
  circularBoundary : setup.figure.circularBoundaryShown = true
  twoSocietyRadii :
    setup.figure.twoDashedCenterToSocietyRadiiShown = true
  radiusArrow :
    setup.figure.radiusArrowFromCenterToBoundaryShown = true
  distanceIsSurfaceArc :
    setup.figure.magentaDistanceArcConnectsSocieties = true
  thetaIsCentralAngle :
    setup.figure.thetaMarkedBetweenSocietyRadii = true
  imageIsSchematic : setup.figure.hasQuantitativeScale = false

/-- Positivity and minor-arc conditions selecting the physical branch shown. -/
structure HasPhysicalExpandingUniverseParameters
    (setup : ExpandingSphericalUniverseSetup) : Prop where
  initialRadiusPositive : 0 < lengthInMeters setup.initialRadius
  everyRadiusPositive :
    ∀ time : TimeQuantity, 0 < lengthInMeters (setup.radiusAt time)
  expansionRateNonnegative :
    0 ≤ speedInMetersPerSecond setup.expansionRate
  observationAfterCreation :
    timeInSeconds setup.creationTime < timeInSeconds setup.observationTime
  angularSeparationPositive : 0 < setup.angularSeparation.toReal
  angularSeparationIsMinor : setup.angularSeparation.toReal < Real.pi

/-!
The two governing laws are kept separate from the problem readouts:

* constant radial expansion gives `R(t) = R₀ + v (t - t₀)` in every
  compatible choice of length and time units;
* on a sphere, the minor surface arc between sites at fixed central angular
  separation has length `D(t) = R(t) theta`, with `theta` in radians.

Neither law contains the requested numerical distance or an answer choice.
-/
structure SatisfiesConstantExpansionAndSphericalArcLaws
    (setup : ExpandingSphericalUniverseSetup) : Prop where
  constantRadialExpansion :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
      (time : TimeQuantity),
      lengthReadout lengthUnit (setup.radiusAt time) =
        lengthReadout lengthUnit setup.initialRadius +
          speedReadout lengthUnit timeUnit setup.expansionRate *
            (timeReadout timeUnit time -
              timeReadout timeUnit setup.creationTime)
  sphericalMinorArcLength :
    ∀ (lengthUnit : LengthUnit) (time : TimeQuantity),
      lengthReadout lengthUnit
          (setup.interSocietySurfaceDistanceAt time) =
        lengthReadout lengthUnit (setup.radiusAt time) *
          setup.angularSeparation.toReal

/-! ## Displayed choices and current target -/

/-- Labels of the four distance choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical metre readout printed beside each answer label. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 656
  | .B => 626
  | .C => 636
  | .D => 646

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- A physical distance rounds to a displayed whole-metre value. -/
def RoundsToNearestMeter
    (distance : LengthQuantity) (wholeMeters : ℝ) : Prop :=
  |lengthInMeters distance - wholeMeters| < (1 / 2 : ℝ)

/-- The observed surface distance rounds to the number printed for a choice. -/
def MatchesAnswerChoice
    (setup : ExpandingSphericalUniverseSetup)
    (choice : AnswerChoice) : Prop :=
  RoundsToNearestMeter
    (setup.interSocietySurfaceDistanceAt setup.observationTime)
    choice.distanceInMeters

/-- A choice is the unique displayed value matching the rounded distance. -/
def IsUniqueMatchingAnswerChoice
    (setup : ExpandingSphericalUniverseSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Substitution of the calibrated data into the two governing laws gives the
exact metre readout before rounding.
-/
theorem distanceAfterFourYears_exact_readout
    (setup : ExpandingSphericalUniverseSetup)
    (hData : MatchesExpandingUniverseProblemData setup)
    (hPhysical : HasPhysicalExpandingUniverseParameters setup)
    (hLaws : SatisfiesConstantExpansionAndSphericalArcLaws setup) :
    lengthInMeters
        (setup.interSocietySurfaceDistanceAt setup.observationTime) =
      (500 + (1 / (10 : ℝ) ^ 6) * fourProblemYearsInSeconds) *
        (Real.pi / 3) := by
  let uMicro : UnitChoices :=
    { UnitChoices.SI with
      length := LengthUnit.micrometers, time := TimeUnit.seconds }
  have hSpeedUnits :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.expansionRate =
        (UnitChoices.dimScale uMicro UnitChoices.SI
          (L𝓭 * T𝓭⁻¹) : ℝ) *
            speedReadout LengthUnit.micrometers TimeUnit.seconds
              setup.expansionRate := by
    have h := setup.expansionRate.2 uMicro UnitChoices.SI
    have hv := congrArg (fun x => (x.val : ℝ)) h
    simpa [speedReadout, uMicro, UnitChoices.SI] using hv
  have hMicroScale :
      (UnitChoices.dimScale uMicro UnitChoices.SI
          (L𝓭 * T𝓭⁻¹) : ℝ) =
        1 / (10 : ℝ) ^ 6 := by
    norm_num [uMicro, UnitChoices.SI, UnitChoices.dimScale,
      LengthUnit.micrometers, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val, TimeUnit.seconds, TimeUnit.div_eq_val,
      MassUnit.div_eq_val, ChargeUnit.div_eq_val,
      TemperatureUnit.div_eq_val, NNReal.eq_iff]
    rfl
  have hSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.expansionRate =
        1 / (10 : ℝ) ^ 6 := by
    rw [hSpeedUnits, hMicroScale,
      hData.expansionRateInMicrometersPerSecond]
    ring
  let uYear : UnitChoices :=
    { UnitChoices.SI with time := problemYear }
  have hTimeUnits (time : TimeQuantity) :
      timeReadout TimeUnit.seconds time =
        (UnitChoices.dimScale uYear UnitChoices.SI T𝓭 : ℝ) *
          timeReadout problemYear time := by
    have h := time.2 uYear UnitChoices.SI
    have hv := congrArg (fun x => (x.val : ℝ)) h
    simpa [timeReadout, uYear, UnitChoices.SI] using hv
  have hYearScale :
      (UnitChoices.dimScale uYear UnitChoices.SI T𝓭 : ℝ) =
        365 * 24 * 60 * 60 := by
    norm_num [uYear, problemYear, UnitChoices.SI,
      UnitChoices.dimScale, TimeUnit.days, TimeUnit.seconds,
      TimeUnit.scale, LengthUnit.div_eq_val, TimeUnit.div_eq_val,
      MassUnit.div_eq_val, ChargeUnit.div_eq_val,
      TemperatureUnit.div_eq_val, NNReal.eq_iff]
    rfl
  have hElapsed :
      timeInSeconds setup.observationTime -
          timeInSeconds setup.creationTime =
        fourProblemYearsInSeconds := by
    rw [show timeInSeconds setup.observationTime =
      timeReadout TimeUnit.seconds setup.observationTime by rfl]
    rw [show timeInSeconds setup.creationTime =
      timeReadout TimeUnit.seconds setup.creationTime by rfl]
    rw [hTimeUnits, hTimeUnits, hYearScale, ← mul_sub]
    rw [hData.observationIsFourProblemYearsAfterCreation]
    norm_num [fourProblemYearsInSeconds]
  have hInitial :
      lengthReadout LengthUnit.meters setup.initialRadius = 500 :=
    hData.initialRadiusInMeters
  calc
    lengthInMeters
        (setup.interSocietySurfaceDistanceAt setup.observationTime) =
      lengthReadout LengthUnit.meters
          (setup.radiusAt setup.observationTime) *
        setup.angularSeparation.toReal :=
      hLaws.sphericalMinorArcLength LengthUnit.meters
        setup.observationTime
    _ = (lengthReadout LengthUnit.meters setup.initialRadius +
          speedReadout LengthUnit.meters TimeUnit.seconds
              setup.expansionRate *
            (timeReadout TimeUnit.seconds setup.observationTime -
              timeReadout TimeUnit.seconds setup.creationTime)) *
          setup.angularSeparation.toReal := by
      rw [hLaws.constantRadialExpansion LengthUnit.meters
        TimeUnit.seconds setup.observationTime]
    _ = (500 + (1 / (10 : ℝ) ^ 6) *
          fourProblemYearsInSeconds) * (Real.pi / 3) := by
      rw [hInitial, hSpeed]
      change (500 + 1 / 10 ^ 6 *
        (timeInSeconds setup.observationTime -
          timeInSeconds setup.creationTime)) *
            setup.angularSeparation.toReal = _
      rw [hElapsed, hData.angularSeparationIsSixtyDegrees]

/-!
After four `365`-day years the radius is approximately `626.144 m`; the
`60 degree` surface arc is approximately `655.70 m`, which rounds to `656 m`
and uniquely selects answer A.

This formalizes `thm:physics:phyx_mini_0632:target`.
-/
theorem problem_phyx_mini_0632
    (setup : ExpandingSphericalUniverseSetup)
    (hData : MatchesExpandingUniverseProblemData setup)
    (hFigure : MatchesSuppliedExpandingUniverseFigure setup)
    (hPhysical : HasPhysicalExpandingUniverseParameters setup)
    (hLaws : SatisfiesConstantExpansionAndSphericalArcLaws setup) :
    RoundsToNearestMeter
        (setup.interSocietySurfaceDistanceAt setup.observationTime) 656 ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hExact :=
    distanceAfterFourYears_exact_readout setup hData hPhysical hLaws
  have hRound :
      RoundsToNearestMeter
        (setup.interSocietySurfaceDistanceAt setup.observationTime) 656 := by
    rw [RoundsToNearestMeter, hExact]
    norm_num [fourProblemYearsInSeconds]
    rw [abs_lt]
    constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4]
  refine ⟨hRound, ?_⟩
  change MatchesAnswerChoice setup .A ∧
    ∀ other, MatchesAnswerChoice setup other → other = .A
  constructor
  · simpa [MatchesAnswerChoice, AnswerChoice.distanceInMeters] using hRound
  · intro other hOther
    have hNearA := hRound
    unfold RoundsToNearestMeter at hNearA
    rw [abs_lt] at hNearA
    cases other with
    | A => rfl
    | B =>
        exfalso
        unfold MatchesAnswerChoice RoundsToNearestMeter at hOther
        simp only [AnswerChoice.distanceInMeters] at hOther
        rw [abs_lt] at hOther
        linarith
    | C =>
        exfalso
        unfold MatchesAnswerChoice RoundsToNearestMeter at hOther
        simp only [AnswerChoice.distanceInMeters] at hOther
        rw [abs_lt] at hOther
        linarith
    | D =>
        exfalso
        unfold MatchesAnswerChoice RoundsToNearestMeter at hOther
        simp only [AnswerChoice.distanceInMeters] at hOther
        rw [abs_lt] at hOther
        linarith

end PhyXMiniProblems.ProblemPhyXMini0632
