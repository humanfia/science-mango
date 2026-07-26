import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0731

open Dimension

/-!
# Collision time for horizontal flight above rising ground

At `t = 0` an airplane flying horizontally reaches the foot of an upward
planar slope.  Its speed is `1300 km/h`, its initial vertical clearance is
`h = 35 m`, and the slope angle is `theta = 4.3 degrees`.  The airplane keeps
the same horizontal heading, so the rising ground eventually meets its flight
path.

Lengths, elapsed times, and speeds are unit-independent Physlib quantities.
Real numbers below occur only as named-unit readouts, dimensionless
trigonometric values, and displayed answer values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev FlightLength : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical elapsed time. -/
abbrev FlightDuration : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : FlightLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical elapsed time in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : FlightDuration) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout used by the geometric laws. -/
def lengthInMeters (length : FlightLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout used by the requested time and answer choices. -/
def durationInSeconds (duration : FlightDuration) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Metres-per-second readout used by the constant-speed law. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Convert an angle stated in degrees to Mathlib's angle type. -/
def angleOfDegrees (degrees : ℝ) : Real.Angle :=
  (degrees * Real.pi / 180 : ℝ)

/-! ## Scenario roles and primary-figure evidence -/

/-- The idealized ground profile described by the problem. -/
inductive GroundProfileKind where
  | initiallyLevelThenUpwardPlanarSlope
  deriving DecidableEq, Repr

/-- The airplane heading retained after it reaches the slope. -/
inductive FlightHeading where
  | horizontalUnchanged
  deriving DecidableEq, Repr

/-- Direction of motion relative to the rising portion of the ground. -/
inductive FlightDirection where
  | intoRisingSlope
  deriving DecidableEq, Repr

/-- Named visual elements present in the supplied diagram. -/
inductive FigureFeature where
  | airplane
  | initiallyLevelGround
  | upwardSlopingGround
  | horizontalDashedFlightLine
  | verticalClearanceMarker
  deriving DecidableEq, Fintype, Repr

/-!
The two mathematical labels and qualitative features transcribed from image
731.  The quantity labeled `h` and the angle labeled `theta` remain physical
data; the figure does not contain an impact-time label.
-/
structure RisingGroundFigure where
  featureShown : FigureFeature → Bool
  clearanceLabelH : FlightLength
  slopeAngleLabelTheta : Real.Angle

/-!
Independent physical quantities and trajectories in the model.

`horizontalDistanceAt` measures distance traveled from the foot of the slope.
Both elevation functions use the same vertical datum at that foot.  The
trajectory fields are independent observables related by the governing laws
below; no impact duration is stored in this structure.
-/
structure RisingGroundFlightSetup where
  groundProfile : GroundProfileKind
  heading : FlightHeading
  direction : FlightDirection
  flightSpeed : DimSpeed
  initialClearance : FlightLength
  slopeAngle : Real.Angle
  slopeEntryTime : FlightDuration
  horizontalDistanceAt : FlightDuration → FlightLength
  aircraftElevationAt : FlightDuration → FlightLength
  groundElevationAt : FlightLength → FlightLength
  figure : RisingGroundFigure

/-! ## Statement, figure, and governing-law assumptions -/

/-!
Numerical and qualitative data read from the prose and primary figure.  In
particular, this predicate says nothing about an impact time or an answer
choice.
-/
structure MatchesProblemAndFigure
    (setup : RisingGroundFlightSetup) : Prop where
  groundInitiallyLevelThenRises :
    setup.groundProfile = .initiallyLevelThenUpwardPlanarSlope
  headingRemainsHorizontal : setup.heading = .horizontalUnchanged
  airplaneMovesIntoRisingSlope : setup.direction = .intoRisingSlope
  speedKilometersPerHour :
    speedReadout LengthUnit.kilometers TimeUnit.hours setup.flightSpeed = 1300
  initialClearanceMeters : lengthInMeters setup.initialClearance = 35
  slopeAngleDegrees : setup.slopeAngle = angleOfDegrees (43 / 10)
  slopeEntryIsTimeZero : durationInSeconds setup.slopeEntryTime = 0
  figureShowsAllFeatures : ∀ feature, setup.figure.featureShown feature = true
  figureClearanceLabelIsH :
    setup.figure.clearanceLabelH = setup.initialClearance
  figureSlopeAngleLabelIsTheta :
    setup.figure.slopeAngleLabelTheta = setup.slopeAngle

/-!
Positivity and the acute physical branch of the slope angle.  These conditions
exclude a stationary plane, zero clearance, and non-rising trigonometric
branches without assigning the requested collision time.
-/
structure HasPhysicalFlightParameters
    (setup : RisingGroundFlightSetup) : Prop where
  flightSpeedPositive : 0 < speedInMetersPerSecond setup.flightSpeed
  initialClearancePositive : 0 < lengthInMeters setup.initialClearance
  slopeAngleAcute : setup.slopeAngle.toReal ∈ Set.Ioo 0 (Real.pi / 2)

/-!
Constant horizontal flight and planar-slope geometry, stated in coherent SI
readouts:

* horizontal distance traveled is `speed * elapsed time`;
* unchanged horizontal heading keeps aircraft elevation equal to `h`;
* the upward ground elevation after distance `x` is `x * tan(theta)`.

These are general kinematic and geometric laws.  They contain no collision
time, numerical answer, or answer-choice label.
-/
structure SatisfiesHorizontalFlightAndSlopeLaws
    (setup : RisingGroundFlightSetup) : Prop where
  horizontalMotion : ∀ elapsed,
    lengthInMeters (setup.horizontalDistanceAt elapsed) =
      speedInMetersPerSecond setup.flightSpeed * durationInSeconds elapsed
  aircraftKeepsConstantElevation : ∀ elapsed,
    lengthInMeters (setup.aircraftElevationAt elapsed) =
      lengthInMeters setup.initialClearance
  upwardPlanarGround : ∀ distance,
    lengthInMeters (setup.groundElevationAt distance) =
      lengthInMeters distance * Real.Angle.tan setup.slopeAngle

/-! ## Collision event and displayed answers -/

/-!
An elapsed time is the first ground impact when aircraft and ground elevations
coincide then, the time is positive, and the aircraft remains strictly above
the ground at every earlier elapsed time.
-/
def IsFirstGroundImpact
    (setup : RisingGroundFlightSetup) (impactTime : FlightDuration) : Prop :=
  setup.aircraftElevationAt impactTime =
      setup.groundElevationAt (setup.horizontalDistanceAt impactTime) ∧
    0 < durationInSeconds impactTime ∧
    ∀ earlierTime,
      durationInSeconds earlierTime < durationInSeconds impactTime →
        lengthInMeters
            (setup.groundElevationAt
              (setup.horizontalDistanceAt earlierTime)) <
          lengthInMeters (setup.aircraftElevationAt earlierTime)

/-- Labels of the four answers supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Seconds printed beside each displayed answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 2 / 5
  | .B => 4 / 5
  | .C => 13 / 10
  | .D => 9 / 5

/-!
A physical impact time agrees with a displayed tenth-second answer when its
second readout is within half of one tenth of the printed value.
-/
def MatchesAnswerChoice
    (impactTime : FlightDuration) (choice : AnswerChoice) : Prop :=
  |durationInSeconds impactTime - choice.seconds| ≤ 1 / 20

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The first impact occurs when
`h = (v * t) * tan(theta)`, hence
`t = h / (v * tan(theta))`.  With the stated `1300 km/h`, `35 m`, and
`4.3 degrees`, this time rounds to `1.3 s`, recorded answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0731:target`.
-/
theorem firstGroundImpact_matches_recordedAnswerC
    (setup : RisingGroundFlightSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalFlightParameters setup)
    (_laws : SatisfiesHorizontalFlightAndSlopeLaws setup) :
    ∃ impactTime : FlightDuration,
      IsFirstGroundImpact setup impactTime ∧
        durationInSeconds impactTime =
          lengthInMeters setup.initialClearance /
            (speedInMetersPerSecond setup.flightSpeed *
              Real.Angle.tan setup.slopeAngle) ∧
        MatchesAnswerChoice impactTime recordedAnswerChoice := by
  have hSpeedConversion (speed : DimSpeed) :
      speedInMetersPerSecond speed =
        (5 / 18 : ℝ) *
          speedReadout LengthUnit.kilometers TimeUnit.hours speed := by
    let kilometersPerHour : UnitChoices :=
      {UnitChoices.SI with
        length := LengthUnit.kilometers, time := TimeUnit.hours}
    have hSpeedScale :
        kilometersPerHour.dimScale UnitChoices.SI (L𝓭 * T𝓭⁻¹) =
          (⟨5 / 18, by norm_num⟩ : NNReal) := by
      simp [kilometersPerHour, UnitChoices.dimScale,
        LengthUnit.kilometers, TimeUnit.hours]
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_rpow]
      norm_num [NNReal.toReal]
    have hUnits :=
      congrArg (fun quantity : WithDim (L𝓭 * T𝓭⁻¹) NNReal =>
        (quantity.val : ℝ))
        (speed.2 kilometersPerHour UnitChoices.SI)
    rw [show dim (WithDim (L𝓭 * T𝓭⁻¹) NNReal) =
        L𝓭 * T𝓭⁻¹ by rfl, hSpeedScale] at hUnits
    dsimp [kilometersPerHour, speedInMetersPerSecond,
      speedReadout] at hUnits
    norm_num at hUnits
    exact hUnits
  have hSpeed :
      speedInMetersPerSecond setup.flightSpeed = 3250 / 9 := by
    rw [hSpeedConversion, _problem.speedKilometersPerHour]
    norm_num
  have hPiBounds :
      (31 / 10 : ℝ) < Real.pi ∧ Real.pi < 16 / 5 := by
    have hSinAtLowerTest :
        Real.sin (31 / 60 : ℝ) < (1 / 2 : ℝ) := by
      have h := Real.sin_bound (x := (31 / 60 : ℝ)) (by norm_num)
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 31 / 60)] at h
      nlinarith [le_abs_self
        (Real.sin (31 / 60 : ℝ) -
          ((31 / 60 : ℝ) - (31 / 60 : ℝ) ^ 3 / 6))]
    have hSinAtUpperTest :
        (1 / 2 : ℝ) < Real.sin (8 / 15 : ℝ) := by
      have h := Real.sin_bound (x := (8 / 15 : ℝ)) (by norm_num)
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 15)] at h
      nlinarith [neg_abs_le
        (Real.sin (8 / 15 : ℝ) -
          ((8 / 15 : ℝ) - (8 / 15 : ℝ) ^ 3 / 6))]
    constructor
    · by_contra hpi
      have hpiLe : Real.pi ≤ (31 / 10 : ℝ) := by
        linarith
      have hmono :
          Real.sin (Real.pi / 6) ≤ Real.sin (31 / 60 : ℝ) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.two_le_pi]
        · nlinarith
      rw [Real.sin_pi_div_six] at hmono
      linarith
    · by_contra hpi
      have hpiGe : (16 / 5 : ℝ) ≤ Real.pi := by
        linarith
      have hmono :
          Real.sin (8 / 15 : ℝ) ≤ Real.sin (Real.pi / 6) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
        · nlinarith
      rw [Real.sin_pi_div_six] at hmono
      linarith
  let x : ℝ := 43 * Real.pi / 1800
  have hxPos : 0 < x := by
    dsimp [x]
    positivity
  have hxLower : (1333 / 18000 : ℝ) < x := by
    dsimp [x]
    nlinarith [hPiBounds.1]
  have hxUpper : x < (77 / 1000 : ℝ) := by
    dsimp [x]
    nlinarith [hPiBounds.2]
  have hxAbs : |x| ≤ 1 := by
    rw [abs_of_pos hxPos]
    linarith
  have hx3Le : x ^ 3 ≤ (77 / 1000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hxPos.le hxUpper.le 3
  have hx4Le : x ^ 4 ≤ (77 / 1000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hxPos.le hxUpper.le 4
  have hSinBound := Real.sin_bound hxAbs
  have hCosBound := Real.cos_bound hxAbs
  rw [abs_of_pos hxPos] at hSinBound hCosBound
  rcases abs_le.mp hSinBound with ⟨hSinBoundLower, hSinBoundUpper⟩
  rcases abs_le.mp hCosBound with ⟨hCosBoundLower, _hCosBoundUpper⟩
  have hSinLower : (14 / 195 : ℝ) < Real.sin x := by
    nlinarith
  have hx3Nonnegative : 0 ≤ x ^ 3 := by
    positivity
  have hSinUpper : Real.sin x < (77 / 1000 : ℝ) := by
    nlinarith
  have hCosLower : (997 / 1000 : ℝ) < Real.cos x := by
    have hx2Le : x ^ 2 ≤ (77 / 1000 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hxPos.le hxUpper.le 2
    nlinarith
  have hCosPos : 0 < Real.cos x := by
    linarith
  have hSinNonnegative : 0 ≤ Real.sin x := by
    nlinarith
  have hSinLeTan : Real.sin x ≤ Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    apply (le_div_iff₀ hCosPos).2
    have hmul :=
      mul_le_mul_of_nonneg_left (Real.cos_le_one x) hSinNonnegative
    nlinarith
  have hTanBounds :
      (14 / 195 : ℝ) < Real.tan x ∧
        Real.tan x < (126 / 1625 : ℝ) := by
    constructor
    · linarith
    · rw [Real.tan_eq_sin_div_cos]
      apply (div_lt_iff₀ hCosPos).2
      nlinarith
  have hAngleTan :
      Real.Angle.tan setup.slopeAngle = Real.tan x := by
    rw [_problem.slopeAngleDegrees]
    simp only [angleOfDegrees, Real.Angle.tan_coe]
    congr 1
    dsimp [x]
    ring
  have hTanPos : 0 < Real.Angle.tan setup.slopeAngle := by
    rw [hAngleTan]
    linarith [hTanBounds.1]
  have hDenominatorPos :
      0 < speedInMetersPerSecond setup.flightSpeed *
      Real.Angle.tan setup.slopeAngle :=
    mul_pos _physical.flightSpeedPositive hTanPos
  let impactSeconds : ℝ :=
    lengthInMeters setup.initialClearance /
      (speedInMetersPerSecond setup.flightSpeed *
        Real.Angle.tan setup.slopeAngle)
  have hImpactSecondsPos : 0 < impactSeconds := by
    dsimp [impactSeconds]
    exact div_pos _physical.initialClearancePositive hDenominatorPos
  let impactTime : FlightDuration :=
    CarriesDimension.toDimensionful
      ({UnitChoices.SI with time := TimeUnit.seconds} : UnitChoices)
      (show WithDim T𝓭 NNReal from
        ⟨⟨impactSeconds, hImpactSecondsPos.le⟩⟩)
  have hImpactReadout :
      durationInSeconds impactTime = impactSeconds := by
    simp [impactTime, durationInSeconds, durationReadout,
      CarriesDimension.toDimensionful_apply_apply,
      TimeUnit.seconds]
    rfl
  have length_ext (a b : FlightLength)
      (hmeters : lengthInMeters a = lengthInMeters b) : a = b := by
    let meterUnits : UnitChoices :=
      {UnitChoices.SI with length := LengthUnit.meters}
    apply (CarriesDimension.toDimensionful meterUnits).symm.injective
    change a meterUnits = b meterUnits
    apply WithDim.ext
    apply NNReal.eq
    simpa [meterUnits, lengthInMeters, lengthReadout] using hmeters
  have hImpactElevationMeters :
      lengthInMeters (setup.aircraftElevationAt impactTime) =
        lengthInMeters
          (setup.groundElevationAt
            (setup.horizontalDistanceAt impactTime)) := by
    rw [_laws.aircraftKeepsConstantElevation,
      _laws.upwardPlanarGround, _laws.horizontalMotion,
      hImpactReadout]
    dsimp [impactSeconds]
    field_simp [ne_of_gt _physical.flightSpeedPositive,
      ne_of_gt hTanPos]
  have hFirstImpact : IsFirstGroundImpact setup impactTime := by
    have hImpactTimePos : 0 < durationInSeconds impactTime := by
      rw [hImpactReadout]
      exact hImpactSecondsPos
    refine ⟨length_ext _ _ hImpactElevationMeters,
      hImpactTimePos, ?_⟩
    intro earlierTime hEarlier
    rw [_laws.upwardPlanarGround, _laws.horizontalMotion,
      _laws.aircraftKeepsConstantElevation]
    rw [hImpactReadout] at hEarlier
    dsimp [impactSeconds] at hEarlier
    have hBeforeImpact :=
      (lt_div_iff₀ hDenominatorPos).mp hEarlier
    calc
      (speedInMetersPerSecond setup.flightSpeed *
          durationInSeconds earlierTime) *
            Real.Angle.tan setup.slopeAngle =
          durationInSeconds earlierTime *
            (speedInMetersPerSecond setup.flightSpeed *
              Real.Angle.tan setup.slopeAngle) := by ring
      _ < lengthInMeters setup.initialClearance := hBeforeImpact
  have hImpactFormula :
      impactSeconds = 63 / (650 * Real.tan x) := by
    dsimp [impactSeconds]
    rw [_problem.initialClearanceMeters, hSpeed, hAngleTan]
    ring
  have hScaledTanPos : 0 < 650 * Real.tan x := by
    have : 0 < Real.tan x := by
      linarith [hTanBounds.1]
    positivity
  have hImpactLower : (5 / 4 : ℝ) < impactSeconds := by
    rw [hImpactFormula]
    apply (lt_div_iff₀ hScaledTanPos).2
    nlinarith [hTanBounds.2]
  have hImpactUpper : impactSeconds < (27 / 20 : ℝ) := by
    rw [hImpactFormula]
    apply (div_lt_iff₀ hScaledTanPos).2
    nlinarith [hTanBounds.1]
  have hMatchesChoice :
      MatchesAnswerChoice impactTime recordedAnswerChoice := by
    rw [MatchesAnswerChoice, hImpactReadout]
    simp only [recordedAnswerChoice, AnswerChoice.seconds]
    rw [abs_le]
    constructor
    · linarith only [hImpactLower]
    · linarith only [hImpactUpper]
  refine ⟨impactTime, hFirstImpact, ?_, hMatchesChoice⟩
  simpa [impactSeconds] using hImpactReadout

end PhyXMiniProblems.ProblemPhyXMini0731
