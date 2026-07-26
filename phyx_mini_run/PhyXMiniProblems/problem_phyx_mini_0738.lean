import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0738

open Dimension

/-!
# Release height of a radar decoy

An airplane moving at `290 km/h` dives at `30 degrees` below the horizontal
and passively releases a radar decoy.  The decoy then travels `700 m`
horizontally before striking level ground.  The idealized model neglects drag
and uses uniform downward gravitational acceleration.

Lengths, durations, speeds, signed velocity components, and acceleration are
unit-independent Physlib quantities.  Real numbers occur only at explicitly
named unit readouts, in trigonometric values, and in displayed answer choices.
In particular, `releaseHeight` is an independent physical field.  No premise
assigns it the recorded `897 m` answer or the eliminated projectile formula.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The physical dimension of velocity, `L T⁻¹`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed Cartesian coordinate or displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration elapsed since release. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed component of planar velocity. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed Cartesian length component in metres. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical duration in seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a speed in the selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an unsigned physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Read an unsigned physical speed in kilometres per hour. -/
def speedInKilometersPerHour (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.kilometers TimeUnit.hours speed

/-- Read a signed velocity component in metres per second. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Convert a numerical degree readout into Mathlib's physical angle type. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical roles and primary-figure vocabulary -/

/-- The ideal point-particle model used after the decoy is released. -/
inductive ProjectileModel where
  | constantGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- The objects visibly represented in image `738.png`. -/
inductive FigureObject where
  | airplane
  | radarDecoy
  | ground
  deriving DecidableEq, Fintype, Repr

/-- The two mathematical labels printed in the primary image. -/
inductive FigureLabel where
  | diveAngleTheta
  | horizontalDistanceD
  deriving DecidableEq, Fintype, Repr

/-- The three points needed to interpret the displayed height and distance. -/
inductive FigurePoint where
  | releasePoint
  | groundBelowRelease
  | impactPoint
  deriving DecidableEq, Fintype, Repr

/-- A physical position in the vertical plane, with upward-positive height. -/
structure PlanarPosition where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-- A signed planar velocity, with upward-positive vertical component. -/
structure PlanarVelocity where
  horizontal : SignedVelocityQuantity
  vertical : SignedVelocityQuantity

/-!
The labelled physical geometry and qualitative content of the supplied
raster.  The image is schematic, but `coordinateOf` interprets its three
distinguished points in the physical horizontal/upward coordinate system.
-/
structure AirplaneDecoyFigure where
  coordinateOf : FigurePoint → PlanarPosition
  displayedDiveAngle : Real.Angle
  displayedHorizontalDistance : LengthQuantity
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  showsAirplaneFlightPath : Bool
  showsDecoyTrajectory : Bool
  showsAirplaneDirectionArrow : Bool
  showsDecoyDirectionArrow : Bool
  groundIsDrawnHorizontal : Bool
  diveAngleIsDrawnBelowHorizontal : Bool
  distanceArrowRunsReleaseToImpact : Bool

/-!
Independent physical quantities for the passive release and subsequent
flight.  Neither the flight duration nor the release height is defined from
an answer choice; governing laws below relate them to the observed impact.
-/
structure RadarDecoyReleaseSetup where
  model : ProjectileModel
  airplaneSpeedAtRelease : DimSpeed
  diveAngleBelowHorizontal : Real.Angle
  decoyInitialVelocity : PlanarVelocity
  gravitationalAcceleration : AccelerationQuantity
  horizontalDistanceToImpact : LengthQuantity
  releaseHeight : LengthQuantity
  flightDuration : DurationQuantity
  positionAt : DurationQuantity → PlanarPosition
  figure : AirplaneDecoyFigure

/-! ## Figure evidence, source readouts, and governing laws -/

/-!
Primary-image evidence.  It records the objects, paths, arrows, labels, and
spatial relations shown in `738.png`; the release height is only identified
as a vertical separation and is not assigned a numerical value.
-/
structure MatchesPrimaryAirplaneDecoyFigure
    (setup : RadarDecoyReleaseSetup) : Prop where
  everyObjectIsShown : ∀ object, setup.figure.showsObject object = true
  everyLabelIsShown : ∀ label, setup.figure.showsLabel label = true
  airplanePathIsShown : setup.figure.showsAirplaneFlightPath = true
  decoyTrajectoryIsShown : setup.figure.showsDecoyTrajectory = true
  airplaneArrowIsShown : setup.figure.showsAirplaneDirectionArrow = true
  decoyArrowIsShown : setup.figure.showsDecoyDirectionArrow = true
  horizontalGroundIsShown : setup.figure.groundIsDrawnHorizontal = true
  diveAngleHasFigureMeaning :
    setup.figure.diveAngleIsDrawnBelowHorizontal = true
  distanceArrowHasFigureMeaning :
    setup.figure.distanceArrowRunsReleaseToImpact = true
  angleLabelMatchesSetup :
    setup.figure.displayedDiveAngle = setup.diveAngleBelowHorizontal
  distanceLabelMatchesSetup :
    setup.figure.displayedHorizontalDistance =
      setup.horizontalDistanceToImpact
  groundReferenceIsVerticallyBelowRelease :
    signedLengthInMeters
        (setup.figure.coordinateOf .groundBelowRelease).horizontal =
      signedLengthInMeters
        (setup.figure.coordinateOf .releasePoint).horizontal
  releasePointIsAboveGround :
    signedLengthInMeters
        (setup.figure.coordinateOf .groundBelowRelease).vertical <
      signedLengthInMeters
        (setup.figure.coordinateOf .releasePoint).vertical
  impactLiesOnSameGroundLevel :
    signedLengthInMeters
        (setup.figure.coordinateOf .impactPoint).vertical =
      signedLengthInMeters
        (setup.figure.coordinateOf .groundBelowRelease).vertical
  impactLiesToTheRight :
    signedLengthInMeters
        (setup.figure.coordinateOf .releasePoint).horizontal <
      signedLengthInMeters
        (setup.figure.coordinateOf .impactPoint).horizontal
  labelledHorizontalSeparation :
    signedLengthInMeters
          (setup.figure.coordinateOf .impactPoint).horizontal -
        signedLengthInMeters
          (setup.figure.coordinateOf .releasePoint).horizontal =
      lengthInMeters setup.horizontalDistanceToImpact
  releaseHeightIsVerticalSeparation :
    signedLengthInMeters
          (setup.figure.coordinateOf .releasePoint).vertical -
        signedLengthInMeters
          (setup.figure.coordinateOf .groundBelowRelease).vertical =
      lengthInMeters setup.releaseHeight
  endpointIsImpactPoint :
    setup.positionAt setup.flightDuration =
      setup.figure.coordinateOf .impactPoint

/-!
Numerical readouts and qualitative idealization stated or conventionally
implicit in the textbook projectile problem.  No release-height value occurs
in this structure.
-/
structure MatchesProblemDescription
    (setup : RadarDecoyReleaseSetup) : Prop where
  idealProjectileModel :
    setup.model = .constantGravityNegligibleDrag
  airplaneSpeedKilometersPerHour :
    speedInKilometersPerHour setup.airplaneSpeedAtRelease = 290
  diveAngleDegrees : setup.diveAngleBelowHorizontal = degrees 30
  horizontalDistanceMeters :
    lengthInMeters setup.horizontalDistanceToImpact = 700

/-!
The standard near-Earth gravitational calibration used in the calculation.
This is a governing environmental datum, not a release-height assumption.
-/
structure UsesStandardNearEarthGravity
    (setup : RadarDecoyReleaseSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5

/-- Positivity and the rightward/downward branch depicted in the figure. -/
structure HasPhysicalRadarDecoyParameters
    (setup : RadarDecoyReleaseSetup) : Prop where
  speedPositive : 0 < speedInMetersPerSecond setup.airplaneSpeedAtRelease
  distancePositive : 0 < lengthInMeters setup.horizontalDistanceToImpact
  releaseHeightPositive : 0 < lengthInMeters setup.releaseHeight
  flightDurationPositive : 0 < durationInSeconds setup.flightDuration
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  divePointsRight : 0 < Real.Angle.cos setup.diveAngleBelowHorizontal
  divePointsDown : 0 < Real.Angle.sin setup.diveAngleBelowHorizontal

/-!
The passive-release and no-drag constant-gravity laws in coherent SI
components:

* the decoy initially inherits the airplane's rightward and downward velocity;
* horizontal velocity then remains constant; and
* vertical displacement includes uniform downward gravitational acceleration.

These are general trajectory relations for every physical elapsed duration.
They contain neither the eliminated height formula nor an answer value.
-/
structure SatisfiesPassiveReleaseProjectileLaws
    (setup : RadarDecoyReleaseSetup) : Prop where
  inheritsHorizontalVelocity :
    signedVelocityInMetersPerSecond
        setup.decoyInitialVelocity.horizontal =
      speedInMetersPerSecond setup.airplaneSpeedAtRelease *
        Real.Angle.cos setup.diveAngleBelowHorizontal
  inheritsDownwardVelocity :
    signedVelocityInMetersPerSecond setup.decoyInitialVelocity.vertical =
      -(speedInMetersPerSecond setup.airplaneSpeedAtRelease *
        Real.Angle.sin setup.diveAngleBelowHorizontal)
  uniformHorizontalMotion : ∀ duration : DurationQuantity,
    signedLengthInMeters (setup.positionAt duration).horizontal -
        signedLengthInMeters
          (setup.figure.coordinateOf .releasePoint).horizontal =
      signedVelocityInMetersPerSecond
          setup.decoyInitialVelocity.horizontal *
        durationInSeconds duration
  verticalConstantGravityMotion : ∀ duration : DurationQuantity,
    signedLengthInMeters (setup.positionAt duration).vertical -
        signedLengthInMeters
          (setup.figure.coordinateOf .releasePoint).vertical =
      signedVelocityInMetersPerSecond setup.decoyInitialVelocity.vertical *
          durationInSeconds duration -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          durationInSeconds duration ^ 2

/-! ## Eliminated height, displayed choices, and formalization target -/

/-!
The exact SI flight time obtained from the stated horizontal distance and the
horizontal component of the stated airplane speed.
-/
noncomputable def computedFlightTimeInSeconds : ℝ :=
  let speedMetersPerSecond : ℝ := 290 * 1000 / 3600
  700 /
    (speedMetersPerSecond * Real.Angle.cos (degrees 30))

/-!
The exact unrounded release height predicted by the stated data and standard
gravity after eliminating the flight time.  The setup's independent physical
height field is not definitionally equal to this scalar expression.
-/
noncomputable def computedReleaseHeightInMeters : ℝ :=
  let speedMetersPerSecond : ℝ := 290 * 1000 / 3600
  let flightTimeSeconds : ℝ := computedFlightTimeInSeconds
  speedMetersPerSecond * Real.Angle.sin (degrees 30) *
      flightTimeSeconds +
    (1 / 2 : ℝ) * (49 / 5 : ℝ) * flightTimeSeconds ^ 2

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Height in metres printed beside each answer label. -/
def AnswerChoice.heightInMeters : AnswerChoice → ℝ
  | .A => 619
  | .B => 751
  | .C => 897
  | .D => 926

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a whole-metre display to nearest-metre precision. -/
def MatchesDisplayedWholeMeterHeight
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters height - choice.heightInMeters| ≤ (1 / 2 : ℝ)

/-- A displayed choice is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedHeight
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters height - choice.heightInMeters| <
      |lengthInMeters height - other.heightInMeters|

/-!
Eliminating the positive flight duration from the two component equations
gives the standard downward-launch formula

`h = d sin(theta) / cos(theta)
       + g d^2 / (2 (v cos(theta))^2)`.

This conclusion is derived from the general laws and is not a premise field.
-/
lemma releaseHeight_eq_projectileExpression
    (setup : RadarDecoyReleaseSetup)
    (_figure : MatchesPrimaryAirplaneDecoyFigure setup)
    (_physical : HasPhysicalRadarDecoyParameters setup)
    (_laws : SatisfiesPassiveReleaseProjectileLaws setup) :
    lengthInMeters setup.releaseHeight =
      lengthInMeters setup.horizontalDistanceToImpact *
          Real.Angle.sin setup.diveAngleBelowHorizontal /
          Real.Angle.cos setup.diveAngleBelowHorizontal +
        accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.horizontalDistanceToImpact ^ 2 /
          (2 *
            (speedInMetersPerSecond setup.airplaneSpeedAtRelease *
              Real.Angle.cos setup.diveAngleBelowHorizontal) ^ 2) := by
  have hHorizontal :=
    _laws.uniformHorizontalMotion setup.flightDuration
  rw [_figure.endpointIsImpactPoint,
    _figure.labelledHorizontalSeparation,
    _laws.inheritsHorizontalVelocity] at hHorizontal
  have hVertical :=
    _laws.verticalConstantGravityMotion setup.flightDuration
  rw [_figure.endpointIsImpactPoint,
    _figure.impactLiesOnSameGroundLevel,
    _laws.inheritsDownwardVelocity] at hVertical
  have hHeightEquation :
      lengthInMeters setup.releaseHeight =
        speedInMetersPerSecond setup.airplaneSpeedAtRelease *
            Real.Angle.sin setup.diveAngleBelowHorizontal *
            durationInSeconds setup.flightDuration +
          (1 / 2 : ℝ) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            durationInSeconds setup.flightDuration ^ 2 := by
    nlinarith [_figure.releaseHeightIsVerticalSeparation]
  have hSpeedNonzero :
      speedInMetersPerSecond setup.airplaneSpeedAtRelease ≠ 0 :=
    ne_of_gt _physical.speedPositive
  have hCosNonzero :
      Real.Angle.cos setup.diveAngleBelowHorizontal ≠ 0 :=
    ne_of_gt _physical.divePointsRight
  have hHorizontalSpeedNonzero :
      speedInMetersPerSecond setup.airplaneSpeedAtRelease *
          Real.Angle.cos setup.diveAngleBelowHorizontal ≠ 0 :=
    mul_ne_zero hSpeedNonzero hCosNonzero
  have hTime :
      durationInSeconds setup.flightDuration =
        lengthInMeters setup.horizontalDistanceToImpact /
          (speedInMetersPerSecond setup.airplaneSpeedAtRelease *
            Real.Angle.cos setup.diveAngleBelowHorizontal) := by
    apply (eq_div_iff hHorizontalSpeedNonzero).2
    simpa [mul_comm] using hHorizontal.symm
  rw [hTime] at hHeightEquation
  rw [hHeightEquation]
  field_simp [hSpeedNonzero, hCosNonzero]

/-!
With `v = 290 km/h`, `theta = 30 degrees`, `d = 700 m`, and
`g = 9.80 m/s^2`, the model gives approximately `897.48 m`.  Thus the release
height has computed value `computedReleaseHeightInMeters`, agrees with the
whole-metre display `897 m`, and recorded choice C is uniquely closest.

This formalizes `thm:physics:phyx_mini_0738:target`.
-/
theorem problem_phyx_mini_0738
    (setup : RadarDecoyReleaseSetup)
    (_figure : MatchesPrimaryAirplaneDecoyFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalRadarDecoyParameters setup)
    (_laws : SatisfiesPassiveReleaseProjectileLaws setup) :
    lengthInMeters setup.releaseHeight =
        computedReleaseHeightInMeters ∧
      MatchesDisplayedWholeMeterHeight
        setup.releaseHeight recordedDatasetAnswer ∧
      IsUniqueClosestDisplayedHeight
        setup.releaseHeight recordedDatasetAnswer := by
  have speedConversion (speed : DimSpeed) :
      speedInMetersPerSecond speed =
        (5 / 18 : ℝ) * speedInKilometersPerHour speed := by
    have hUnits := speed.2
      ({UnitChoices.SI with
        length := LengthUnit.kilometers, time := TimeUnit.hours} : UnitChoices)
      UnitChoices.SI
    have hUnitsVal := congrArg
      (fun quantity : WithDim (L𝓭 * T𝓭⁻¹) NNReal => (quantity.val : ℝ))
      hUnits
    change
      ((speed UnitChoices.SI).val : ℝ) =
        (5 / 18 : ℝ) *
          ((speed
            {UnitChoices.SI with
              length := LengthUnit.kilometers,
              time := TimeUnit.hours}).val : ℝ)
    rw [hUnitsVal]
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul]
    congr 1
    have hOneKilometerPerHour := congrArg
      (fun quantity : WithDim (L𝓭 * T𝓭⁻¹) NNReal => (quantity.val : ℝ))
      DimSpeed.oneKilometerPerHour_in_SI
    simpa only [DimSpeed.oneKilometerPerHour,
      CarriesDimension.toDimensionful_apply_apply, WithDim.smul_val,
      smul_eq_mul, mul_one, NNReal.coe_div, NNReal.coe_ofNat] using
        hOneKilometerPerHour
  have hSpeed :
      speedInMetersPerSecond setup.airplaneSpeedAtRelease =
        (725 / 9 : ℝ) := by
    rw [speedConversion,
      _description.airplaneSpeedKilometersPerHour]
    norm_num
  have hSin :
      Real.Angle.sin setup.diveAngleBelowHorizontal = (1 / 2 : ℝ) := by
    rw [_description.diveAngleDegrees]
    change Real.sin (30 * Real.pi / 180) = (1 / 2 : ℝ)
    rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring]
    exact Real.sin_pi_div_six
  have hCos :
      Real.Angle.cos setup.diveAngleBelowHorizontal =
        Real.sqrt 3 / 2 := by
    rw [_description.diveAngleDegrees]
    change Real.cos (30 * Real.pi / 180) = Real.sqrt 3 / 2
    rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring]
    exact Real.cos_pi_div_six
  have hSinThirty :
      Real.Angle.sin (degrees 30) = (1 / 2 : ℝ) := by
    change Real.sin (30 * Real.pi / 180) = (1 / 2 : ℝ)
    rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring]
    exact Real.sin_pi_div_six
  have hCosThirty :
      Real.Angle.cos (degrees 30) = Real.sqrt 3 / 2 := by
    change Real.cos (30 * Real.pi / 180) = Real.sqrt 3 / 2
    rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring]
    exact Real.cos_pi_div_six
  have hSqrtNonzero : Real.sqrt (3 : ℝ) ≠ 0 := by
    positivity
  have hSqrtSquare : Real.sqrt (3 : ℝ) ^ 2 = 3 := by
    norm_num
  have hSqrtCube :
      Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt (3 : ℝ) ^ 3 =
          Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hSqrtSquare]
  have hLinearHeightTerm :
      (700 : ℝ) * (1 / 2) / (Real.sqrt 3 / 2) =
        (700 / 3 : ℝ) * Real.sqrt 3 := by
    field_simp [hSqrtNonzero]
    nlinarith [hSqrtSquare]
  have hGravityHeightTerm :
      (49 / 5 : ℝ) * 700 ^ 2 /
          (2 * ((725 / 9) * (Real.sqrt 3 / 2)) ^ 2) =
        2074464 / 4205 := by
    rw [mul_pow, div_pow, div_pow, hSqrtSquare]
    norm_num
  have hHeightExact :
      lengthInMeters setup.releaseHeight =
        (700 / 3 : ℝ) * Real.sqrt 3 + 2074464 / 4205 := by
    rw [releaseHeight_eq_projectileExpression
      setup _figure _physical _laws]
    rw [_description.horizontalDistanceMeters, hSpeed,
      _gravity.gravityMetersPerSecondSquared, hSin, hCos]
    rw [hLinearHeightTerm, hGravityHeightTerm]
  have hComputedHeightExact :
      computedReleaseHeightInMeters =
        (700 / 3 : ℝ) * Real.sqrt 3 + 2074464 / 4205 := by
    unfold computedReleaseHeightInMeters computedFlightTimeInSeconds
    dsimp only
    rw [hSinThirty, hCosThirty]
    field_simp [hSqrtNonzero]
    ring_nf
    rw [hSqrtSquare, hSqrtCube]
    ring
  have hHeightComputed :
      lengthInMeters setup.releaseHeight =
        computedReleaseHeightInMeters :=
    hHeightExact.trans hComputedHeightExact.symm
  have hSqrtLower : (5 / 3 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 3)]
    norm_num
  have hSqrtUpper : Real.sqrt 3 < (97 / 56 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 97 / 56)]
    norm_num
  have hHeightLower :
      (897 : ℝ) < lengthInMeters setup.releaseHeight := by
    rw [hHeightExact]
    nlinarith
  have hHeightUpper :
      lengthInMeters setup.releaseHeight < (1795 / 2 : ℝ) := by
    rw [hHeightExact]
    nlinarith
  have hMatches :
      MatchesDisplayedWholeMeterHeight
        setup.releaseHeight recordedDatasetAnswer := by
    unfold MatchesDisplayedWholeMeterHeight recordedDatasetAnswer
    simp only [AnswerChoice.heightInMeters]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hUnique :
      IsUniqueClosestDisplayedHeight
        setup.releaseHeight recordedDatasetAnswer := by
    unfold IsUniqueClosestDisplayedHeight recordedDatasetAnswer
    intro other hOther
    fin_cases other
    · simp only [AnswerChoice.heightInMeters]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith
    · simp only [AnswerChoice.heightInMeters]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith
    · contradiction
    · simp only [AnswerChoice.heightInMeters]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
  exact ⟨hHeightComputed, hMatches, hUnique⟩

end PhyXMiniProblems.ProblemPhyXMini0738
