import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0683

open Dimension

/-!
# Fire-hose projectile motion

The nozzle is the origin of a planar coordinate system.  The building is a
horizontal distance `d` away, and the water strikes it at height `h`.  The
stream leaves the nozzle with speed `v_i` at an angle `theta_i` above the
horizontal and then follows uniform-gravity projectile motion without drag.

Lengths, speeds, and accelerations are represented by unit-independent
Physlib quantities.  Real numbers occur only as explicitly named SI readouts,
time coordinates in seconds, and dimensionless radian representatives of
angles.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- Acceleration has physical dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, used for the figure labels `d` and `h`. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length, used for Cartesian coordinate components. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical acceleration magnitude, used for `g`. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative physical length in metres. -/
def lengthMagnitudeInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed Cartesian length component in metres. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a nonnegative speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a nonnegative acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Physical setup and primary-image labels -/

/-- A point in the vertical plane of the illustrated water trajectory. -/
structure PlanarPosition where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-- The three geometrically significant points marked or implied by the image. -/
inductive FigurePoint where
  /-- The hose nozzle and launch point of the water. -/
  | hoseNozzle
  /-- The point where the vertical building face meets the ground. -/
  | buildingGroundContact
  /-- The point where the stream strikes the building. -/
  | waterImpact
  deriving DecidableEq, Repr

/--
Geometric objects and labels read from the supplied firefighting figure.
The booleans retain visible spatial information that does not enter the final
closed form directly.
-/
structure FireHoseFigure where
  coordinateOf : FigurePoint → PlanarPosition
  initialVelocityArrowSpeed : DimSpeed
  initialVelocityArrowAngleRadians : ℝ
  horizontalDistanceLabel : LengthMagnitude
  impactHeightLabel : LengthMagnitude
  groundShownHorizontal : Bool
  buildingFaceShownVertical : Bool
  parabolicWaterArcShown : Bool

/--
The independent physical quantities and observables of the fire-hose stream.
The trajectory and impact observables are not defined from the requested
height formula; they are related only by the governing-law and figure
premises below.
-/
structure FireHoseProjectileSetup where
  horizontalDistance : LengthMagnitude
  impactHeight : LengthMagnitude
  initialSpeed : DimSpeed
  launchAngleRadians : ℝ
  gravitationalAcceleration : AccelerationMagnitude
  positionAtSeconds : ℝ → PlanarPosition
  impactTimeSeconds : ℝ
  figure : FireHoseFigure

/--
The no-drag constant-gravity projectile equations, expressed in coherent SI
component readouts for every nonnegative time in seconds.  The launch point is
the coordinate origin, so the two initial-position terms are zero.
-/
def SatisfiesUniformGravityProjectileMotion
    (setup : FireHoseProjectileSetup) : Prop :=
  ∀ timeSeconds : ℝ, 0 ≤ timeSeconds →
    signedLengthInMeters
        (setup.positionAtSeconds timeSeconds).horizontal =
      speedInMetersPerSecond setup.initialSpeed *
        Real.cos setup.launchAngleRadians * timeSeconds ∧
    signedLengthInMeters
        (setup.positionAtSeconds timeSeconds).vertical =
      speedInMetersPerSecond setup.initialSpeed *
          Real.sin setup.launchAngleRadians * timeSeconds -
        accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration * timeSeconds ^ 2 / 2

/--
Primary-image readouts and incidence geometry.  This connects the labels
`d`, `h`, `v_i`, and `theta_i` to the physical setup, places the nozzle and
building on the same horizontal ground, and identifies the positive-time
trajectory point that strikes the building.  It contains no eliminated
height formula.
-/
structure MatchesFireHoseFigure
    (setup : FireHoseProjectileSetup) : Prop where
  horizontalDistanceLabelMatches :
    setup.figure.horizontalDistanceLabel = setup.horizontalDistance
  impactHeightLabelMatches :
    setup.figure.impactHeightLabel = setup.impactHeight
  velocityArrowSpeedMatches :
    setup.figure.initialVelocityArrowSpeed = setup.initialSpeed
  velocityArrowAngleMatches :
    setup.figure.initialVelocityArrowAngleRadians =
      setup.launchAngleRadians
  horizontalGroundShown :
    setup.figure.groundShownHorizontal = true
  verticalBuildingFaceShown :
    setup.figure.buildingFaceShownVertical = true
  waterArcShown :
    setup.figure.parabolicWaterArcShown = true
  launchPointIsTrajectoryOrigin :
    setup.figure.coordinateOf .hoseNozzle = setup.positionAtSeconds 0
  launchHorizontalCoordinateIsZero :
    signedLengthInMeters
        (setup.figure.coordinateOf .hoseNozzle).horizontal = 0
  launchVerticalCoordinateIsZero :
    signedLengthInMeters
        (setup.figure.coordinateOf .hoseNozzle).vertical = 0
  buildingGroundIsLevelWithNozzle :
    signedLengthInMeters
        (setup.figure.coordinateOf .buildingGroundContact).vertical =
      signedLengthInMeters
        (setup.figure.coordinateOf .hoseNozzle).vertical
  distanceFromNozzleToBuilding :
    signedLengthInMeters
          (setup.figure.coordinateOf .buildingGroundContact).horizontal -
        signedLengthInMeters
          (setup.figure.coordinateOf .hoseNozzle).horizontal =
      lengthMagnitudeInMeters setup.horizontalDistance
  impactOccursAtPositiveTime :
    0 < setup.impactTimeSeconds
  impactPointIsOnTrajectory :
    setup.figure.coordinateOf .waterImpact =
      setup.positionAtSeconds setup.impactTimeSeconds
  impactPointIsOnBuildingFace :
    signedLengthInMeters
        (setup.figure.coordinateOf .waterImpact).horizontal =
      signedLengthInMeters
        (setup.figure.coordinateOf .buildingGroundContact).horizontal
  impactHeightAboveGround :
    signedLengthInMeters
          (setup.figure.coordinateOf .waterImpact).vertical -
        signedLengthInMeters
          (setup.figure.coordinateOf .buildingGroundContact).vertical =
      lengthMagnitudeInMeters setup.impactHeight

/--
For a stream launched toward the building at an acute angle, the impact
height is answer choice C:

`h = d tan(theta_i) - g d^2 / (2 v_i^2 cos(theta_i)^2)`.

This is the formalization of `thm:physics:phyx_mini_0683:target`.
-/
theorem problem_phyx_mini_0683
    (setup : FireHoseProjectileSetup)
    (h_motion : SatisfiesUniformGravityProjectileMotion setup)
    (h_figure : MatchesFireHoseFigure setup)
    (h_distance_positive :
      0 < lengthMagnitudeInMeters setup.horizontalDistance)
    (h_speed_positive : 0 < speedInMetersPerSecond setup.initialSpeed)
    (h_gravity_positive :
      0 < accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration)
    (h_launch_angle :
      setup.launchAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)) :
    lengthMagnitudeInMeters setup.impactHeight =
      lengthMagnitudeInMeters setup.horizontalDistance *
          Real.tan setup.launchAngleRadians -
        accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
            lengthMagnitudeInMeters setup.horizontalDistance ^ 2 /
          (2 * speedInMetersPerSecond setup.initialSpeed ^ 2 *
            Real.cos setup.launchAngleRadians ^ 2) := by
  rcases h_motion setup.impactTimeSeconds
      (le_of_lt h_figure.impactOccursAtPositiveTime) with
    ⟨h_horizontal_motion, h_vertical_motion⟩
  have h_impact_horizontal :
      signedLengthInMeters
          (setup.figure.coordinateOf .waterImpact).horizontal =
        lengthMagnitudeInMeters setup.horizontalDistance := by
    linarith [h_figure.impactPointIsOnBuildingFace,
      h_figure.distanceFromNozzleToBuilding,
      h_figure.launchHorizontalCoordinateIsZero]
  have h_impact_vertical :
      signedLengthInMeters
          (setup.figure.coordinateOf .waterImpact).vertical =
        lengthMagnitudeInMeters setup.impactHeight := by
    linarith [h_figure.impactHeightAboveGround,
      h_figure.buildingGroundIsLevelWithNozzle,
      h_figure.launchVerticalCoordinateIsZero]
  have h_horizontal_distance :
      lengthMagnitudeInMeters setup.horizontalDistance =
        speedInMetersPerSecond setup.initialSpeed *
          Real.cos setup.launchAngleRadians * setup.impactTimeSeconds := by
    calc
      lengthMagnitudeInMeters setup.horizontalDistance =
          signedLengthInMeters
            (setup.figure.coordinateOf .waterImpact).horizontal :=
        h_impact_horizontal.symm
      _ = signedLengthInMeters
            (setup.positionAtSeconds setup.impactTimeSeconds).horizontal := by
        rw [← h_figure.impactPointIsOnTrajectory]
      _ = speedInMetersPerSecond setup.initialSpeed *
            Real.cos setup.launchAngleRadians *
              setup.impactTimeSeconds :=
        h_horizontal_motion
  have h_impact_height :
      lengthMagnitudeInMeters setup.impactHeight =
        speedInMetersPerSecond setup.initialSpeed *
            Real.sin setup.launchAngleRadians * setup.impactTimeSeconds -
          accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
              setup.impactTimeSeconds ^ 2 / 2 := by
    calc
      lengthMagnitudeInMeters setup.impactHeight =
          signedLengthInMeters
            (setup.figure.coordinateOf .waterImpact).vertical :=
        h_impact_vertical.symm
      _ = signedLengthInMeters
            (setup.positionAtSeconds setup.impactTimeSeconds).vertical := by
        rw [← h_figure.impactPointIsOnTrajectory]
      _ = speedInMetersPerSecond setup.initialSpeed *
              Real.sin setup.launchAngleRadians *
                setup.impactTimeSeconds -
            accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
                setup.impactTimeSeconds ^ 2 / 2 :=
        h_vertical_motion
  have h_cos_positive : 0 < Real.cos setup.launchAngleRadians := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have h_pi_positive : 0 < Real.pi := Real.pi_pos
      linarith [h_launch_angle.1]
    · exact h_launch_angle.2
  have h_speed_ne :
      speedInMetersPerSecond setup.initialSpeed ≠ 0 :=
    ne_of_gt h_speed_positive
  have h_cos_ne : Real.cos setup.launchAngleRadians ≠ 0 :=
    ne_of_gt h_cos_positive
  rw [h_impact_height, h_horizontal_distance,
    Real.tan_eq_sin_div_cos]
  field_simp [h_speed_ne, h_cos_ne]

end PhyXMiniProblems.ProblemPhyXMini0683
