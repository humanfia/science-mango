import Mathlib
import Physlib.SpaceAndTime.Space.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0691

open Dimension

/-!
# Separation of two symmetrically launched droplets

Two molten-metal droplets leave one point with the same initial speed and
elevation angle.  The eastbound droplet has a positive horizontal velocity
component and the westbound droplet has the opposite component.  Their
vertical velocity components and gravitational accelerations agree.

Speed, elapsed time, and gravitational acceleration are represented by
unit-independent Physlib quantities.  Coordinates in `Space 2` and distances
between them are scalar readouts in metres in one fixed Cartesian frame:
coordinate `0` points east and coordinate `1` points upward.  The launch angle
is a dimensionless real readout in radians.

Assumption/target split:

* governing laws: ideal constant-gravity projectile kinematics in the two
  coordinate directions;
* previous-part results: none;
* data and figure readouts: common launch point, common speed `v_i`, common
  angle `θ_i`, outward east/west velocity arrows, two dashed trajectories,
  and the horizontal reference surface;
* current target conclusion: the distance between the droplets at elapsed
  time `t` is `2 * v_i * t * cos θ_i`.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A physical elapsed-time interval. -/
abbrev ElapsedTimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A physical gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read an elapsed-time interval in SI seconds. -/
def elapsedSeconds (time : ElapsedTimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Read a speed magnitude in SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Read an acceleration magnitude in SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-! ## Objects, directions, and primary-image labels -/

/-- The two molten-metal droplets distinguished by their launch directions. -/
inductive Droplet where
  | eastbound
  | westbound
  deriving DecidableEq, Fintype, Repr

/-- The two horizontal directions named in the problem. -/
inductive HorizontalDirection where
  | east
  | west
  deriving DecidableEq, Fintype, Repr

/-- Literal physical-quantity labels repeated on the two sides of the figure. -/
inductive FigureQuantityLabel where
  | initialVelocity
  | initialAngle
  deriving DecidableEq, Fintype, Repr

/-- The sign of a horizontal component when east is the positive direction. -/
def HorizontalDirection.sign : HorizontalDirection → ℝ
  | .east => 1
  | .west => -1

/-!
Qualitative evidence transcribed from the supplied bitmap.  The figure shows
two orange droplets, two red outward velocity arrows labelled `v_i`, two
angles labelled `θ_i`, mirror-image dashed trajectories, and a horizontal
reference surface meeting at the common launch point.
-/
structure SymmetricSplashFigure where
  launchDirection : Droplet → HorizontalDirection
  dropletShown : Droplet → Bool
  velocityArrowShown : Droplet → Bool
  velocityArrowAlongDashedTrajectory : Droplet → Bool
  dashedTrajectoryShown : Droplet → Bool
  quantityLabelShown : Droplet → FigureQuantityLabel → Bool
  commonLaunchPointShown : Bool
  horizontalReferenceSurfaceShown : Bool
  mirrorSymmetricLayoutShown : Bool

/-! ## Physical setup and assumptions -/

/-!
Independent data for the symmetric launch.  Positions are metre-coordinate
readouts in the fixed two-dimensional frame.  In particular, neither
trajectory is defined from the requested separation formula.
-/
structure SymmetricDropletSetup where
  figure : SymmetricSplashFigure
  initialSpeed : SpeedQuantity
  launchAngleRadians : ℝ
  gravitationalAcceleration : AccelerationQuantity
  commonLaunchPositionInMeters : Space 2
  positionInMeters : Droplet → ElapsedTimeQuantity → Space 2

/-- The direction assignments and literal visual evidence in the primary image. -/
structure MatchesPrimaryFigure (setup : SymmetricDropletSetup) : Prop where
  eastboundPointsEast :
    setup.figure.launchDirection .eastbound = .east
  westboundPointsWest :
    setup.figure.launchDirection .westbound = .west
  everyDropletShown :
    ∀ droplet, setup.figure.dropletShown droplet = true
  everyVelocityArrowShown :
    ∀ droplet, setup.figure.velocityArrowShown droplet = true
  everyVelocityArrowFollowsPath :
    ∀ droplet,
      setup.figure.velocityArrowAlongDashedTrajectory droplet = true
  everyDashedTrajectoryShown :
    ∀ droplet, setup.figure.dashedTrajectoryShown droplet = true
  everyQuantityLabelShown :
    ∀ droplet label, setup.figure.quantityLabelShown droplet label = true
  commonLaunchPoint : setup.figure.commonLaunchPointShown = true
  horizontalReferenceSurface :
    setup.figure.horizontalReferenceSurfaceShown = true
  mirrorSymmetricLayout : setup.figure.mirrorSymmetricLayoutShown = true

/-!
Physical branch conditions: the speed and gravitational acceleration are
positive, and the common elevation angle lies between horizontal and vertical.
-/
structure HasPhysicalParameters (setup : SymmetricDropletSetup) : Prop where
  initialSpeedPositive :
    0 < speedInMetersPerSecond setup.initialSpeed
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  launchAngleNonnegative : 0 ≤ setup.launchAngleRadians
  launchAngleAtMostVertical : setup.launchAngleRadians ≤ Real.pi / 2

/-!
Ideal projectile motion in a uniform downward gravitational field, with no
air resistance.  Coordinate `0` points east and coordinate `1` points upward.
The horizontal component has the sign supplied by the figure direction; both
droplets share the same vertical component and acceleration.  This governing
law contains no distance-between-droplets formula.
-/
structure SatisfiesIdealProjectileKinematics
    (setup : SymmetricDropletSetup) : Prop where
  horizontalPosition : ∀ droplet time,
    setup.positionInMeters droplet time 0 =
      setup.commonLaunchPositionInMeters 0 +
        (setup.figure.launchDirection droplet).sign *
          speedInMetersPerSecond setup.initialSpeed *
          Real.cos setup.launchAngleRadians * elapsedSeconds time
  verticalPosition : ∀ droplet time,
    setup.positionInMeters droplet time 1 =
      setup.commonLaunchPositionInMeters 1 +
        speedInMetersPerSecond setup.initialSpeed *
          Real.sin setup.launchAngleRadians * elapsedSeconds time -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          elapsedSeconds time ^ 2

/-! ## Requested observable and displayed answer choices -/

/-- Euclidean distance between the two droplet positions, read in metres. -/
def separationInMetersAt
    (setup : SymmetricDropletSetup) (time : ElapsedTimeQuantity) : ℝ :=
  dist (setup.positionInMeters .eastbound time)
    (setup.positionInMeters .westbound time)

/-- Labels of the four multiple-choice expressions. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical coefficient multiplying `v_i * t * cos θ_i` in each choice. -/
def AnswerChoice.coefficient : AnswerChoice → ℝ
  | .A => 1
  | .B => 6
  | .C => 2
  | .D => 4

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The droplets have equal vertical coordinates, while their horizontal
displacements from the common launch point are opposite.  Therefore their
Euclidean separation at any nonnegative elapsed time is twice either
horizontal displacement, namely `2 v_i t cos θ_i` (choice C).

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0691:target`.
-/
theorem problem_phyx_mini_0691
    (setup : SymmetricDropletSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_kinematics : SatisfiesIdealProjectileKinematics setup)
    (time : ElapsedTimeQuantity)
    (h_time_nonnegative : 0 ≤ elapsedSeconds time) :
    separationInMetersAt setup time =
      2 * speedInMetersPerSecond setup.initialSpeed *
        elapsedSeconds time * Real.cos setup.launchAngleRadians := by
  rw [separationInMetersAt, Space.dist_eq, Fin.sum_univ_two]
  simp only [h_kinematics.horizontalPosition, h_kinematics.verticalPosition,
    h_figure.eastboundPointsEast, h_figure.westboundPointsWest,
    HorizontalDirection.sign]
  have hcos : 0 ≤ Real.cos setup.launchAngleRadians :=
    Real.cos_nonneg_of_mem_Icc ⟨by
      linarith [Real.pi_pos.le, h_physical.launchAngleNonnegative],
      h_physical.launchAngleAtMostVertical⟩
  have hfactor :
      0 ≤ 2 * speedInMetersPerSecond setup.initialSpeed *
        elapsedSeconds time * Real.cos setup.launchAngleRadians := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) h_physical.initialSpeedPositive.le)
        h_time_nonnegative)
      hcos
  calc
    _ = √((2 * speedInMetersPerSecond setup.initialSpeed *
        elapsedSeconds time * Real.cos setup.launchAngleRadians) ^ 2) := by
      congr 1
      ring
    _ = _ := Real.sqrt_sq hfactor

end PhyXMiniProblems.ProblemPhyXMini0691
