import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0692

open Dimension

/-!
# Total acceleration of a pendulum at its horizontal positions

A pendulum of cord length `1.00 m` has speed `5.00 m/s` at the two
horizontal positions labelled `theta = 90 degrees` and `theta = 270 degrees`.
The supplied image decomposes the planar acceleration into radial and
tangential components, labels gravity as downward, and labels the angle `phi`
between the total and radial acceleration vectors.

Physical lengths, speeds, positions, and accelerations below are coherent
`Dimensionful` quantities.  Real numbers are used only after choosing a unit
system, for dimensionless angle readouts, and for the displayed answer values.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The two-dimensional vertical plane in which the pendulum swings. -/
abbrev PendulumPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- A unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent physical speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A unit-independent point or displacement vector in the pendulum plane. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 PendulumPlane)

/-- A unit-independent acceleration vector in the pendulum plane. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension PendulumPlane)

/-- Scalar readout of a physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  (length units).val

/-- Scalar readout of a physical speed in a coherent choice of units. -/
def speedReadout (units : UnitChoices) (speed : SpeedQuantity) : ℝ :=
  (speed units).val

/-- Planar readout of a physical position in a coherent choice of units. -/
def positionVectorReadout
    (units : UnitChoices) (position : PlanarPositionQuantity) : PendulumPlane :=
  (position units).val

/-- Planar readout of an acceleration vector in coherent acceleration units. -/
def accelerationVectorReadout
    (units : UnitChoices)
    (acceleration : PlanarAccelerationQuantity) : PendulumPlane :=
  (acceleration units).val

/-- Magnitude readout of a physical acceleration vector. -/
def accelerationMagnitudeReadout
    (units : UnitChoices)
    (acceleration : PlanarAccelerationQuantity) : ℝ :=
  ‖accelerationVectorReadout units acceleration‖

/-- Length readout in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- Speed readout in SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout UnitChoices.SI speed

/-- Acceleration-magnitude readout in SI metres per second squared. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) : ℝ :=
  accelerationMagnitudeReadout UnitChoices.SI acceleration

/-! ## Positions, figure labels, and physical setup -/

/-- The two horizontal positions named in the problem. -/
inductive HorizontalPosition where
  | theta90
  | theta270
  deriving DecidableEq, Fintype, Repr

/-- The directed degree label attached to each horizontal position. -/
def HorizontalPosition.thetaDegrees : HorizontalPosition → ℝ
  | .theta90 => 90
  | .theta270 => 270

/-- Geometric objects and vector labels visible in the supplied bitmap. -/
inductive FigureElement where
  | fixedPivot
  | pendulumCord
  | pendulumBob
  | dashedVerticalReference
  | dashedCircularArc
  | thetaAngleArc
  | totalAccelerationArrow
  | radialAccelerationArrow
  | tangentialAccelerationArrow
  | gravityArrow
  | phiAngleArc
  deriving DecidableEq, Fintype, Repr

/-- Presentation-level visibility data transcribed from the primary image. -/
structure PendulumFigure where
  isShown : FigureElement → Bool

/--
The kinematic state at one horizontal position.

The fields correspond to the image labels `theta`, `a`, `a_r`, `a_t`, `g`,
and `phi`.  In particular, the total acceleration remains an independent
physical vector; no numerical answer is stored in this structure.
-/
structure HorizontalPendulumState where
  thetaDegrees : ℝ
  bobPosition : PlanarPositionQuantity
  speed : SpeedQuantity
  totalAcceleration : PlanarAccelerationQuantity
  radialAcceleration : PlanarAccelerationQuantity
  tangentialAcceleration : PlanarAccelerationQuantity
  gravitationalAcceleration : PlanarAccelerationQuantity
  phiRadians : ℝ

/-- The fixed geometry, length, two horizontal states, and supplied figure. -/
structure PendulumSetup where
  pivotPosition : PlanarPositionQuantity
  cordLength : LengthQuantity
  downwardDirection : PendulumPlane
  state : HorizontalPosition → HorizontalPendulumState
  figure : PendulumFigure

/-! ## Stated data and primary-figure readouts -/

/--
The numerical data stated in the prose: `r = 1.00 m`, both horizontal speeds
are `5.00 m/s`, and the two directed position labels are `90` and `270`
degrees.  No total-acceleration value occurs here.
-/
structure MatchesProblemStatement (setup : PendulumSetup) : Prop where
  cordLengthMeters : lengthInMeters setup.cordLength = 1
  horizontalSpeedMetersPerSecond :
    ∀ position,
      speedInMetersPerSecond (setup.state position).speed = 5
  directedThetaLabel :
    ∀ position,
      (setup.state position).thetaDegrees = position.thetaDegrees

/--
The standard terrestrial-gravity calibration implicit in the numerical
multiple-choice problem.  This supplies `9.80 m/s²`, not the requested total
acceleration.
-/
structure UsesStandardTerrestrialGravity (setup : PendulumSetup) : Prop where
  gravityMagnitudeMetersPerSecondSquared :
    ∀ position,
      accelerationMagnitudeInMetersPerSecondSquared
          (setup.state position).gravitationalAcceleration = 9.8

/-- Positivity and normalization conditions for the nondegenerate setup. -/
structure HasPhysicalPendulumParameters (setup : PendulumSetup) : Prop where
  cordLengthPositive : 0 < lengthInMeters setup.cordLength
  horizontalSpeedPositive :
    ∀ position, 0 < speedInMetersPerSecond (setup.state position).speed
  gravityMagnitudePositive :
    ∀ position,
      0 < accelerationMagnitudeInMetersPerSecondSquared
        (setup.state position).gravitationalAcceleration
  downwardDirectionIsUnit : ‖setup.downwardDirection‖ = 1

/--
Geometry read from the image: every named element is present, the bob is one
cord length from the pivot, `a_r` points toward the pivot, `a_r` and `a_t` are
perpendicular, `g` points downward, and `phi` is the angle from `a_r` to `a`.
These are geometric readouts, not a numerical total-acceleration answer.
-/
structure MatchesSuppliedFigure (setup : PendulumSetup) : Prop where
  everyNamedElementShown :
    ∀ element, setup.figure.isShown element = true
  bobAtCordRadius :
    ∀ position units,
      ‖positionVectorReadout units setup.pivotPosition -
          positionVectorReadout units (setup.state position).bobPosition‖ =
        lengthReadout units setup.cordLength
  radialPointsTowardPivot :
    ∀ position units,
      SameRay ℝ
        (accelerationVectorReadout units
          (setup.state position).radialAcceleration)
        (positionVectorReadout units setup.pivotPosition -
          positionVectorReadout units (setup.state position).bobPosition)
  radialTangentialPerpendicular :
    ∀ position units,
      inner ℝ
        (accelerationVectorReadout units
          (setup.state position).radialAcceleration)
        (accelerationVectorReadout units
          (setup.state position).tangentialAcceleration) = 0
  gravityPointsDownward :
    ∀ position units,
      SameRay ℝ
        (accelerationVectorReadout units
          (setup.state position).gravitationalAcceleration)
        setup.downwardDirection
  phiLabelsAngleFromRadialToTotal :
    ∀ position units,
      (setup.state position).phiRadians =
        InnerProductGeometry.angle
          (accelerationVectorReadout units
            (setup.state position).radialAcceleration)
          (accelerationVectorReadout units
            (setup.state position).totalAcceleration)

/-! ## Governing pendulum kinematics -/

/--
The physical laws used at either horizontal position:

* total acceleration is the vector sum `a = a_r + a_t`;
* circular-motion radial acceleration has magnitude `v²/r`;
* at a horizontal position gravity is wholly tangential.

The orthogonality of the displayed radial and tangential arrows is retained
separately in `MatchesSuppliedFigure`.  None of these laws states the requested
total magnitude or an answer choice.
-/
structure SatisfiesHorizontalPendulumLaws (setup : PendulumSetup) : Prop where
  totalAccelerationDecomposition :
    ∀ position units,
      accelerationVectorReadout units
          (setup.state position).totalAcceleration =
        accelerationVectorReadout units
            (setup.state position).radialAcceleration +
          accelerationVectorReadout units
            (setup.state position).tangentialAcceleration
  radialAccelerationMagnitude :
    ∀ position units,
      accelerationMagnitudeReadout units
          (setup.state position).radialAcceleration =
        speedReadout units (setup.state position).speed ^ 2 /
          lengthReadout units setup.cordLength
  gravityIsTangentialAtHorizontalPosition :
    ∀ position units,
      accelerationVectorReadout units
          (setup.state position).tangentialAcceleration =
        accelerationVectorReadout units
          (setup.state position).gravitationalAcceleration

/-!
Pythagorean composition of the radial and tangential acceleration components.
This generic lemma leaves the problem-specific numerical substitutions to the
main theorem.
-/
lemma totalAccelerationMagnitudeFormula
    (setup : PendulumSetup)
    (_physical : HasPhysicalPendulumParameters setup)
    (_figure : MatchesSuppliedFigure setup)
    (_laws : SatisfiesHorizontalPendulumLaws setup)
    (position : HorizontalPosition)
    (units : UnitChoices) :
    accelerationMagnitudeReadout units
        (setup.state position).totalAcceleration =
      Real.sqrt
        ((speedReadout units (setup.state position).speed ^ 2 /
              lengthReadout units setup.cordLength) ^ 2 +
          accelerationMagnitudeReadout units
              (setup.state position).gravitationalAcceleration ^ 2) := by
  calc
    accelerationMagnitudeReadout units
          (setup.state position).totalAcceleration =
        ‖accelerationVectorReadout units
            (setup.state position).radialAcceleration +
          accelerationVectorReadout units
            (setup.state position).tangentialAcceleration‖ := by
      rw [accelerationMagnitudeReadout,
        _laws.totalAccelerationDecomposition position units]
    _ = Real.sqrt
          (accelerationMagnitudeReadout units
                (setup.state position).radialAcceleration ^ 2 +
            accelerationMagnitudeReadout units
                (setup.state position).tangentialAcceleration ^ 2) := by
      simpa [accelerationMagnitudeReadout, pow_two] using
        (norm_add_eq_sqrt_iff_real_inner_eq_zero).2
          (_figure.radialTangentialPerpendicular position units)
    _ = Real.sqrt
          ((speedReadout units (setup.state position).speed ^ 2 /
                lengthReadout units setup.cordLength) ^ 2 +
            accelerationMagnitudeReadout units
                (setup.state position).gravitationalAcceleration ^ 2) := by
      rw [_laws.radialAccelerationMagnitude position units]
      simp only [accelerationMagnitudeReadout]
      rw [_laws.gravityIsTangentialAtHorizontalPosition position units]

/-! ## Displayed choices and final target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed acceleration-magnitude values, in metres per second squared. -/
def answerMagnitudeInMetersPerSecondSquared : AnswerChoice → ℝ
  | .A => 14.5
  | .B => 12.8
  | .C => 26.8
  | .D => 21.1

/-- A choice is the unique displayed value closest to an exact SI magnitude. -/
def IsClosestDisplayedAnswer
    (exactMagnitude : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |exactMagnitude - answerMagnitudeInMetersPerSecondSquared choice| <
      |exactMagnitude - answerMagnitudeInMetersPerSecondSquared other|

/-!
At each of the two horizontal positions, the total acceleration magnitude is
the Pythagorean combination of `25 m/s²` radial and `9.8 m/s²` tangential
acceleration.  Its exact square-root value makes choice C (`26.8 m/s²`) the
unique closest displayed answer.

Blueprint label: `thm:physics:phyx_mini_0692:target`.
-/
theorem totalAccelerationAtHorizontalPositions
    (setup : PendulumSetup)
    (_problem : MatchesProblemStatement setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalPendulumParameters setup)
    (_figure : MatchesSuppliedFigure setup)
    (_laws : SatisfiesHorizontalPendulumLaws setup) :
    ∀ position : HorizontalPosition,
      accelerationMagnitudeInMetersPerSecondSquared
          (setup.state position).totalAcceleration =
          Real.sqrt
            ((((5 : ℝ) ^ 2 / 1) ^ 2) + (9.8 : ℝ) ^ 2) ∧
        IsClosestDisplayedAnswer
          (accelerationMagnitudeInMetersPerSecondSquared
            (setup.state position).totalAcceleration)
          .C := by
  intro position
  have hFormula :=
    totalAccelerationMagnitudeFormula setup _physical _figure _laws
      position UnitChoices.SI
  have hSpeed :
      speedReadout UnitChoices.SI (setup.state position).speed = 5 :=
    _problem.horizontalSpeedMetersPerSecond position
  have hLength : lengthReadout UnitChoices.SI setup.cordLength = 1 :=
    _problem.cordLengthMeters
  have hGravity :
      accelerationMagnitudeReadout UnitChoices.SI
          (setup.state position).gravitationalAcceleration = 9.8 :=
    _gravity.gravityMagnitudeMetersPerSecondSquared position
  have hExact :
      accelerationMagnitudeInMetersPerSecondSquared
          (setup.state position).totalAcceleration =
        Real.sqrt ((((5 : ℝ) ^ 2 / 1) ^ 2) + (9.8 : ℝ) ^ 2) :=
    hFormula.trans (by rw [hSpeed, hLength, hGravity])
  have hLower : (26.8 : ℝ) <
      Real.sqrt ((((5 : ℝ) ^ 2 / 1) ^ 2) + (9.8 : ℝ) ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  refine ⟨hExact, ?_⟩
  rw [hExact]
  unfold IsClosestDisplayedAnswer
  intro other hne
  cases other with
  | A =>
      simp only [answerMagnitudeInMetersPerSecondSquared]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      norm_num
  | B =>
      simp only [answerMagnitudeInMetersPerSecondSquared]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      norm_num
  | C => exact (hne rfl).elim
  | D =>
      simp only [answerMagnitudeInMetersPerSecondSquared]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0692
