import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Basic

/-!
# PhyX mini problem 0025: speed of a laser spot from a rotating mirror

A fixed laser enters a square room through the midpoint of the south wall and
strikes a mirror at the room center.  The mirror rotates about the vertical
axis with positive angular speed `ω`.  Its reflected ray meets the walls and
produces a moving spot.  The primary image labels the room side by `L`, the
east-wall midpoint by `O`, and the spot's distance above `O` by `x`.

Lengths, times, angular speeds, and linear speeds are represented by PhysLean
dimensionful quantities.  Ray directions use Mathlib's positive-scaling
quotient `Module.Ray`.  Angles below are unwrapped real radian readouts on the
single east-wall sweep from `O` to the northeast corner.
-/

namespace PhyXMiniProblems.ProblemPhyXMini0025

noncomputable section

open Dimension

/-! ## Dimensioned quantities and labelled floor geometry -/

/-- The horizontal plane of the overhead room diagram. -/
abbrev FloorPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- A physical length, independent of a choice of units. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time coordinate or time interval. -/
abbrev DimTime : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A positive-or-negative angular-speed readout, with radians dimensionless. -/
abbrev DimAngularSpeed : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical linear speed along a wall. -/
abbrev DimLinearSpeed : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A point in the floor plane whose coordinates carry length dimension. -/
abbrev FloorPoint : Type := Dimensionful (WithDim L𝓭 FloorPlane)

/-- A direction of propagation, modulo multiplication by a positive scalar. -/
abbrev BeamDirection : Type := Module.Ray ℝ FloorPlane

/-- The four walls of the square, named in the orientation of the primary image. -/
inductive WallLabel where
  | north
  | east
  | south
  | west
  deriving DecidableEq, Repr

/-- A directed geometrical-optics ray with a dimensioned point of origin. -/
structure DirectedBeam where
  origin : FloorPoint
  direction : BeamDirection

/-- A dimensioned point is on the forward half-ray of a directed beam. -/
def PointOnBeam (beam : DirectedBeam) (point : FloorPoint) : Prop :=
  ∀ units : UnitChoices,
    ∃ rayParameter : ℝ,
      0 ≤ rayParameter ∧
        (point units).val =
          (beam.origin units).val + rayParameter • beam.direction.someVector

/--
The square-room data and the labels used by the image.  The predicate
`onWall` and the east-wall offset are physical incidence/readout interfaces;
their metric properties are stated separately in `MatchesSquareRoomFigure`.
-/
structure SquareRoomFigure where
  sideLength : DimLength
  center : FloorPoint
  southWallMidpoint : FloorPoint
  eastWallMidpointO : FloorPoint
  northEastCorner : FloorPoint
  onWall : WallLabel → FloorPoint → Prop
  eastWallOffsetFromO : FloorPoint → DimLength

/--
Metric and incidence facts read from the square figure.  In particular, `O`
is the midpoint of the east wall and its separation from both the center and
the northeast corner is `L / 2`.
-/
structure MatchesSquareRoomFigure (room : SquareRoomFigure) : Prop where
  sideLengthPositive :
    ∀ units : UnitChoices, 0 < (room.sideLength units).val
  southMidpointOnSouthWall :
    room.onWall .south room.southWallMidpoint
  OOnEastWall : room.onWall .east room.eastWallMidpointO
  northEastCornerOnEastWall : room.onWall .east room.northEastCorner
  northEastCornerOnNorthWall : room.onWall .north room.northEastCorner
  centerToOIsHalfSide :
    ∀ units : UnitChoices,
      dist (room.center units).val (room.eastWallMidpointO units).val =
        (room.sideLength units).val / 2
  OToNorthEastCornerIsHalfSide :
    ∀ units : UnitChoices,
      dist (room.eastWallMidpointO units).val
          (room.northEastCorner units).val =
        (room.sideLength units).val / 2
  offsetAtO :
    ∀ units : UnitChoices,
      (room.eastWallOffsetFromO room.eastWallMidpointO units).val = 0
  offsetAtNorthEastCorner :
    ∀ units : UnitChoices,
      (room.eastWallOffsetFromO room.northEastCorner units).val =
        (room.sideLength units).val / 2

/-! ## The rotating-mirror experiment and its laws -/

/--
Time-dependent quantities in the experiment.  `reflectedAngleFromEastNormal`
is an unwrapped radian angle: it is zero along the ray from the center to `O`
and increases toward the northeast corner.  `spotSpeed` is the nonnegative
linear speed of the spot along the wall currently struck.
-/
structure RotatingMirrorExperiment where
  room : SquareRoomFigure
  mirrorPosition : FloorPoint
  incomingBeam : DirectedBeam
  mirrorOrientation : DimTime → ℝ
  angularSpeed : DimAngularSpeed
  reflectedBeam : DimTime → DirectedBeam
  reflectedAngleFromEastNormal : DimTime → ℝ
  spotPosition : DimTime → FloorPoint
  spotSpeed : DimTime → DimLinearSpeed

/-- Primary-image incidence data, kept separate from the governing laws. -/
structure MatchesRotatingMirrorFigure
    (experiment : RotatingMirrorExperiment) : Prop where
  roomFigure : MatchesSquareRoomFigure experiment.room
  mirrorAtRoomCenter :
    experiment.mirrorPosition = experiment.room.center
  incomingBeamStartsAtSouthMidpoint :
    experiment.incomingBeam.origin = experiment.room.southWallMidpoint
  incomingBeamStrikesMirror :
    PointOnBeam experiment.incomingBeam experiment.mirrorPosition
  reflectedBeamStartsAtMirror :
    ∀ t : DimTime,
      (experiment.reflectedBeam t).origin = experiment.mirrorPosition
  reflectedBeamStrikesSpot :
    ∀ t : DimTime,
      PointOnBeam (experiment.reflectedBeam t) (experiment.spotPosition t)

/-- Positivity assumptions selecting the counterclockwise physical branch. -/
structure HasPhysicalParameters
    (experiment : RotatingMirrorExperiment) : Prop where
  angularSpeedPositive :
    ∀ units : UnitChoices, 0 < (experiment.angularSpeed units).val

/--
The physical laws used in the model.

* the mirror angle advances at constant angular speed;
* specular reflection makes the outgoing-ray angle advance through twice the
  mirror's angle because the incident beam is fixed;
* while the spot is on the east wall, central-ray geometry gives
  `x = (L/2) tan φ`;
* differentiating that relation together with `φ' = 2ω` gives
  `v = L ω / cos² φ`.

None of these fields states the requested elapsed-time formula.
-/
structure RotatingMirrorOpticsLaws
    (experiment : RotatingMirrorExperiment) : Prop where
  constantAngularSpeed :
    ∀ (units : UnitChoices) (t₁ t₂ : DimTime),
      experiment.mirrorOrientation t₂ - experiment.mirrorOrientation t₁ =
        (experiment.angularSpeed units).val *
          ((t₂ units).val - (t₁ units).val)
  specularReflectionAngleChange :
    ∀ t₁ t₂ : DimTime,
      experiment.reflectedAngleFromEastNormal t₂ -
          experiment.reflectedAngleFromEastNormal t₁ =
        2 * (experiment.mirrorOrientation t₂ -
          experiment.mirrorOrientation t₁)
  spotOnReflectedBeam :
    ∀ t : DimTime,
      PointOnBeam (experiment.reflectedBeam t) (experiment.spotPosition t)
  eastWallIntersectionGeometry :
    ∀ (units : UnitChoices) (t : DimTime),
      experiment.room.onWall .east (experiment.spotPosition t) →
        (experiment.room.eastWallOffsetFromO
            (experiment.spotPosition t) units).val =
          (experiment.room.sideLength units).val / 2 *
            Real.tan (experiment.reflectedAngleFromEastNormal t)
  eastWallSpotSpeed :
    ∀ (units : UnitChoices) (t : DimTime),
      experiment.room.onWall .east (experiment.spotPosition t) →
        (experiment.spotSpeed t units).val =
          (experiment.room.sideLength units).val *
            (experiment.angularSpeed units).val /
              Real.cos (experiment.reflectedAngleFromEastNormal t) ^ 2

/-! ## The minimum-to-maximum sweep and target -/

/-- Membership in a closed physical time interval, expressed in SI seconds. -/
def InClosedTimeInterval (startTime endTime time : DimTime) : Prop :=
  (startTime UnitChoices.SI).val ≤ (time UnitChoices.SI).val ∧
    (time UnitChoices.SI).val ≤ (endTime UnitChoices.SI).val

/--
The particular east-wall pass shown in the image: the spot moves from `O` to
the northeast corner without leaving the east wall, and its unwrapped
outgoing-ray angle remains on the first-quadrant branch.
-/
structure IsEastWallSweepFromOToCorner
    (experiment : RotatingMirrorExperiment)
    (startTime endTime : DimTime) : Prop where
  ordered :
    (startTime UnitChoices.SI).val ≤ (endTime UnitChoices.SI).val
  startsAtO :
    experiment.spotPosition startTime = experiment.room.eastWallMidpointO
  endsAtNorthEastCorner :
    experiment.spotPosition endTime = experiment.room.northEastCorner
  remainsOnEastWall :
    ∀ t : DimTime,
      InClosedTimeInterval startTime endTime t →
        experiment.room.onWall .east (experiment.spotPosition t)
  reflectedAngleRange :
    ∀ t : DimTime,
      InClosedTimeInterval startTime endTime t →
        0 ≤ experiment.reflectedAngleFromEastNormal t ∧
          experiment.reflectedAngleFromEastNormal t ≤ Real.pi / 4

/-- A time realizes the minimum spot speed on the selected wall sweep. -/
def IsMinimumSpotSpeedOn
    (experiment : RotatingMirrorExperiment)
    (startTime endTime minimumTime : DimTime) : Prop :=
  InClosedTimeInterval startTime endTime minimumTime ∧
    ∀ (units : UnitChoices) (t : DimTime),
      InClosedTimeInterval startTime endTime t →
        (experiment.spotSpeed minimumTime units).val ≤
          (experiment.spotSpeed t units).val

/-- A time realizes the maximum spot speed on the selected wall sweep. -/
def IsMaximumSpotSpeedOn
    (experiment : RotatingMirrorExperiment)
    (startTime endTime maximumTime : DimTime) : Prop :=
  InClosedTimeInterval startTime endTime maximumTime ∧
    ∀ (units : UnitChoices) (t : DimTime),
      InClosedTimeInterval startTime endTime t →
        (experiment.spotSpeed t units).val ≤
          (experiment.spotSpeed maximumTime units).val

/--
On the depicted east-wall pass, the spot has minimum speed at `O`, maximum
speed at the northeast corner, and the elapsed time between those extrema is
`π / (8ω)`.

Blueprint label: `thm:physics:phyx_mini_0025:target`.
-/
theorem spotMinimumToMaximumSpeedInterval
    (experiment : RotatingMirrorExperiment)
    (hFigure : MatchesRotatingMirrorFigure experiment)
    (hParameters : HasPhysicalParameters experiment)
    (hLaws : RotatingMirrorOpticsLaws experiment)
    (startTime endTime : DimTime)
    (hSweep : IsEastWallSweepFromOToCorner experiment startTime endTime) :
    IsMinimumSpotSpeedOn experiment startTime endTime startTime ∧
      IsMaximumSpotSpeedOn experiment startTime endTime endTime ∧
      ∀ units : UnitChoices,
        (endTime units).val - (startTime units).val =
          Real.pi / (8 * (experiment.angularSpeed units).val) := by
  have hStartInInterval :
      InClosedTimeInterval startTime endTime startTime := by
    exact ⟨le_rfl, hSweep.ordered⟩
  have hEndInInterval :
      InClosedTimeInterval startTime endTime endTime := by
    exact ⟨hSweep.ordered, le_rfl⟩
  have hStartOnEastWall :
      experiment.room.onWall .east (experiment.spotPosition startTime) := by
    rw [hSweep.startsAtO]
    exact hFigure.roomFigure.OOnEastWall
  have hEndOnEastWall :
      experiment.room.onWall .east (experiment.spotPosition endTime) := by
    rw [hSweep.endsAtNorthEastCorner]
    exact hFigure.roomFigure.northEastCornerOnEastWall
  have hStartAngleRange :=
    hSweep.reflectedAngleRange startTime hStartInInterval
  have hEndAngleRange :=
    hSweep.reflectedAngleRange endTime hEndInInterval
  have hSideLengthSI :=
    hFigure.roomFigure.sideLengthPositive UnitChoices.SI
  have hStartGeometry :=
    hLaws.eastWallIntersectionGeometry UnitChoices.SI startTime
      hStartOnEastWall
  rw [hSweep.startsAtO, hFigure.roomFigure.offsetAtO] at hStartGeometry
  have hHalfSideSI :
      (experiment.room.sideLength UnitChoices.SI).val / 2 ≠ 0 := by
    positivity
  have hStartTan :
      Real.tan (experiment.reflectedAngleFromEastNormal startTime) = 0 := by
    apply (mul_left_cancel₀ hHalfSideSI)
    simpa using hStartGeometry.symm
  have hStartAngle :
      experiment.reflectedAngleFromEastNormal startTime = 0 := by
    apply Real.tan_inj_of_lt_of_lt_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · simpa using hStartTan
  have hEndGeometry :=
    hLaws.eastWallIntersectionGeometry UnitChoices.SI endTime
      hEndOnEastWall
  rw [hSweep.endsAtNorthEastCorner,
    hFigure.roomFigure.offsetAtNorthEastCorner] at hEndGeometry
  have hEndTan :
      Real.tan (experiment.reflectedAngleFromEastNormal endTime) = 1 := by
    apply (mul_left_cancel₀ hHalfSideSI)
    simpa using hEndGeometry.symm
  have hEndAngle :
      experiment.reflectedAngleFromEastNormal endTime = Real.pi / 4 := by
    apply Real.tan_inj_of_lt_of_lt_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · simpa using hEndTan
  constructor
  · refine ⟨hStartInInterval, ?_⟩
    intro units t ht
    have hRange := hSweep.reflectedAngleRange t ht
    have hOnEastWall := hSweep.remainsOnEastWall t ht
    have hSideLength :=
      hFigure.roomFigure.sideLengthPositive units
    have hAngularSpeed :=
      hParameters.angularSpeedPositive units
    have hNumeratorPositive :
        0 < (experiment.room.sideLength units).val *
          (experiment.angularSpeed units).val :=
      mul_pos hSideLength hAngularSpeed
    have hCosPositive :
        0 < Real.cos (experiment.reflectedAngleFromEastNormal t) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos]
    have hCosSquarePositive :
        0 < Real.cos (experiment.reflectedAngleFromEastNormal t) ^ 2 :=
      pow_pos hCosPositive 2
    have hCosLeOne :
        Real.cos (experiment.reflectedAngleFromEastNormal t) ≤ 1 :=
      Real.cos_le_one _
    have hCosSquareLeOne :
        Real.cos (experiment.reflectedAngleFromEastNormal t) ^ 2 ≤ 1 := by
      nlinarith
    rw [hLaws.eastWallSpotSpeed units startTime hStartOnEastWall,
      hLaws.eastWallSpotSpeed units t hOnEastWall, hStartAngle]
    simp only [Real.cos_zero, one_pow, div_one]
    rw [le_div_iff₀ hCosSquarePositive]
    nlinarith
  · constructor
    · refine ⟨hEndInInterval, ?_⟩
      intro units t ht
      have hRange := hSweep.reflectedAngleRange t ht
      have hOnEastWall := hSweep.remainsOnEastWall t ht
      have hSideLength :=
        hFigure.roomFigure.sideLengthPositive units
      have hAngularSpeed :=
        hParameters.angularSpeedPositive units
      have hNumeratorPositive :
          0 < (experiment.room.sideLength units).val *
            (experiment.angularSpeed units).val :=
        mul_pos hSideLength hAngularSpeed
      have hCosPositive :
          0 < Real.cos (experiment.reflectedAngleFromEastNormal t) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith [Real.pi_pos]
      have hCosEndPositive : 0 < Real.cos (Real.pi / 4) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith [Real.pi_pos]
      have hCosSquarePositive :
          0 < Real.cos (experiment.reflectedAngleFromEastNormal t) ^ 2 :=
        pow_pos hCosPositive 2
      have hCosEndSquarePositive :
          0 < Real.cos (Real.pi / 4) ^ 2 :=
        pow_pos hCosEndPositive 2
      have hCosEndLe :
          Real.cos (Real.pi / 4) ≤
            Real.cos (experiment.reflectedAngleFromEastNormal t) := by
        exact Real.cos_le_cos_of_nonneg_of_le_pi hRange.1
          (by linarith [Real.pi_pos]) hRange.2
      have hCosEndSquareLe :
          Real.cos (Real.pi / 4) ^ 2 ≤
            Real.cos (experiment.reflectedAngleFromEastNormal t) ^ 2 := by
        nlinarith
      rw [hLaws.eastWallSpotSpeed units t hOnEastWall,
        hLaws.eastWallSpotSpeed units endTime hEndOnEastWall, hEndAngle]
      rw [div_le_div_iff₀ hCosSquarePositive hCosEndSquarePositive]
      nlinarith
    · intro units
      have hAngularSpeed :=
        hParameters.angularSpeedPositive units
      have hMirrorAngleChange :=
        hLaws.constantAngularSpeed units startTime endTime
      have hReflectedAngleChange :=
        hLaws.specularReflectionAngleChange startTime endTime
      rw [hStartAngle, hEndAngle, hMirrorAngleChange] at hReflectedAngleChange
      field_simp [ne_of_gt hAngularSpeed]
      nlinarith

end

end PhyXMiniProblems.ProblemPhyXMini0025
