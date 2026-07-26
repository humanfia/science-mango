import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0062

open Dimension

/-!
# Laser streak from a rotating hexagonal mirror

A horizontal laser is aimed from the right at the center of a regular
hexagonal mirror rotating about that center. During the interval in which one
face intercepts the center ray, its normal turns through `60°`. Specular
reflection doubles that angular sweep, and the two limiting reflected rays
meet the vertical wall behind the laser at the endpoints of the light streak.

All distances and signed wall coordinates are genuine dimensionful lengths.
Their numerical values below are read only after selecting a length unit.
Angles are dimensionless real readouts in radians, measured from the rightward
axis from the mirror center toward the wall.
-/

/-- A physical length or signed one-dimensional displacement. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a dimensionful length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The scalar SI readout of a dimensionful length, in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The scalar centimeter readout of a dimensionful length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The polygonal reflecting element identified in the diagram. -/
inductive MirrorShape where
  | regularHexagon
  deriving DecidableEq, Repr

/-- The axis about which the mirror rotates in the plane of the figure. -/
inductive MirrorRotation where
  | aboutCenter
  deriving DecidableEq, Repr

/-- The target point of the incident laser ray. -/
inductive LaserAim where
  | mirrorCenter
  deriving DecidableEq, Repr

/-- The wall's qualitative placement relative to the laser and mirror. -/
inductive WallPlacement where
  | behindLaserOnIncidentAxis
  deriving DecidableEq, Repr

/-- The two limiting rays produced when the illuminated mirror face changes. -/
inductive SweepEndpoint where
  | lower
  | upper
  deriving DecidableEq, Repr

/-!
The physical quantities and figure labels for the rotating-mirror setup.

The `40 cm` arrow in the image runs between opposite vertices of the regular
hexagon. `mirrorVertexRadius` is retained separately because the limiting ray
is reflected at the right-hand transition vertex. Wall-hit heights are signed
coordinates relative to the laser axis, while `streakLengthOnWall` is the
positive distance between those coordinates.
-/
structure RotatingHexagonalMirrorSetup where
  mirrorShape : MirrorShape
  rotation : MirrorRotation
  laserAim : LaserAim
  wallPlacement : WallPlacement
  mirrorVertexToVertexWidth : LengthQuantity
  mirrorVertexRadius : LengthQuantity
  laserDistanceFromMirrorCenter : LengthQuantity
  wallDistanceFromMirrorCenter : LengthQuantity
  faceNormalAngleRad : SweepEndpoint → ℝ
  reflectedRayAngleRad : SweepEndpoint → ℝ
  wallHitHeight : SweepEndpoint → LengthQuantity
  streakLengthOnWall : LengthQuantity

/-- The categorical arrangement shown by the figure. -/
def HasDepictedOpticalLayout
    (setup : RotatingHexagonalMirrorSetup) : Prop :=
  setup.mirrorShape = .regularHexagon ∧
    setup.rotation = .aboutCenter ∧
    setup.laserAim = .mirrorCenter ∧
    setup.wallPlacement = .behindLaserOnIncidentAxis

/-!
The numerical labels read directly from the image: the mirror's
vertex-to-vertex width is `40 cm`, the center-to-laser distance is `50 cm`,
and the center-to-wall distance is `2.0 m`. No streak length is included.
-/
def MatchesFigureReadouts
    (setup : RotatingHexagonalMirrorSetup) : Prop :=
  lengthInCentimeters setup.mirrorVertexToVertexWidth = 40 ∧
    lengthInCentimeters setup.laserDistanceFromMirrorCenter = 50 ∧
    lengthInMeters setup.wallDistanceFromMirrorCenter = 2.0

/-!
Positivity and axial ordering of the depicted apparatus. In particular, the
laser is outside the mirror and the wall is behind the laser. These physical
conditions do not assign a numerical value to the requested streak.
-/
def HasPhysicalDimensions
    (setup : RotatingHexagonalMirrorSetup) : Prop :=
  0 < lengthInMeters setup.mirrorVertexToVertexWidth ∧
    0 < lengthInMeters setup.mirrorVertexRadius ∧
    lengthInMeters setup.mirrorVertexRadius <
      lengthInMeters setup.laserDistanceFromMirrorCenter ∧
    lengthInMeters setup.laserDistanceFromMirrorCenter <
      lengthInMeters setup.wallDistanceFromMirrorCenter ∧
    0 < lengthInMeters setup.streakLengthOnWall

/-!
Regular-hexagon transition geometry. Opposite vertices are two circumradii
apart. When the incident center ray changes from one face to the next, the
outward face normal has reached `-π/6` or `π/6` from the wall axis.
-/
def SatisfiesRegularHexagonTransitionGeometry
    (setup : RotatingHexagonalMirrorSetup) : Prop :=
  (∀ unit : LengthUnit,
      lengthReadout unit setup.mirrorVertexToVertexWidth =
        2 * lengthReadout unit setup.mirrorVertexRadius) ∧
    setup.faceNormalAngleRad .lower = -(Real.pi / 6) ∧
    setup.faceNormalAngleRad .upper = Real.pi / 6

/-!
Specular reflection for the fixed leftward incident ray. With angles measured
from the rightward wall axis, reflecting across a face whose normal has angle
`α` produces an outgoing ray at angle `2α`.
-/
def SatisfiesLawOfSpecularReflection
    (setup : RotatingHexagonalMirrorSetup) : Prop :=
  ∀ endpoint : SweepEndpoint,
    setup.reflectedRayAngleRad endpoint =
      2 * setup.faceNormalAngleRad endpoint

/-!
Planar ray geometry at the vertical wall. At either transition the reflection
point is the right-hand mirror vertex, so the horizontal run to the wall is
the center-to-wall distance minus the vertex radius. The streak length is the
difference between the upper and lower wall-hit coordinates. Both relations
are stated in every length unit to keep the model unit-covariant.
-/
def SatisfiesWallProjectionGeometry
    (setup : RotatingHexagonalMirrorSetup) : Prop :=
  (∀ (unit : LengthUnit) (endpoint : SweepEndpoint),
      lengthReadout unit (setup.wallHitHeight endpoint) =
        (lengthReadout unit setup.wallDistanceFromMirrorCenter -
            lengthReadout unit setup.mirrorVertexRadius) *
          Real.tan (setup.reflectedRayAngleRad endpoint)) ∧
    ∀ unit : LengthUnit,
      lengthReadout unit setup.streakLengthOnWall =
        lengthReadout unit (setup.wallHitHeight .upper) -
          lengthReadout unit (setup.wallHitHeight .lower)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The streak length in meters printed beside each answer choice. -/
def answerStreakLengthInMeters : AnswerChoice → ℝ
  | .A => 1.4
  | .B => 5.6
  | .C => 6.1
  | .D => 2.4

/-!
A choice is selected when its printed length is at least as close to the exact
physical streak length as every other displayed value. This avoids treating
the rounded answer `6.1 m` as an exact governing-law hypothesis.
-/
def IsNearestDisplayedStreakLength
    (streakLength : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |lengthInMeters streakLength - answerStreakLengthInMeters choice| ≤
      |lengthInMeters streakLength - answerStreakLengthInMeters other|

/-!
Regular-hexagon transition angles together with specular reflection give a
reflected sweep from `-π/3` to `π/3`. This is a derived optical consequence,
not a figure readout.
-/
lemma reflectedSweepEndpointAngles
    (setup : RotatingHexagonalMirrorSetup)
    (h_hexagon : SatisfiesRegularHexagonTransitionGeometry setup)
    (h_reflection : SatisfiesLawOfSpecularReflection setup) :
    setup.reflectedRayAngleRad .lower = -(Real.pi / 3) ∧
      setup.reflectedRayAngleRad .upper = Real.pi / 3 := by
  constructor
  · rw [h_reflection, h_hexagon.2.1]
    ring
  · rw [h_reflection, h_hexagon.2.2]
    ring

/-!
The exact, unrounded streak has twice the upper limiting-ray height. The
horizontal run is the wall distance measured from the right-hand transition
vertex rather than from the mirror center.
-/
lemma streakLength_eq_hexagonSweepFormula
    (setup : RotatingHexagonalMirrorSetup)
    (h_hexagon : SatisfiesRegularHexagonTransitionGeometry setup)
    (h_reflection : SatisfiesLawOfSpecularReflection setup)
    (h_projection : SatisfiesWallProjectionGeometry setup) :
    lengthInMeters setup.streakLengthOnWall =
      2 *
        (lengthInMeters setup.wallDistanceFromMirrorCenter -
          lengthInMeters setup.mirrorVertexRadius) *
        Real.tan (Real.pi / 3) := by
  obtain ⟨h_lower, h_upper⟩ :=
    reflectedSweepEndpointAngles setup h_hexagon h_reflection
  change lengthReadout LengthUnit.meters setup.streakLengthOnWall =
    2 *
      (lengthReadout LengthUnit.meters setup.wallDistanceFromMirrorCenter -
        lengthReadout LengthUnit.meters setup.mirrorVertexRadius) *
      Real.tan (Real.pi / 3)
  rw [h_projection.2 LengthUnit.meters,
    h_projection.1 LengthUnit.meters .upper,
    h_projection.1 LengthUnit.meters .lower,
    h_upper, h_lower, Real.tan_neg]
  ring

/-!
For the depicted `40 cm` regular hexagon and a wall `2.0 m` from its center,
the exact model gives approximately `6.24 m`. Of the displayed measurements,
`6.1 m` is therefore the nearest, namely answer choice C. The `50 cm` laser
distance fixes the depicted ordering but does not alter the reflected angular
sweep or the wall intersection.

This formalizes `thm:physics:phyx_mini_0062:target`.
-/
theorem problem_phyx_mini_0062
    (setup : RotatingHexagonalMirrorSetup)
    (h_layout : HasDepictedOpticalLayout setup)
    (h_readouts : MatchesFigureReadouts setup)
    (h_physical : HasPhysicalDimensions setup)
    (h_hexagon : SatisfiesRegularHexagonTransitionGeometry setup)
    (h_reflection : SatisfiesLawOfSpecularReflection setup)
    (h_projection : SatisfiesWallProjectionGeometry setup) :
    IsNearestDisplayedStreakLength setup.streakLengthOnWall .C := by
  have h_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    change
      (length {UnitChoices.SI with length := LengthUnit.centimeters}).val =
        100 * (length UnitChoices.SI).val
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
          (dim (WithDim L𝓭 ℝ)) = 100 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have h_width_meters :
      lengthInMeters setup.mirrorVertexToVertexWidth = 2 / 5 := by
    have h_width_centimeters := h_readouts.1
    rw [h_centimeters_eq] at h_width_centimeters
    norm_num at h_width_centimeters ⊢
    linarith
  have h_radius_meters :
      lengthInMeters setup.mirrorVertexRadius = 1 / 5 := by
    have h_diameter := h_hexagon.1 LengthUnit.meters
    change lengthInMeters setup.mirrorVertexToVertexWidth =
      2 * lengthInMeters setup.mirrorVertexRadius at h_diameter
    norm_num at h_width_meters ⊢
    linarith
  have h_streak :
      lengthInMeters setup.streakLengthOnWall =
        (18 / 5 : ℝ) * Real.sqrt 3 := by
    rw [streakLength_eq_hexagonSweepFormula setup h_hexagon h_reflection
      h_projection, h_readouts.2.2, h_radius_meters,
      Real.tan_pi_div_three]
    norm_num
  have h_sqrt_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h_streak_ge :
      (61 / 10 : ℝ) ≤ lengthInMeters setup.streakLengthOnWall := by
    rw [h_streak]
    nlinarith
  unfold IsNearestDisplayedStreakLength
  intro other
  cases other with
  | A =>
      simp only [answerStreakLengthInMeters]
      rw [abs_of_nonneg (by norm_num; linarith),
        abs_of_nonneg (by norm_num; linarith)]
      linarith
  | B =>
      simp only [answerStreakLengthInMeters]
      rw [abs_of_nonneg (by norm_num; linarith),
        abs_of_nonneg (by norm_num; linarith)]
      linarith
  | C => exact le_rfl
  | D =>
      simp only [answerStreakLengthInMeters]
      rw [abs_of_nonneg (by norm_num; linarith),
        abs_of_nonneg (by norm_num; linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0062
