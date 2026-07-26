import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Projection
import Physlib.Optics.Basic

noncomputable section

/-!
# Deflection of a horizontal laser beam by a plane mirror

The diagram is modeled in a two-dimensional Euclidean plane.  Angles are
dimensionless real readouts in radians; `degrees` converts the degree labels in
the source figure to those readouts.

The source records choice C (`60°`) for the mirror angle `φ`, but the pictured
ray directions and the law of specular reflection imply `φ = 30°`, choice A.
The recorded answer is retained below as metadata and is kept separate from
the physically supported conclusion.
-/

namespace PhyXMiniProblems.ProblemPhyXMini0060

/-- The Euclidean plane containing the mirror and both laser rays. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Convert a dimensionless angle readout in degrees to radians. -/
noncomputable def degrees (value : ℝ) : ℝ :=
  value * Real.pi / 180

/--
An oriented laser ray.  Its direction is normalized, so the scalar parameter
of `pointAt` has the same length readout as the plane coordinates.
-/
structure LightRay where
  origin : Plane
  direction : Plane
  direction_is_unit : ‖direction‖ = 1

namespace LightRay

/-- The point at the given signed distance along a laser ray. -/
def pointAt (ray : LightRay) (distance : ℝ) : Plane :=
  distance • ray.direction + ray.origin

end LightRay

/--
An ideal plane mirror in the two-dimensional optical diagram.

The named unit tangent points toward the right in the figure and fixes the
acute representative of the mirror's otherwise unoriented surface line.
-/
structure PlaneMirror where
  surface : AffineSubspace ℝ Plane
  surface_nonempty : Nonempty surface
  tangentDirectionTowardRight : Plane
  direction_eq_span_tangent :
    surface.direction = Submodule.span ℝ {tangentDirectionTowardRight}
  tangent_is_unit : ‖tangentDirectionTowardRight‖ = 1

namespace PlaneMirror

/--
Reflect a propagation direction in the affine mirror.  Translating the
direction to the impact point allows direct use of Mathlib's affine reflection.
-/
noncomputable def reflectDirection
    (mirror : PlaneMirror) (impact direction : Plane) : Plane :=
  letI : Nonempty mirror.surface := mirror.surface_nonempty
  EuclideanGeometry.reflection mirror.surface (direction + impact) - impact

end PlaneMirror

/--
The physical objects and labeled angular readouts in the source figure.

`phiRadians` is the angle labeled `φ` between the horizontal reference and the
mirror surface.  It is an angle readout, not a scalar replacement for the
mirror or either laser ray.
-/
structure MirrorDeflectionSetup where
  horizontalDirectionTowardRight : Plane
  horizontal_direction_is_unit : ‖horizontalDirectionTowardRight‖ = 1
  mirror : PlaneMirror
  incidentRay : LightRay
  reflectedRay : LightRay
  impact : Plane
  incidentAngleFromHorizontalRadians : ℝ
  reflectedAngleFromHorizontalRadians : ℝ
  phiRadians : ℝ

/--
The three scalar angle labels agree with Mathlib's undirected angles between
the corresponding nonzero geometric directions.
-/
def HasGeometricAngleReadouts (setup : MirrorDeflectionSetup) : Prop :=
  setup.incidentAngleFromHorizontalRadians =
      InnerProductGeometry.angle
        setup.horizontalDirectionTowardRight setup.incidentRay.direction ∧
    setup.reflectedAngleFromHorizontalRadians =
      InnerProductGeometry.angle
        setup.horizontalDirectionTowardRight setup.reflectedRay.direction ∧
    setup.phiRadians =
      InnerProductGeometry.angle
        setup.horizontalDirectionTowardRight
        setup.mirror.tangentDirectionTowardRight

/--
Figure-derived data: the incoming beam is horizontal and reaches the mirror,
the outgoing beam begins at the impact point, and the marked deflection is
`60°`.  Only the acute range of `φ` is read from the drawing; its requested
numerical value is intentionally absent.
-/
def MatchesFigureReadouts (setup : MirrorDeflectionSetup) : Prop :=
  setup.impact ∈ setup.mirror.surface ∧
    (∃ travelDistance : ℝ,
      0 < travelDistance ∧
        setup.incidentRay.pointAt travelDistance = setup.impact) ∧
    setup.reflectedRay.origin = setup.impact ∧
    setup.incidentRay.direction = setup.horizontalDirectionTowardRight ∧
    setup.incidentAngleFromHorizontalRadians = 0 ∧
    setup.reflectedAngleFromHorizontalRadians = degrees 60 ∧
    0 < setup.phiRadians ∧
    setup.phiRadians < Real.pi / 2

/--
The governing law of specular reflection.

The first conjunct is the geometric reflection of the propagation vector in
the mirror.  The second is its angle-readout form on the pictured branch:
the mirror direction bisects the incident and reflected direction angles.
-/
def ObeysSpecularReflectionLaw (setup : MirrorDeflectionSetup) : Prop :=
  setup.reflectedRay.direction =
      setup.mirror.reflectDirection setup.impact setup.incidentRay.direction ∧
    setup.reflectedAngleFromHorizontalRadians =
      2 * setup.phiRadians - setup.incidentAngleFromHorizontalRadians

/-- Labels of the four answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The radian value printed beside each answer choice. -/
noncomputable def answerAngleRadians : AnswerChoice → ℝ
  | .A => degrees 30
  | .B => degrees 90
  | .C => degrees 60
  | .D => degrees 120

/-- A mirror-angle readout agrees exactly with the selected answer. -/
def MatchesAnswer (phiRadians : ℝ) (choice : AnswerChoice) : Prop :=
  phiRadians = answerAngleRadians choice

/--
The answer label recorded in the supplied dataset metadata, contrary to the
pictured physics.
-/
def recordedDatasetAnswer : AnswerChoice := .C

/--
The physically supported target is that the mirror angle `φ` is `30°`, hence
choice A.  Indeed, the incoming direction has horizontal angle zero, the
outgoing direction has angle `60°`, and the mirror direction bisects those
direction angles under specular reflection.  Neither `30°` nor choice A occurs
in the governing-law or figure-readout premises.

This declaration corresponds to
`thm:physics:phyx_mini_0060:target`.
-/
theorem problem_phyx_mini_0060
    (setup : MirrorDeflectionSetup)
    (hAngles : HasGeometricAngleReadouts setup)
    (hFigure : MatchesFigureReadouts setup)
    (hReflection : ObeysSpecularReflectionLaw setup) :
    setup.phiRadians = degrees 30 ∧
      MatchesAnswer setup.phiRadians .A := by
  rcases hFigure with ⟨_, _, _, _, hIncident, hReflected, _, _⟩
  rcases hReflection with ⟨_, hReflectionAngle⟩
  rw [hReflected, hIncident] at hReflectionAngle
  have hPhi : setup.phiRadians = degrees 30 := by
    norm_num [degrees] at hReflectionAngle ⊢
    linarith
  exact ⟨hPhi, hPhi⟩

end PhyXMiniProblems.ProblemPhyXMini0060
