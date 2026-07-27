import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

namespace IPhO2026Problems
namespace IPhO2026_2_C_1

noncomputable section

open Dimension

/-- A unit-independent physical length, grounded by Physlib's length
dimension. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- The numerical projection of a physical length into SI metres. -/
def lengthInMetres (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- A point in the Cartesian cross-section of Figure 2g.
Both coordinates are unit-independent Physlib length quantities. -/
structure PlanePoint where
  x : LengthQuantity
  y : LengthQuantity

/-- A dimensionless propagation direction in the Cartesian cross-section. -/
structure PlaneDirection where
  dx : ℝ
  dy : ℝ

namespace PlaneDirection

/-- The coordinate dot product on directions in the plane. -/
def dot (u v : PlaneDirection) : ℝ :=
  u.dx * v.dx + u.dy * v.dy

/-- A direction is nonzero when at least one Cartesian component is nonzero. -/
def IsNonzero (d : PlaneDirection) : Prop :=
  d.dx ≠ 0 ∨ d.dy ≠ 0

/-- The normal used in the reflection formula has unit Euclidean length. -/
def IsUnit (d : PlaneDirection) : Prop :=
  dot d d = 1

/-- Reflection of a propagation direction from a surface with a unit outward
normal.  For an incoming direction `d` and normal `n`, this is
`d - 2 (d ⬝ n) n`. -/
def reflectedByNormal (incoming normal : PlaneDirection) : PlaneDirection where
  dx := incoming.dx - 2 * dot incoming normal * normal.dx
  dy := incoming.dy - 2 * dot incoming normal * normal.dy

/-- The specular-reflection law at a mirror point, expressed as a constraining
vector equation rather than as the requested slope/intercept formula. -/
def IsSpecularReflection
    (incoming normal outgoing : PlaneDirection) : Prop :=
  normal.IsUnit ∧ outgoing = reflectedByNormal incoming normal

end PlaneDirection

/-- The upper semicircular cross-section of a half-cylindrical mirror.
`radius` is a positive unit-independent Physlib length quantity. -/
structure HalfCylindricalMirror where
  radius : LengthQuantity
  radius_pos : 0 < lengthInMetres radius

namespace HalfCylindricalMirror

/-- Membership in the reflecting upper semicircle in Figure 2g, expressed in
the common SI-length projection used for analytic geometry. -/
def OnReflectingSurface (mirror : HalfCylindricalMirror) (point : PlanePoint) : Prop :=
  lengthInMetres point.x ^ 2 + lengthInMetres point.y ^ 2 =
      lengthInMetres mirror.radius ^ 2 ∧
    0 ≤ lengthInMetres point.y

end HalfCylindricalMirror

/-- A line in the Figure 2g convention `y = slope * x + intercept`.
The slope is dimensionless and the intercept is a unit-independent Physlib
length quantity. -/
structure SlopeInterceptLine where
  slope : ℝ
  intercept : LengthQuantity

namespace SlopeInterceptLine

/-- A point lies on a slope-intercept line.  The coordinate equation is
evaluated in SI metres. -/
def Contains (line : SlopeInterceptLine) (point : PlanePoint) : Prop :=
  lengthInMetres point.y =
    line.slope * lengthInMetres point.x + lengthInMetres line.intercept

/-- A nonvertical line has `direction` as a supporting direction.
This equation keeps the orientation-free line geometry separate from the
oriented propagation direction of an optical ray. -/
def HasDirection (line : SlopeInterceptLine) (direction : PlaneDirection) : Prop :=
  direction.dy = line.slope * direction.dx

end SlopeInterceptLine

/-- An oriented optical ray together with a marked point on its path. -/
structure OpticalRayAtPoint where
  markedPoint : PlanePoint
  propagationDirection : PlaneDirection
  direction_nonzero : propagationDirection.IsNonzero

/-- The physical and figure-derived data for one ray striking the mirror at
incidence angle `incidenceAngle`.  Angles are measured in radians.

The line coefficients remain unconstrained except through the hit-point,
direction, and specular-reflection equations; in particular, neither requested
closed form is assumed here. -/
structure Figure2gRayInteraction
    (mirror : HalfCylindricalMirror) (incidenceAngle : ℝ) where
  incidenceAngle_pos : 0 < incidenceAngle
  incidenceAngle_lt_pi_div_two : incidenceAngle < Real.pi / 2
  hitPoint : PlanePoint
  incidentRay : OpticalRayAtPoint
  reflectedRay : OpticalRayAtPoint
  outwardNormal : PlaneDirection
  reflectedLine : SlopeInterceptLine
  incident_marked_at_hit : incidentRay.markedPoint = hitPoint
  reflected_marked_at_hit : reflectedRay.markedPoint = hitPoint
  hit_point_x_from_figure :
    lengthInMetres hitPoint.x =
      lengthInMetres mirror.radius * Real.sin incidenceAngle
  hit_point_y_from_figure :
    lengthInMetres hitPoint.y =
      lengthInMetres mirror.radius * Real.cos incidenceAngle
  hit_on_reflecting_surface : mirror.OnReflectingSurface hitPoint
  incoming_vertical_up :
    incidentRay.propagationDirection = { dx := 0, dy := 1 }
  normal_radial_outward :
    outwardNormal =
      { dx := Real.sin incidenceAngle
        dy := Real.cos incidenceAngle }
  obeys_specular_reflection :
    PlaneDirection.IsSpecularReflection
      incidentRay.propagationDirection outwardNormal
      reflectedRay.propagationDirection
  hit_on_reflected_line : reflectedLine.Contains hitPoint
  reflected_line_has_ray_direction :
    reflectedLine.HasDirection reflectedRay.propagationDirection
  reflected_ray_outgoing_down_left :
    reflectedRay.propagationDirection.dx < 0 ∧
      reflectedRay.propagationDirection.dy < 0

namespace Figure2gRayInteraction

/-- The scalar readout denoted by `m_A` when the interaction is ray A. -/
def mA {mirror : HalfCylindricalMirror} {incidenceAngle : ℝ}
    (interaction : Figure2gRayInteraction mirror incidenceAngle) : ℝ :=
  interaction.reflectedLine.slope

/-- The unit-independent physical length denoted by `b_A` when the interaction
is ray A. -/
def bA {mirror : HalfCylindricalMirror} {incidenceAngle : ℝ}
    (interaction : Figure2gRayInteraction mirror incidenceAngle) : LengthQuantity :=
  interaction.reflectedLine.intercept

end Figure2gRayInteraction

/-- Context retained for the later caustic construction: ray B is parallel to
ray A, has incidence angle `theta + deltaTheta`, and intersects ray A's
reflected line at the sampled caustic point.  `relativeScale` makes the
informal condition `Δθ ≪ θ` explicit without choosing an unstated numerical
tolerance. -/
structure Figure2gCausticSetup
    (mirror : HalfCylindricalMirror) (theta : ℝ) where
  rayA : Figure2gRayInteraction mirror theta
  deltaTheta : ℝ
  deltaTheta_pos : 0 < deltaTheta
  relativeScale : ℝ
  relativeScale_pos : 0 < relativeScale
  relativeScale_lt_one : relativeScale < 1
  deltaTheta_small_relative :
    |deltaTheta| ≤ relativeScale * |theta|
  rayB : Figure2gRayInteraction mirror (theta + deltaTheta)
  incoming_rays_parallel :
    rayB.incidentRay.propagationDirection =
      rayA.incidentRay.propagationDirection
  causticSamplePoint : PlanePoint
  caustic_point_on_reflected_rayA :
    rayA.reflectedLine.Contains causticSamplePoint
  caustic_point_on_reflected_rayB :
    rayB.reflectedLine.Contains causticSamplePoint

/-- The vector reflection law and Figure 2g orientation select the outgoing
down-left branch and give its doubled-angle direction. -/
theorem reflected_direction_from_specular_law
    (mirror : HalfCylindricalMirror) (incidenceAngle : ℝ)
    (interaction : Figure2gRayInteraction mirror incidenceAngle) :
    interaction.reflectedRay.propagationDirection =
      { dx := -Real.sin (2 * incidenceAngle)
        dy := -Real.cos (2 * incidenceAngle) } := by
  have hreflection := interaction.obeys_specular_reflection.2
  rw [interaction.incoming_vertical_up, interaction.normal_radial_outward] at hreflection
  rw [hreflection, PlaneDirection.mk.injEq]
  constructor
  · dsimp [PlaneDirection.reflectedByNormal, PlaneDirection.dot]
    rw [Real.sin_two_mul]
    ring
  · dsimp [PlaneDirection.reflectedByNormal, PlaneDirection.dot]
    rw [Real.cos_two_mul]
    ring

/-- The direction equation of the reflected supporting line determines its
dimensionless slope. -/
theorem reflected_line_slope
    (mirror : HalfCylindricalMirror) (incidenceAngle : ℝ)
    (interaction : Figure2gRayInteraction mirror incidenceAngle) :
    interaction.mA = Real.cot (2 * incidenceAngle) := by
  have hdirection :=
    reflected_direction_from_specular_law mirror incidenceAngle interaction
  have hline := interaction.reflected_line_has_ray_direction
  rw [hdirection] at hline
  change
    -Real.cos (2 * incidenceAngle) =
      interaction.reflectedLine.slope * (-Real.sin (2 * incidenceAngle))
    at hline
  have hleft := interaction.reflected_ray_outgoing_down_left.1
  rw [hdirection] at hleft
  change -Real.sin (2 * incidenceAngle) < 0 at hleft
  have hsin : Real.sin (2 * incidenceAngle) ≠ 0 := by
    nlinarith
  change interaction.reflectedLine.slope = Real.cot (2 * incidenceAngle)
  rw [Real.cot_eq_cos_div_sin]
  apply (eq_div_iff hsin).2
  nlinarith [hline]

/-- Incidence of the reflected line at the mirror hit point determines its
length-valued intercept. -/
theorem reflected_line_intercept
    (mirror : HalfCylindricalMirror) (incidenceAngle : ℝ)
    (interaction : Figure2gRayInteraction mirror incidenceAngle) :
    lengthInMetres interaction.bA =
      lengthInMetres mirror.radius / (2 * Real.cos incidenceAngle) := by
  have hline := interaction.hit_on_reflected_line
  change
    lengthInMetres interaction.hitPoint.y =
      interaction.reflectedLine.slope *
          lengthInMetres interaction.hitPoint.x +
        lengthInMetres interaction.reflectedLine.intercept
    at hline
  rw [interaction.hit_point_x_from_figure,
    interaction.hit_point_y_from_figure] at hline
  have hslope := reflected_line_slope mirror incidenceAngle interaction
  change
    interaction.reflectedLine.slope = Real.cot (2 * incidenceAngle)
    at hslope
  rw [hslope] at hline
  have hsin_pos : 0 < Real.sin incidenceAngle :=
    Real.sin_pos_of_pos_of_lt_pi interaction.incidenceAngle_pos
      (by nlinarith [interaction.incidenceAngle_lt_pi_div_two, Real.pi_pos])
  have hcos_pos : 0 < Real.cos incidenceAngle :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [interaction.incidenceAngle_pos, Real.pi_pos],
        interaction.incidenceAngle_lt_pi_div_two⟩
  have htrig :
      Real.cos incidenceAngle -
          Real.cot (2 * incidenceAngle) * Real.sin incidenceAngle =
        1 / (2 * Real.cos incidenceAngle) := by
    rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul]
    field_simp [ne_of_gt hsin_pos, ne_of_gt hcos_pos]
    ring
  change
    lengthInMetres interaction.reflectedLine.intercept =
      lengthInMetres mirror.radius / (2 * Real.cos incidenceAngle)
  calc
    lengthInMetres interaction.reflectedLine.intercept =
        lengthInMetres mirror.radius *
          (Real.cos incidenceAngle -
            Real.cot (2 * incidenceAngle) * Real.sin incidenceAngle) := by
      nlinarith [hline]
    _ = lengthInMetres mirror.radius *
          (1 / (2 * Real.cos incidenceAngle)) := by rw [htrig]
    _ = lengthInMetres mirror.radius /
          (2 * Real.cos incidenceAngle) := by ring

/-- **IPhO 2026, Problem 2, C.1.**  In the Figure 2g coordinate convention,
the reflected ray A has slope `cot (2 * theta)` and intercept
`R / (2 * cos theta)`. -/
theorem rayA_slope_and_intercept
    (mirror : HalfCylindricalMirror) (theta : ℝ)
    (setup : Figure2gCausticSetup mirror theta) :
    setup.rayA.mA = Real.cot (2 * theta) ∧
      lengthInMetres setup.rayA.bA =
        lengthInMetres mirror.radius / (2 * Real.cos theta) := by
  exact
    ⟨reflected_line_slope mirror theta setup.rayA,
      reflected_line_intercept mirror theta setup.rayA⟩

end

end IPhO2026_2_C_1
end IPhO2026Problems
