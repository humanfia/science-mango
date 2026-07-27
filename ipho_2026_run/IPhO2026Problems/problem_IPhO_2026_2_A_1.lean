import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 2, part A.1

Parallel rays enter the open diameter of a half-cylindrical mirror.  This file
models the two-dimensional cross-section shown in Figures 2c--2e, individual
specular-reflection events, and the threshold readout `x_N`.

The mirror radius and reflection threshold are dimensionful physical lengths.
Their real-valued transverse and point coordinates are obtained through one
named SI projection.  Angles are dimensionless and measured in radians.
-/

namespace IPhO2026Problems.IPhO2026_2_A_1

/-- A physical length represented independently of the choice of units. -/
abbrev PhysicalLength := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The common length-coordinate projection used throughout the cross-section.
Its numerical value is measured in SI metres. -/
noncomputable def lengthCoordinate (length : PhysicalLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The Euclidean cross-section perpendicular to the cylinder axis. -/
abbrev CrossSectionPoint := EuclideanSpace ℝ (Fin 2)

/-- The official figure labels used to read the mirror and limiting-ray
geometry. -/
inductive FigureLabel where
  | figure2c
  | figure2d
  | figure2e
  deriving DecidableEq

/-- A half-cylindrical mirror, represented by its semicircular cross-section.
`opticalAxisDirection` points from the center into the reflecting half-plane. -/
structure HalfCylindricalMirror where
  center : CrossSectionPoint
  opticalAxisDirection : CrossSectionPoint
  opticalAxisDirection_unit : ‖opticalAxisDirection‖ = 1
  radius : PhysicalLength
  radiusCoordinate_pos : 0 < lengthCoordinate radius

/-- A point lies on the reflecting semicircular arc of the mirror. -/
def OnReflectingArc (mirror : HalfCylindricalMirror)
    (point : CrossSectionPoint) : Prop :=
  ‖point - mirror.center‖ = lengthCoordinate mirror.radius ∧
    0 ≤ inner ℝ (point - mirror.center) mirror.opticalAxisDirection

/-- An oriented geometrical ray in the cross-section. -/
structure GeometricRay where
  origin : CrossSectionPoint
  direction : CrossSectionPoint
  direction_ne_zero : direction ≠ 0

/-- Parallel incident rays indexed by their signed transverse-coordinate
readout `x`.  The unit transverse vector makes the index use the same length
unit as the point coordinates. -/
structure ParallelIncidentRayFamily where
  rayAt : ℝ → GeometricRay
  axisPoint : CrossSectionPoint
  commonDirection : CrossSectionPoint
  transverseDirection : CrossSectionPoint
  commonDirection_unit : ‖commonDirection‖ = 1
  transverseDirection_unit : ‖transverseDirection‖ = 1
  transverseDirection_perp :
    inner ℝ commonDirection transverseDirection = 0
  rayAt_origin :
    ∀ x, (rayAt x).origin = axisPoint + x • transverseDirection
  rayAt_direction :
    ∀ x, (rayAt x).direction = commonDirection

/-- The incident family is centered on, and parallel to, the mirror's optical
axis as in Figure 2d. -/
def AlignedWithMirror (mirror : HalfCylindricalMirror)
    (family : ParallelIncidentRayFamily) : Prop :=
  family.axisPoint = mirror.center ∧
    family.commonDirection = mirror.opticalAxisDirection

/-- The local geometric data at one reflection from the curved mirror. -/
structure ReflectionEvent where
  surfacePoint : CrossSectionPoint
  incomingDirection : CrossSectionPoint
  outgoingDirection : CrossSectionPoint
  surfaceNormal : CrossSectionPoint
  incomingDirection_ne_zero : incomingDirection ≠ 0
  outgoingDirection_ne_zero : outgoingDirection ≠ 0
  surfaceNormal_ne_zero : surfaceNormal ≠ 0

/-- Vector form of the law of specular reflection.  The normal need not be a
unit vector. -/
def IsSpecularReflection (event : ReflectionEvent) : Prop :=
  event.outgoingDirection =
    event.incomingDirection -
      (2 *
        (inner ℝ event.incomingDirection event.surfaceNormal /
          inner ℝ event.surfaceNormal event.surfaceNormal)) •
        event.surfaceNormal

/-- A finite ordered record of all reflections undergone by one ray. -/
structure ReflectionTrace where
  numberOfReflections : ℕ
  eventAt : Fin numberOfReflections → ReflectionEvent

/-- The physical interaction of rays with a fixed half-cylindrical mirror.
Every recorded event occurs on the arc, uses a radial normal, and obeys the
specular-reflection law. -/
structure MirrorDynamics (mirror : HalfCylindricalMirror) where
  trace : GeometricRay → ReflectionTrace
  event_on_arc :
    ∀ (ray : GeometricRay)
      (i : Fin (trace ray).numberOfReflections),
      OnReflectingArc mirror ((trace ray).eventAt i).surfacePoint
  event_normal_is_radial :
    ∀ (ray : GeometricRay)
      (i : Fin (trace ray).numberOfReflections),
      ∃ c : ℝ, c ≠ 0 ∧
        ((trace ray).eventAt i).surfaceNormal =
          c • (((trace ray).eventAt i).surfacePoint - mirror.center)
  event_is_specular :
    ∀ (ray : GeometricRay)
      (i : Fin (trace ray).numberOfReflections),
      IsSpecularReflection ((trace ray).eventAt i)

/-- The number `N` of reflections undergone by a ray. -/
def reflectionCount {mirror : HalfCylindricalMirror}
    (dynamics : MirrorDynamics mirror) (ray : GeometricRay) : ℕ :=
  (dynamics.trace ray).numberOfReflections

/-- Figure 2e's threshold meaning: within the open aperture `|x| < R`, a ray
has at most `N` reflections exactly when its distance from the optical axis is
at most the positive threshold `xN`. -/
def IsReflectionThreshold (mirror : HalfCylindricalMirror)
    (family : ParallelIncidentRayFamily) (dynamics : MirrorDynamics mirror)
    (N : ℕ) (xN : PhysicalLength) : Prop :=
  0 < lengthCoordinate xN ∧
    lengthCoordinate xN < lengthCoordinate mirror.radius ∧
    ∀ x, |x| < lengthCoordinate mirror.radius →
      (reflectionCount dynamics (family.rayAt x) ≤ N ↔
        |x| ≤ lengthCoordinate xN)

/-- Figure-derived limiting-ray relations used before solving for `xN`.

The projection relation reads the transverse coordinate from the radius and
the limiting angle.  The final relation is the full-turn closure accumulated
from the equal turning angles of the specular orbit.  Neither field states the
requested closed form for `xN`. -/
structure Figure2cTo2eLimitingGeometry
    (mirror : HalfCylindricalMirror)
    (family : ParallelIncidentRayFamily)
    (dynamics : MirrorDynamics mirror)
    (N : ℕ) (xN : PhysicalLength) (limitingAngle : ℝ) : Prop where
  limitingAngle_pos : 0 < limitingAngle
  limitingAngle_lt_rightAngle : limitingAngle < Real.pi / 2
  threshold_projection :
    lengthCoordinate xN =
      lengthCoordinate mirror.radius * Real.sin limitingAngle
  threshold_ray_count :
    reflectionCount dynamics (family.rayAt (lengthCoordinate xN)) = N
  total_turning_angle :
    (2 * (N : ℝ) + 1) * (Real.pi - 2 * limitingAngle) =
      2 * Real.pi

/-- The threshold formula requested in IPhO 2026 problem 2, part A.1.

The first equality is the sine form recorded in the marking context; the
second is its complementary-angle cosine form. -/
theorem threshold_formula
    (mirror : HalfCylindricalMirror)
    (family : ParallelIncidentRayFamily)
    (dynamics : MirrorDynamics mirror)
    (R xN : PhysicalLength) (limitingAngle : ℝ) (N : ℕ)
    (hN : 0 < N)
    (hRadius : mirror.radius = R)
    (hAligned : AlignedWithMirror mirror family)
    (hThreshold : IsReflectionThreshold mirror family dynamics N xN)
    (hFigure :
      Figure2cTo2eLimitingGeometry
        mirror family dynamics N xN limitingAngle) :
    lengthCoordinate xN =
        lengthCoordinate R * Real.sin
          (((2 * (N : ℝ) - 1) * Real.pi) / (4 * (N : ℝ) + 2)) ∧
      lengthCoordinate xN =
        lengthCoordinate R * Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  have hDenominator : (4 * (N : ℝ) + 2) ≠ 0 := by
    positivity
  have hLimitingAngle :
      limitingAngle =
        ((2 * (N : ℝ) - 1) * Real.pi) / (4 * (N : ℝ) + 2) := by
    apply (eq_div_iff hDenominator).2
    nlinarith [hFigure.total_turning_angle]
  have hComplementaryAngle :
      ((2 * (N : ℝ) - 1) * Real.pi) / (4 * (N : ℝ) + 2) =
        Real.pi / 2 - Real.pi / (2 * (N : ℝ) + 1) := by
    have hOddDenominator : (2 * (N : ℝ) + 1) ≠ 0 := by
      positivity
    field_simp
    ring
  constructor
  · simpa [hRadius, hLimitingAngle] using hFigure.threshold_projection
  · simpa [hRadius, hLimitingAngle, hComplementaryAngle,
      Real.sin_pi_div_two_sub] using hFigure.threshold_projection

end IPhO2026Problems.IPhO2026_2_A_1
