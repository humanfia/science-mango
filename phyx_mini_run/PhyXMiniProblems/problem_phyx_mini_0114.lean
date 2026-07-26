import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Units.WithDim.Basic

/-!
# Exact focal distance of a parabolic mirror

The mirror is the surface of revolution obtained from `y = a x²` about the
`y`-axis.  By axial symmetry it is enough to work in the meridional plane of
the ray shown in the figure.  Coordinate components below are read in one
chosen unit system, while all physical lengths and the inverse-length
coefficient `a` use Physlib's dimensionful quantity type.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0114

open Dimension

/-- The two-dimensional meridional plane containing the optic axis and the ray. -/
abbrev DiagramPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- A signed physical length, independent of the chosen unit readout. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The dimension carried by the parabola coefficient `a`: inverse length. -/
abbrev InverseLength : Type := Dimensionful (WithDim L𝓭⁻¹ ℝ)

/-- The incoming ray is parallel to the optic axis and propagates downward. -/
def incidentDirection : DiagramPlane :=
  !₂[0, -1]

/-- The horizontal direction from the point of incidence toward the optic axis. -/
def leftwardDirection : DiagramPlane :=
  !₂[-1, 0]

/--
The tangent direction to `y = a x²` at radial coordinate `r`.  The product
`a r` is dimensionless, so the vector is independent of the length unit used
for the two scalar readouts.
-/
def tangentDirection (aReadout rReadout : ℝ) : DiagramPlane :=
  !₂[1, 2 * aReadout * rReadout]

/-- The normal pointing into the open side of the parabolic mirror. -/
def outwardNormalDirection (aReadout rReadout : ℝ) : DiagramPlane :=
  !₂[-2 * aReadout * rReadout, 1]

/--
Specular reflection of the axial incident direction across the local tangent
line.  This is the vector form of equality of incidence and reflection angles,
implemented using Mathlib's reflection in a Euclidean subspace.
-/
noncomputable def specularlyReflectedDirection
    (aReadout rReadout : ℝ) : DiagramPlane :=
  Submodule.reflection
    (ℝ ∙ tangentDirection aReadout rReadout) incidentDirection

/-- The undirected radian angle between two directions in the diagram plane. -/
def angleBetweenDirections (first second : DiagramPlane) : ℝ :=
  InnerProductGeometry.angle first second

/--
Physical quantities and labels in the parabolic-mirror figure.

The mirror hit is at radius `r` and at height `f + b`: `f` is the focus's
height above the vertex, while `b` is the vertical rise from the focus level
to the hit.  `pathLengthToFocus` is an auxiliary propagation distance, not the
requested focal distance.  The angle fields are radian readouts of the labels
`φ` and `Δα`.
-/
structure ParabolicMirrorFigure where
  /-- Coefficient `a` in `y = a x²`, with inverse-length dimension. -/
  coefficientA : InverseLength
  /-- Figure label `r`, the incoming ray's radial distance from the optic axis. -/
  rayRadiusR : OpticalLength
  /-- Figure label `f`, the unknown distance from the vertex to the axial focus `F`. -/
  focusDistanceF : OpticalLength
  /-- Figure label `b`, the vertical separation between the hit and focus levels. -/
  focusToHitRiseB : OpticalLength
  /-- Distance propagated by the reflected unit direction from the hit to `F`. -/
  pathLengthToFocus : OpticalLength
  /-- Figure angle `φ`, measured in radians. -/
  phiRadians : ℝ
  /-- Figure angle `Δα`, measured in radians from the leftward horizontal. -/
  deltaAlphaRadians : ℝ

/-- Positivity and principal-angle conditions for the depicted physical branch. -/
structure HasPhysicalParabolicMirrorParameters
    (setup : ParabolicMirrorFigure) : Prop where
  coefficient_positive :
    0 < (setup.coefficientA UnitChoices.SI).val
  radius_positive :
    0 < (setup.rayRadiusR UnitChoices.SI).val
  focus_distance_positive :
    0 < (setup.focusDistanceF UnitChoices.SI).val
  rise_nonnegative :
    0 ≤ (setup.focusToHitRiseB UnitChoices.SI).val
  path_length_positive :
    0 < (setup.pathLengthToFocus UnitChoices.SI).val
  phi_acute :
    0 ≤ setup.phiRadians ∧ setup.phiRadians ≤ Real.pi / 2
  deltaAlpha_acute :
    0 ≤ setup.deltaAlphaRadians ∧ setup.deltaAlphaRadians ≤ Real.pi / 2

/--
Geometry read directly from the meridional figure.  The first relation places
the hit `(r, f + b)` on the parabola.  The remaining relations attach the
displayed angle labels to the incident ray, local normal, reflected ray, and
leftward horizontal.  They do not determine the requested value of `f` by
themselves.
-/
structure MatchesParabolicMirrorFigure
    (setup : ParabolicMirrorFigure) : Prop where
  mirror_point_on_parabola :
    ∀ units : UnitChoices,
      (setup.focusDistanceF units).val +
          (setup.focusToHitRiseB units).val =
        (setup.coefficientA units).val *
          (setup.rayRadiusR units).val ^ 2
  phi_is_incidence_angle :
    setup.phiRadians =
      angleBetweenDirections
        (-incidentDirection)
        (outwardNormalDirection
          (setup.coefficientA UnitChoices.SI).val
          (setup.rayRadiusR UnitChoices.SI).val)
  phi_is_reflection_angle :
    setup.phiRadians =
      angleBetweenDirections
        (specularlyReflectedDirection
          (setup.coefficientA UnitChoices.SI).val
          (setup.rayRadiusR UnitChoices.SI).val)
        (outwardNormalDirection
          (setup.coefficientA UnitChoices.SI).val
          (setup.rayRadiusR UnitChoices.SI).val)
  deltaAlpha_is_reflected_inclination :
    setup.deltaAlphaRadians =
      angleBetweenDirections
        (specularlyReflectedDirection
          (setup.coefficientA UnitChoices.SI).val
          (setup.rayRadiusR UnitChoices.SI).val)
        leftwardDirection

/--
Ideal straight-line propagation after specular reflection: starting from the
mirror hit, the reflected ray reaches the axial focus.  The displacement to
the focus is `(-r, -b)` in every consistent length-unit readout.  Specular
reflection is supplied by `specularlyReflectedDirection`, independently of the
unknown focal-distance formula.
-/
structure SatisfiesIdealParabolicMirrorOptics
    (setup : ParabolicMirrorFigure) : Prop where
  reflected_ray_reaches_focus :
    ∀ units : UnitChoices,
      !₂[-(setup.rayRadiusR units).val,
          -(setup.focusToHitRiseB units).val] =
        (setup.pathLengthToFocus units).val •
          specularlyReflectedDirection
            (setup.coefficientA units).val
            (setup.rayRadiusR units).val

/--
Every nonaxial ray parallel to the axis and reflected by `y = a x²` meets the
axis at the unit-independent focal distance `f = 1 / (4a)`, exactly and
without a paraxial approximation.  This is answer choice A.

Blueprint label: `thm:physics:phyx_mini_0114:target`.
-/
theorem parabolicMirrorFocalDistance
    (setup : ParabolicMirrorFigure)
    (_physical : HasPhysicalParabolicMirrorParameters setup)
    (_figure : MatchesParabolicMirrorFigure setup)
    (_optics : SatisfiesIdealParabolicMirrorOptics setup) :
    ∀ units : UnitChoices,
      (setup.focusDistanceF units).val =
        1 / (4 * (setup.coefficientA units).val) := by
  intro units
  have ha_scale :=
    congrArg WithDim.val
      (setup.coefficientA.property UnitChoices.SI units)
  have hr_scale :=
    congrArg WithDim.val
      (setup.rayRadiusR.property UnitChoices.SI units)
  have hp_scale :=
    congrArg WithDim.val
      (setup.pathLengthToFocus.property UnitChoices.SI units)
  simp only [WithDim.smul_val, NNReal.smul_def, smul_eq_mul] at ha_scale hr_scale hp_scale
  have ha : 0 < (setup.coefficientA units).val := by
    rw [ha_scale]
    apply mul_pos
    · exact_mod_cast
        UnitChoices.dimScale_pos UnitChoices.SI units
          (dim (WithDim L𝓭⁻¹ ℝ))
    · exact _physical.coefficient_positive
  have hr : 0 < (setup.rayRadiusR units).val := by
    rw [hr_scale]
    apply mul_pos
    · exact_mod_cast
        UnitChoices.dimScale_pos UnitChoices.SI units
          (dim (WithDim L𝓭 ℝ))
    · exact _physical.radius_positive
  have hp : 0 < (setup.pathLengthToFocus units).val := by
    rw [hp_scale]
    apply mul_pos
    · exact_mod_cast
        UnitChoices.dimScale_pos UnitChoices.SI units
          (dim (WithDim L𝓭 ℝ))
    · exact _physical.path_length_positive
  have h_reaches := _optics.reflected_ray_reaches_focus units
  have hx := congrArg (fun v : DiagramPlane => v 0) h_reaches
  have hy := congrArg (fun v : DiagramPlane => v 1) h_reaches
  simp [specularlyReflectedDirection, Submodule.reflection_singleton_apply,
    tangentDirection, incidentDirection] at hx hy
  simp [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq] at hx hy
  have hmirror := _figure.mirror_point_on_parabola units
  generalize ha_def : (setup.coefficientA units).val = a at ha hx hy hmirror ⊢
  generalize hr_def : (setup.rayRadiusR units).val = r at hr hx hy hmirror
  generalize hp_def : (setup.pathLengthToFocus units).val = p at hp hx hy
  generalize hb_def : (setup.focusToHitRiseB units).val = b at hy hmirror
  generalize hf_def : (setup.focusDistanceF units).val = f at hmirror ⊢
  clear ha_scale hr_scale hp_scale h_reaches
  clear ha_def hr_def hp_def hb_def hf_def
  clear _physical _figure _optics setup units
  field_simp at hx hy
  ring_nf at hx hy
  have hxp : 4 * a * p = 1 + 4 * a ^ 2 * r ^ 2 := by
    nlinarith [hx]
  have hxp_b := congrArg (fun x : ℝ => x * b) hxp
  have h_times_p :
      p * (4 * a * b + 1 - 4 * a ^ 2 * r ^ 2) = 0 := by
    nlinarith [hy, hxp_b]
  have hb : 4 * a * b + 1 - 4 * a ^ 2 * r ^ 2 = 0 :=
    (mul_eq_zero.mp h_times_p).resolve_left (ne_of_gt hp)
  have hmirror_mul := congrArg (fun x : ℝ => 4 * a * x) hmirror
  field_simp
  nlinarith [hb, hmirror_mul]

end PhyXMiniProblems.ProblemPhyXMini0114
