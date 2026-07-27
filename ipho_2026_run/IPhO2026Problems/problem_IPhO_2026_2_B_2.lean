import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 problem 2, part B.2

The half-cylindrical mirror and cylindrical absorber from figure 2f are modeled
at the level needed for the power calculation.  Length, irradiance, and power
carry their physical dimensions through Physlib's `WithDim`.
-/

namespace IPhO2026Problems
namespace IPhO2026_2_B_2

open Dimension

/-- A real-valued length in a common coherent system of units. -/
abbrev LengthQuantity := WithDim L𝓭 ℝ

/-- The physical dimension `mass * length^2 / time^3` of power. -/
def powerDimension : Dimension := M𝓭 * L𝓭 ^ 2 * T𝓭⁻¹ ^ 3

/-- A real-valued physical power. -/
abbrev PowerQuantity := WithDim powerDimension ℝ

/-- The physical dimension of irradiance: power per unit area. -/
def irradianceDimension : Dimension := powerDimension * (L𝓭 ^ 2)⁻¹

/-- A real-valued irradiance. -/
abbrev IrradianceQuantity := WithDim irradianceDimension ℝ

/--
The labeled geometric data of figure 2f.

The abstract point, axis, parallelism, plane-incidence, and distance data retain
the geometric roles of the two cylinder centers and axes without committing to
a coordinate realization that the subproblem does not require.
-/
structure Figure2fGeometry where
  Point : Type
  Axis : Type
  mirrorCenter : Point
  containerCenter : Point
  mirrorAxis : Axis
  containerAxis : Axis
  mirrorOpticalAxis : Axis
  axesParallel : Axis → Axis → Prop
  onSymmetryPlane : Point → Prop
  centerDistance : Point → Point → LengthQuantity
  mirrorRadius : LengthQuantity
  containerRadius : LengthQuantity
  illuminatedLength : LengthQuantity
  mirrorIsHalfCylinder : Prop
  containerIsCylinder : Prop

/--
Ray, irradiance, incidence-angle, and received-power data for the solar cooker.
`incidenceAngle` is measured from the mirror normal at the point of incidence,
as specified in the problem statement.
-/
structure OpticalModel (g : Figure2fGeometry) where
  Ray : Type
  isIncoming : Ray → Prop
  hitsMirror : Ray → Prop
  hitsContainer : Ray → Prop
  absorbedByContainer : Ray → Prop
  parallelToOpticalAxis : Ray → Prop
  reflectionCount : Ray → ℕ
  incidenceAngle : Ray → ℝ
  irradianceAlong : Ray → IrradianceQuantity
  solarIrradiance : IrradianceQuantity
  thetaMax : ℝ
  actualReceivedPower : PowerQuantity
  noMirrorReceivedPower : PowerQuantity

/-- Figure 2f's shape, parallel-axis, symmetry-plane, and `R / 2` placement data. -/
def HasFigure2fPlacement (g : Figure2fGeometry) : Prop :=
  g.mirrorIsHalfCylinder ∧
    g.containerIsCylinder ∧
    g.axesParallel g.mirrorAxis g.containerAxis ∧
    g.onSymmetryPlane g.mirrorCenter ∧
    g.onSymmetryPlane g.containerCenter ∧
    (g.centerDistance g.mirrorCenter g.containerCenter).val = g.mirrorRadius.val / 2

/--
Incoming sunlight has one positive constant irradiance and all incoming rays
are parallel to the mirror's optical axis.
-/
def HasUniformParallelSunlight {g : Figure2fGeometry} (o : OpticalModel g) : Prop :=
  0 < o.solarIrradiance.val ∧
    (∃ ray, o.isIncoming ray) ∧
    ∀ ray, o.isIncoming ray →
      o.parallelToOpticalAxis ray ∧ o.irradianceAlong ray = o.solarIrradiance

/-- Every ray that reaches the cylindrical container is absorbed. -/
def IsFullyAbsorbing {g : Figure2fGeometry} (o : OpticalModel g) : Prop :=
  ∀ ray, o.hitsContainer ray → o.absorbedByContainer ray

/-- A ray absorbed by the container has reflected from the mirror at most once. -/
def IsSingleReflectionRegime {g : Figure2fGeometry} (o : OpticalModel g) : Prop :=
  ∀ ray, o.absorbedByContainer ray → o.reflectionCount ray ≤ 1

/--
`thetaMax` is attained and bounds the mirror incidence angle of every reflected
ray that strikes the container.
-/
def IsLargestRelevantIncidenceAngle {g : Figure2fGeometry} (o : OpticalModel g) : Prop :=
  (∀ ray, o.hitsMirror ray → o.hitsContainer ray → o.reflectionCount ray = 1 →
      o.incidenceAngle ray ≤ o.thetaMax) ∧
    ∃ ray, o.hitsMirror ray ∧ o.hitsContainer ray ∧ o.reflectionCount ray = 1 ∧
      o.incidenceAngle ray = o.thetaMax

/--
The conclusion of previous part B.1 after substituting
`alpha = R` and `beta = -R / 2`.
-/
def HasPartB1RadiusRelation (g : Figure2fGeometry) (thetaMax : ℝ) : Prop :=
  g.containerRadius.val =
    g.mirrorRadius.val * Real.sin thetaMax -
      g.mirrorRadius.val / 2 * Real.sin (2 * thetaMax)

/--
Power equals uniform irradiance times the illuminated projected area.

With the mirror, the transverse collection width is
`2 * R * sin(thetaMax)`; without it, the cylinder's projected width is `2 * a`.
Both areas have the same illuminated axial length.
-/
def SatisfiesProjectedAperturePowerLaws {g : Figure2fGeometry}
    (o : OpticalModel g) : Prop :=
  o.actualReceivedPower.val =
      o.solarIrradiance.val *
        (2 * g.mirrorRadius.val * Real.sin o.thetaMax) * g.illuminatedLength.val ∧
    o.noMirrorReceivedPower.val =
      o.solarIrradiance.val * (2 * g.containerRadius.val) * g.illuminatedLength.val

/--
For the solar cooker of figure 2f, the mirror enhancement of the received
power is `1 / (1 - cos(thetaMax))`.

Blueprint label: `thm:physics:IPhO_2026_2_B_2:target`.
-/
theorem problem_IPhO_2026_2_B_2
    (g : Figure2fGeometry) (o : OpticalModel g)
    (h_placement : HasFigure2fPlacement g)
    (h_sunlight : HasUniformParallelSunlight o)
    (h_absorbing : IsFullyAbsorbing o)
    (h_reflection : IsSingleReflectionRegime o)
    (h_theta_max : IsLargestRelevantIncidenceAngle o)
    (h_theta_pos : 0 < o.thetaMax)
    (h_theta_lt : o.thetaMax < Real.pi / 2)
    (h_mirror_radius : 0 < g.mirrorRadius.val)
    (h_container_radius : 0 < g.containerRadius.val)
    (h_length : 0 < g.illuminatedLength.val)
    (h_part_B1 : HasPartB1RadiusRelation g o.thetaMax)
    (h_power : SatisfiesProjectedAperturePowerLaws o) :
    o.actualReceivedPower.val / o.noMirrorReceivedPower.val =
      1 / (1 - Real.cos o.thetaMax) := by
  rcases h_power with ⟨hP, hP0⟩
  have hI : 0 < o.solarIrradiance.val := h_sunlight.1
  unfold HasPartB1RadiusRelation at h_part_B1
  rw [Real.sin_two_mul] at h_part_B1
  have hcos : 1 - Real.cos o.thetaMax ≠ 0 := by
    intro hz
    have hc : Real.cos o.thetaMax = 1 := by
      linarith
    rw [hc] at h_part_B1
    nlinarith
  rw [hP, hP0]
  field_simp [hcos, ne_of_gt hI, ne_of_gt h_container_radius, ne_of_gt h_length]
  nlinarith [h_part_B1]

end IPhO2026_2_B_2
end IPhO2026Problems
