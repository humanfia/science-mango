import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0028

/-- The unit system obtained from SI by expressing its length component in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The real-valued readout of a physical length in an arbitrary unit system. -/
def lengthValue
    (units : UnitChoices) (length : Dimensionful (WithDim Dimension.L𝓭 ℝ)) : ℝ :=
  (length units).val

/-- The numerical value of a physical length when expressed in centimeters. -/
def centimeterValue (length : Dimensionful (WithDim Dimension.L𝓭 ℝ)) : ℝ :=
  lengthValue centimeterUnitChoices length

/--
The plano-convex lens and the axis-coordinate labels needed in the meridional
cross-section from the figure. Refractive indices are dimensionless, while all
three geometric fields are genuine physical lengths.
-/
structure PlanoConvexLens where
  /-- Figure point `C`, represented by its coordinate on the principal axis. -/
  curvatureCenterAxisPosition : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- The axis coordinate of the planar entry face. -/
  planarFaceAxisPosition : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- Figure label `R`, the radius of the spherical convex face. -/
  sphericalRadius : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- The refractive index of the lens material. -/
  lensRefractiveIndex : ℝ
  /-- The refractive index of the exterior medium (air in this problem). -/
  exteriorRefractiveIndex : ℝ

/--
The non-numerical geometry and positivity conditions for the depicted lens.
The spherical vertex is at `C + R`; the planar face lies strictly between the
center of curvature and that vertex.
-/
def IsPhysicalPlanoConvexLens (lens : PlanoConvexLens) : Prop :=
  0 < centimeterValue lens.sphericalRadius ∧
    centimeterValue lens.curvatureCenterAxisPosition <
      centimeterValue lens.planarFaceAxisPosition ∧
    centimeterValue lens.planarFaceAxisPosition <
      centimeterValue lens.curvatureCenterAxisPosition +
        centimeterValue lens.sphericalRadius ∧
    0 < lens.exteriorRefractiveIndex ∧
    lens.exteriorRefractiveIndex < lens.lensRefractiveIndex

/--
Readouts for one meridional ray which enters normally through the planar face,
travels parallel to the principal axis inside the lens, and refracts through
the spherical face. Angles are dimensionless real readouts in radians and are
measured from the local outward spherical normal.
-/
structure ParallelAxisRayTrace where
  /-- The ray's perpendicular distance from the principal axis (`h₁` or `h₂`). -/
  heightFromAxis : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- Axis coordinate of the point where the ray meets the spherical face. -/
  sphericalFaceAxisPosition : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- Incident angle between the horizontal internal ray and the radial normal. -/
  normalAngleRadians : ℝ
  /-- Refracted angle in air, measured from the same radial normal. -/
  transmittedAngleRadians : ℝ
  /-- Axis coordinate at which the transmitted ray crosses the principal axis. -/
  axisCrossingPosition : Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- Snell's law for dimensionless refractive indices and radian angle readouts. -/
def SnellLawAtInterface
    (incidentRefractiveIndex transmittedRefractiveIndex : ℝ)
    (incidentAngleRadians transmittedAngleRadians : ℝ) : Prop :=
  incidentRefractiveIndex * Real.sin incidentAngleRadians =
    transmittedRefractiveIndex * Real.sin transmittedAngleRadians

/--
The governing spherical-surface geometry and refraction law for one depicted
ray. The square-root equation selects the right-hand spherical face. The last
equation follows the transmitted ray from its surface point to its crossing
with the principal axis; it is a general ray law and contains no numerical
claim about the requested separation `Δx`.
-/
def SatisfiesSphericalExitRayLaw
    (units : UnitChoices) (lens : PlanoConvexLens) (ray : ParallelAxisRayTrace) : Prop :=
  let h := lengthValue units ray.heightFromAxis
  let radius := lengthValue units lens.sphericalRadius
  let centerX := lengthValue units lens.curvatureCenterAxisPosition
  let surfaceX := lengthValue units ray.sphericalFaceAxisPosition
  let crossingX := lengthValue units ray.axisCrossingPosition
  0 < h ∧
    h < radius ∧
    ray.normalAngleRadians ∈ Set.Ioo 0 (Real.pi / 2) ∧
    ray.transmittedAngleRadians ∈
      Set.Ioo ray.normalAngleRadians (Real.pi / 2) ∧
    Real.sin ray.normalAngleRadians = h / radius ∧
    SnellLawAtInterface
      lens.lensRefractiveIndex lens.exteriorRefractiveIndex
      ray.normalAngleRadians ray.transmittedAngleRadians ∧
    surfaceX = centerX + Real.sqrt (radius ^ 2 - h ^ 2) ∧
    crossingX = surfaceX +
      h / Real.tan (ray.transmittedAngleRadians - ray.normalAngleRadians)

/-- The centimeter readout of the figure's `Δx` between two axis crossings. -/
def axisCrossingSeparationCm
    (ray₁ ray₂ : ParallelAxisRayTrace) : ℝ :=
  |centimeterValue ray₁.axisCrossingPosition -
    centimeterValue ray₂.axisCrossingPosition|

/--
For a plano-convex lens of index `1.60` in air, spherical radius `20.0 cm`,
and parallel rays at heights `0.500 cm` and `12.0 cm`, the separation of the
two principal-axis crossings rounds to `21.3 cm`, answer choice D.

The strict half-tenth bound gives the reporting precision implicit in the
one-decimal answer choices.

Blueprint: `thm:physics:phyx_mini_0028:target`.
-/
theorem axisCrossingSeparation_roundsTo_choiceD
    (lens : PlanoConvexLens)
    (nearAxisRay edgeRay : ParallelAxisRayTrace)
    (h_lens_physical : IsPhysicalPlanoConvexLens lens)
    (h_lens_index : lens.lensRefractiveIndex = 8 / 5)
    (h_air_index : lens.exteriorRefractiveIndex = 1)
    (h_radius : centimeterValue lens.sphericalRadius = 20)
    (h_near_height : centimeterValue nearAxisRay.heightFromAxis = 1 / 2)
    (h_edge_height : centimeterValue edgeRay.heightFromAxis = 12)
    (h_near_ray_law :
      SatisfiesSphericalExitRayLaw centimeterUnitChoices lens nearAxisRay)
    (h_edge_ray_law :
      SatisfiesSphericalExitRayLaw centimeterUnitChoices lens edgeRay) :
    |axisCrossingSeparationCm nearAxisRay edgeRay - 213 / 10| < 1 / 20 := by
  change lengthValue centimeterUnitChoices lens.sphericalRadius = 20 at h_radius
  change lengthValue centimeterUnitChoices nearAxisRay.heightFromAxis = 1 / 2 at h_near_height
  change lengthValue centimeterUnitChoices edgeRay.heightFromAxis = 12 at h_edge_height
  simp only [SatisfiesSphericalExitRayLaw] at h_near_ray_law h_edge_ray_law
  rcases h_near_ray_law with
    ⟨h_near_height_pos, h_near_height_lt, h_near_normal_angle,
      h_near_transmitted_angle, h_near_sin, h_near_snell,
      h_near_surface, h_near_crossing⟩
  rcases h_edge_ray_law with
    ⟨h_edge_height_pos, h_edge_height_lt, h_edge_normal_angle,
      h_edge_transmitted_angle, h_edge_sin, h_edge_snell,
      h_edge_surface, h_edge_crossing⟩
  have h_near_sin_normal :
      Real.sin nearAxisRay.normalAngleRadians = 1 / 40 := by
    rw [h_near_height, h_radius] at h_near_sin
    norm_num at h_near_sin ⊢
    exact h_near_sin
  have h_edge_sin_normal :
      Real.sin edgeRay.normalAngleRadians = 3 / 5 := by
    rw [h_edge_height, h_radius] at h_edge_sin
    norm_num at h_edge_sin ⊢
    exact h_edge_sin
  have h_near_sin_transmitted :
      Real.sin nearAxisRay.transmittedAngleRadians = 1 / 25 := by
    simp only [SnellLawAtInterface] at h_near_snell
    rw [h_lens_index, h_air_index, h_near_sin_normal] at h_near_snell
    norm_num at h_near_snell ⊢
    linarith
  have h_edge_sin_transmitted :
      Real.sin edgeRay.transmittedAngleRadians = 24 / 25 := by
    simp only [SnellLawAtInterface] at h_edge_snell
    rw [h_lens_index, h_air_index, h_edge_sin_normal] at h_edge_snell
    norm_num at h_edge_snell ⊢
    linarith
  have h_near_cos_normal_pos :
      0 < Real.cos nearAxisRay.normalAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos, h_near_normal_angle.1],
        h_near_normal_angle.2⟩
  have h_near_cos_transmitted_pos :
      0 < Real.cos nearAxisRay.transmittedAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by
        nlinarith [Real.pi_pos, h_near_normal_angle.1,
          h_near_transmitted_angle.1],
        h_near_transmitted_angle.2⟩
  have h_edge_cos_normal_pos :
      0 < Real.cos edgeRay.normalAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos, h_edge_normal_angle.1],
        h_edge_normal_angle.2⟩
  have h_edge_cos_transmitted_pos :
      0 < Real.cos edgeRay.transmittedAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by
        nlinarith [Real.pi_pos, h_edge_normal_angle.1,
          h_edge_transmitted_angle.1],
        h_edge_transmitted_angle.2⟩
  have h_near_cos_normal_sq :
      Real.cos nearAxisRay.normalAngleRadians ^ 2 = 1599 / 1600 := by
    have h_trig := Real.sin_sq_add_cos_sq nearAxisRay.normalAngleRadians
    rw [h_near_sin_normal] at h_trig
    norm_num at h_trig ⊢
    linarith only [h_trig]
  have h_near_cos_transmitted_sq :
      Real.cos nearAxisRay.transmittedAngleRadians ^ 2 = 624 / 625 := by
    have h_trig := Real.sin_sq_add_cos_sq nearAxisRay.transmittedAngleRadians
    rw [h_near_sin_transmitted] at h_trig
    norm_num at h_trig ⊢
    linarith only [h_trig]
  have h_edge_cos_normal :
      Real.cos edgeRay.normalAngleRadians = 4 / 5 := by
    have h_trig := Real.sin_sq_add_cos_sq edgeRay.normalAngleRadians
    rw [h_edge_sin_normal] at h_trig
    norm_num at h_trig ⊢
    nlinarith only [h_trig, h_edge_cos_normal_pos]
  have h_edge_cos_transmitted :
      Real.cos edgeRay.transmittedAngleRadians = 7 / 25 := by
    have h_trig := Real.sin_sq_add_cos_sq edgeRay.transmittedAngleRadians
    rw [h_edge_sin_transmitted] at h_trig
    norm_num at h_trig ⊢
    nlinarith only [h_trig, h_edge_cos_transmitted_pos]
  have h_sqrt_256 : Real.sqrt 256 = 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h_edge_surface' :
      lengthValue centimeterUnitChoices edgeRay.sphericalFaceAxisPosition =
        lengthValue centimeterUnitChoices lens.curvatureCenterAxisPosition + 16 := by
    rw [h_radius, h_edge_height] at h_edge_surface
    norm_num at h_edge_surface
    rw [h_sqrt_256] at h_edge_surface
    exact h_edge_surface
  have h_edge_tan :
      Real.tan (edgeRay.transmittedAngleRadians - edgeRay.normalAngleRadians) =
        3 / 4 := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub,
      h_edge_sin_transmitted, h_edge_sin_normal,
      h_edge_cos_transmitted, h_edge_cos_normal]
    norm_num
  have h_edge_crossing' :
      lengthValue centimeterUnitChoices edgeRay.axisCrossingPosition =
        lengthValue centimeterUnitChoices edgeRay.sphericalFaceAxisPosition + 16 := by
    rw [h_edge_height, h_edge_tan] at h_edge_crossing
    norm_num at h_edge_crossing ⊢
    exact h_edge_crossing
  have h_edge_axis_crossing :
      lengthValue centimeterUnitChoices edgeRay.axisCrossingPosition =
        lengthValue centimeterUnitChoices lens.curvatureCenterAxisPosition + 32 := by
    calc
      lengthValue centimeterUnitChoices edgeRay.axisCrossingPosition =
          lengthValue centimeterUnitChoices edgeRay.sphericalFaceAxisPosition + 16 :=
        h_edge_crossing'
      _ = lengthValue centimeterUnitChoices lens.curvatureCenterAxisPosition + 32 := by
        rw [h_edge_surface']
        ring
  have h_near_tan :
      Real.tan (nearAxisRay.transmittedAngleRadians -
          nearAxisRay.normalAngleRadians) =
        (Real.cos nearAxisRay.normalAngleRadians / 25 -
            Real.cos nearAxisRay.transmittedAngleRadians / 40) /
          (Real.cos nearAxisRay.transmittedAngleRadians *
              Real.cos nearAxisRay.normalAngleRadians + 1 / 1000) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub,
      h_near_sin_transmitted, h_near_sin_normal]
    ring
  have h_near_surface_sqrt :
      Real.sqrt (20 ^ 2 - (1 / 2 : ℝ) ^ 2) =
        20 * Real.cos nearAxisRay.normalAngleRadians := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num)
      (mul_nonneg (by norm_num) h_near_cos_normal_pos.le)).2
    nlinarith only [h_near_cos_normal_sq]
  have h_near_surface' :
      lengthValue centimeterUnitChoices nearAxisRay.sphericalFaceAxisPosition =
        lengthValue centimeterUnitChoices lens.curvatureCenterAxisPosition +
          20 * Real.cos nearAxisRay.normalAngleRadians := by
    rw [h_radius, h_near_height] at h_near_surface
    rw [h_near_surface_sqrt] at h_near_surface
    exact h_near_surface
  have h_near_cos_normal_lower :
      (99968 : ℝ) / 100000 < Real.cos nearAxisRay.normalAngleRadians := by
    nlinarith only [h_near_cos_normal_sq, h_near_cos_normal_pos]
  have h_near_cos_normal_upper :
      Real.cos nearAxisRay.normalAngleRadians < (99969 : ℝ) / 100000 := by
    nlinarith only [h_near_cos_normal_sq, h_near_cos_normal_pos]
  have h_near_cos_transmitted_lower :
      (99919 : ℝ) / 100000 <
        Real.cos nearAxisRay.transmittedAngleRadians := by
    nlinarith only [h_near_cos_transmitted_sq, h_near_cos_transmitted_pos]
  have h_near_cos_transmitted_upper :
      Real.cos nearAxisRay.transmittedAngleRadians < (99920 : ℝ) / 100000 := by
    nlinarith only [h_near_cos_transmitted_sq, h_near_cos_transmitted_pos]
  have h_near_tan_numerator_pos :
      0 < Real.cos nearAxisRay.normalAngleRadians / 25 -
        Real.cos nearAxisRay.transmittedAngleRadians / 40 := by
    nlinarith only [h_near_cos_normal_lower, h_near_cos_transmitted_upper]
  have h_near_tan_denominator_pos :
      0 < Real.cos nearAxisRay.transmittedAngleRadians *
          Real.cos nearAxisRay.normalAngleRadians + 1 / 1000 := by
    nlinarith only [
      mul_pos h_near_cos_transmitted_pos h_near_cos_normal_pos]
  have h_near_crossing' :
      lengthValue centimeterUnitChoices nearAxisRay.axisCrossingPosition =
        lengthValue centimeterUnitChoices lens.curvatureCenterAxisPosition +
          (20 * Real.cos nearAxisRay.normalAngleRadians +
            ((1 / 2) * (Real.cos nearAxisRay.transmittedAngleRadians *
              Real.cos nearAxisRay.normalAngleRadians + 1 / 1000)) /
              (Real.cos nearAxisRay.normalAngleRadians / 25 -
                Real.cos nearAxisRay.transmittedAngleRadians / 40)) := by
    rw [h_near_height, h_near_tan, h_near_surface'] at h_near_crossing
    rw [h_near_crossing]
    field_simp [ne_of_gt h_near_tan_numerator_pos,
      ne_of_gt h_near_tan_denominator_pos]
    ring
  have h_near_fraction_lower :
      (213 : ℝ) / 4 - 20 * Real.cos nearAxisRay.normalAngleRadians <
        ((1 / 2) * (Real.cos nearAxisRay.transmittedAngleRadians *
          Real.cos nearAxisRay.normalAngleRadians + 1 / 1000)) /
          (Real.cos nearAxisRay.normalAngleRadians / 25 -
            Real.cos nearAxisRay.transmittedAngleRadians / 40) := by
    apply (lt_div_iff₀ h_near_tan_numerator_pos).2
    nlinarith only [h_near_cos_normal_sq, h_near_cos_normal_upper,
      h_near_cos_transmitted_lower]
  have h_near_offset_lower :
      (213 : ℝ) / 4 <
        20 * Real.cos nearAxisRay.normalAngleRadians +
          ((1 / 2) * (Real.cos nearAxisRay.transmittedAngleRadians *
            Real.cos nearAxisRay.normalAngleRadians + 1 / 1000)) /
            (Real.cos nearAxisRay.normalAngleRadians / 25 -
              Real.cos nearAxisRay.transmittedAngleRadians / 40) := by
    linarith only [h_near_fraction_lower]
  have h_near_fraction_upper :
      ((1 / 2) * (Real.cos nearAxisRay.transmittedAngleRadians *
        Real.cos nearAxisRay.normalAngleRadians + 1 / 1000)) /
          (Real.cos nearAxisRay.normalAngleRadians / 25 -
            Real.cos nearAxisRay.transmittedAngleRadians / 40) <
        (1067 : ℝ) / 20 -
          20 * Real.cos nearAxisRay.normalAngleRadians := by
    apply (div_lt_iff₀ h_near_tan_numerator_pos).2
    nlinarith only [h_near_cos_normal_sq, h_near_cos_normal_lower,
      h_near_cos_transmitted_upper]
  have h_near_offset_upper :
      20 * Real.cos nearAxisRay.normalAngleRadians +
          ((1 / 2) * (Real.cos nearAxisRay.transmittedAngleRadians *
            Real.cos nearAxisRay.normalAngleRadians + 1 / 1000)) /
            (Real.cos nearAxisRay.normalAngleRadians / 25 -
              Real.cos nearAxisRay.transmittedAngleRadians / 40) <
        (1067 : ℝ) / 20 := by
    linarith only [h_near_fraction_upper]
  simp only [axisCrossingSeparationCm, centimeterValue]
  rw [h_near_crossing', h_edge_axis_crossing]
  have h_crossing_difference_pos :
      0 <
        (lengthValue centimeterUnitChoices lens.curvatureCenterAxisPosition +
            (20 * Real.cos nearAxisRay.normalAngleRadians +
              ((1 / 2) * (Real.cos nearAxisRay.transmittedAngleRadians *
                Real.cos nearAxisRay.normalAngleRadians + 1 / 1000)) /
                (Real.cos nearAxisRay.normalAngleRadians / 25 -
                  Real.cos nearAxisRay.transmittedAngleRadians / 40))) -
          (lengthValue centimeterUnitChoices lens.curvatureCenterAxisPosition + 32) := by
    nlinarith only [h_near_offset_lower]
  rw [abs_of_pos h_crossing_difference_pos, abs_lt]
  constructor <;>
    nlinarith only [h_near_offset_lower, h_near_offset_upper]

end PhyXMiniProblems.ProblemPhyXMini0028
