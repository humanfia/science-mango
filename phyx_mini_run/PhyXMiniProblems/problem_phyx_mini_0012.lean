import Mathlib
import Physlib.Units.WithDim.Basic

/- The figure's `R` is the outside bend radius.  The fiber therefore
occupies the annular region between radii `R - d` and `R`. -/

namespace PhyXMini0012

/-- A nonnegative length readout carrying Physlib's physical length dimension. -/
abbrev FiberLength := WithDim Dimension.L𝓭 NNReal

/-- The material and geometric data of the vacuum-clad optical fiber. -/
structure BentOpticalFiber where
  /-- The dimensionless refractive index `n` of the fiber core. -/
  coreRefractiveIndex : NNReal
  /-- The dimensionless refractive index of the surrounding medium. -/
  surroundingRefractiveIndex : NNReal
  /-- The physical fiber diameter `d`, also the radial thickness in the figure. -/
  diameter : FiberLength

/--
The least information about the axial family of geometrical-optics rays needed
to discuss confinement in a bend.  At a proposed outside radius, the limiting
ray is the axial ray having the smallest incidence angle at the outer wall.
-/
structure AxialRayConfinementModel where
  /-- Sine of the limiting ray's incidence angle, measured from the wall normal. -/
  limitingIncidenceSineAtOuterWall : FiberLength → NNReal
  /-- Whether every launched axial ray remains confined at this outside radius. -/
  noLightEscapesAt : FiberLength → Prop

/--
For a fiber of core index `n` and diameter `d` surrounded by vacuum, the least
outside bend radius which confines every ray launched along the fiber axis is
`n d / (n - 1)`.

The two physical-law hypotheses are kept separate from the answer.  The figure
geometry gives the limiting incidence sine `(R - d) / R`; total internal
reflection compares it with the Snell-law critical sine `n_out / n`.
-/
theorem minimum_outside_radius
    (fiber : BentOpticalFiber)
    (model : AxialRayConfinementModel)
    (minimumOutsideRadius : FiberLength)
    (hCoreIndex : 1 < fiber.coreRefractiveIndex)
    (hVacuum : fiber.surroundingRefractiveIndex = 1)
    (hDiameter : 0 < fiber.diameter)
    (hFigureGeometry : ∀ outsideRadius : FiberLength,
      fiber.diameter < outsideRadius →
        model.limitingIncidenceSineAtOuterWall outsideRadius =
          (outsideRadius.val - fiber.diameter.val) / outsideRadius.val)
    (hTotalInternalReflection : ∀ outsideRadius : FiberLength,
      fiber.diameter < outsideRadius →
        (model.noLightEscapesAt outsideRadius ↔
          fiber.surroundingRefractiveIndex / fiber.coreRefractiveIndex ≤
            model.limitingIncidenceSineAtOuterWall outsideRadius))
    (hMinimum : IsLeast
      {outsideRadius : FiberLength |
        fiber.diameter < outsideRadius ∧ model.noLightEscapesAt outsideRadius}
      minimumOutsideRadius) :
    minimumOutsideRadius =
      (fiber.coreRefractiveIndex / (fiber.coreRefractiveIndex - 1)) •
        fiber.diameter := by
  let n := fiber.coreRefractiveIndex
  let d := fiber.diameter.val
  let r := minimumOutsideRadius.val
  have hn : 0 < n := lt_trans (by norm_num) hCoreIndex
  have hn1 : 0 < n - 1 := tsub_pos_iff_lt.mpr hCoreIndex
  have hd : 0 < d := hDiameter
  have hone_le_n : (1 : NNReal) ≤ n := le_of_lt hCoreIndex
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCoreR : (1 : ℝ) < n := by exact_mod_cast hCoreIndex
  have hn1R : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfactor : 1 < n / (n - 1) := by
    apply (lt_div_iff₀ hn1).2
    simpa using tsub_lt_self hn (by norm_num : (0 : NNReal) < 1)
  have hcand_gt : fiber.diameter < (n / (n - 1)) • fiber.diameter := by
    change d < (n / (n - 1)) * d
    rw [← NNReal.coe_lt_coe]
    simp only [NNReal.coe_mul]
    have hfR : (1 : ℝ) < (n / (n - 1) : NNReal) := by
      exact_mod_cast hfactor
    simpa only [one_mul] using mul_lt_mul_of_pos_right hfR hdR
  have hdcand : d ≤ n / (n - 1) * d := by
    exact le_of_lt hcand_gt
  have hcand_conf :
      model.noLightEscapesAt ((n / (n - 1)) • fiber.diameter) := by
    apply (hTotalInternalReflection _ hcand_gt).2
    rw [hVacuum, hFigureGeometry _ hcand_gt]
    apply le_of_eq
    change 1 / n = ((n / (n - 1) * d) - d) / (n / (n - 1) * d)
    ext
    push_cast [hone_le_n, hdcand]
    field_simp [ne_of_gt hnR, ne_of_gt hn1R, ne_of_gt hdR]
    ring
  have hmin_gt : fiber.diameter < minimumOutsideRadius := hMinimum.1.1
  have hdr : d ≤ r := le_of_lt hmin_gt
  have hr : 0 < r := lt_trans hd hmin_gt
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcrit : 1 / n ≤ (r - d) / r := by
    have h :=
      (hTotalInternalReflection minimumOutsideRadius hmin_gt).1 hMinimum.1.2
    rw [hVacuum, hFigureGeometry minimumOutsideRadius hmin_gt] at h
    exact h
  rw [← NNReal.coe_le_coe] at hcrit
  push_cast [hdr] at hcrit
  field_simp [ne_of_gt hnR, ne_of_gt hrR] at hcrit
  have hlower : n / (n - 1) * d ≤ r := by
    rw [← NNReal.coe_le_coe]
    push_cast [hone_le_n]
    field_simp [ne_of_gt hn1R]
    nlinarith
  apply le_antisymm
  · exact hMinimum.2 ⟨hcand_gt, hcand_conf⟩
  · exact hlower

end PhyXMini0012
