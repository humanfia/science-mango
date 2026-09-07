import Family8Grounding.Family8FiniteRandomRigidMotionPaperTubeSlabGeometryV1

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix

namespace Family8FiniteRandomRigidMotionPaperTubeOverlapUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Family8FiniteRandomRigidMotionPaperTubeSlabGeometryV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# The paper-scale tube overlap upper bound

The three thin slab normals from `PaperTubeSlabGeometryV1` give a coordinate
window of determinant `sin(angle)` and three full widths `2 rho`.  The exact
Jacobian formula therefore proves the cross-multiplied estimate used by the
random rigid-motion conflict argument, including the parallel case.
-/

/-- Positive transversality gives the explicit reciprocal-sine ENNReal
overlap bound. -/
theorem volume_inter_carrier_le_inv_sin_mul_eight_rho_cubed
    {rho : NNReal} (T U : Tube rho)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction)) :
    volume (T.carrier ∩ U.carrier) ≤
      ENNReal.ofReal ((Real.sin (InnerProductGeometry.angle
        T.axis.direction U.axis.direction))⁻¹) *
        (2 * (rho : ENNReal)) * (2 * (rho : ENNReal)) *
          (2 * (rho : ENNReal)) := by
  let e := commonTubeNormal T U
  let nT := leftTubeNormal T U
  let nU := rightTubeNormal T U
  let cE : Real :=
    ⟪e, T.axis.base + (2 : Real)⁻¹ • T.axis.direction⟫_ℝ
  let cT : Real :=
    ⟪nT, T.axis.base + (2 : Real)⁻¹ • T.axis.direction⟫_ℝ
  let cU : Real :=
    ⟪nU, U.axis.base + (2 : Real)⁻¹ • U.axis.direction⟫_ℝ
  have heSlab : T.carrier ⊆ affineSlab e cE rho := by
    exact Family8FiniteRandomRigidMotionPaperTubeSlabGeometryV1.Tube.carrier_subset_affineSlab_of_inner_direction_eq_zero T e
      (norm_commonTubeNormal T U hangle)
      (inner_commonTubeNormal_left T U)
  have hnTSlab : T.carrier ⊆ affineSlab nT cT rho := by
    exact Family8FiniteRandomRigidMotionPaperTubeSlabGeometryV1.Tube.carrier_subset_affineSlab_of_inner_direction_eq_zero T nT
      (norm_leftTubeNormal T U hangle) (inner_leftTubeNormal_axis T U)
  have hnUSlab : U.carrier ⊆ affineSlab nU cU rho := by
    exact Family8FiniteRandomRigidMotionPaperTubeSlabGeometryV1.Tube.carrier_subset_affineSlab_of_inner_direction_eq_zero U nU
      (norm_rightTubeNormal T U hangle) (inner_rightTubeNormal_axis T U)
  have hsubset :
      T.carrier ∩ U.carrier ⊆
        affineSlab e cE rho ∩ affineSlab nT cT rho ∩
          affineSlab nU cU rho := by
    rintro x ⟨hxT, hxU⟩
    exact ⟨⟨heSlab hxT, hnTSlab hxT⟩, hnUSlab hxU⟩
  have hdetAbs :
      |LinearMap.det (innerCoordinateMap ![e, nT, nU])| =
        Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) := by
    exact abs_det_common_left_right_eq_sin_angle T U hangle
  have hdet : LinearMap.det (innerCoordinateMap ![e, nT, nU]) ≠ 0 := by
    exact (abs_pos.mp (hdetAbs.symm ▸ hangle))
  calc
    volume (T.carrier ∩ U.carrier) ≤
        volume (affineSlab e cE rho ∩ affineSlab nT cT rho ∩
          affineSlab nU cU rho) := measure_mono hsubset
    _ = ENNReal.ofReal
          |(LinearMap.det (innerCoordinateMap ![e, nT, nU]))⁻¹| *
        (2 * (rho : ENNReal)) * (2 * (rho : ENNReal)) *
          (2 * (rho : ENNReal)) :=
      volume_twoSlabs_with_longitudinalCut e nT nU cE cT cU
        rho rho rho hdet
    _ = ENNReal.ofReal ((Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction))⁻¹) *
        (2 * (rho : ENNReal)) * (2 * (rho : ENNReal)) *
          (2 * (rho : ENNReal)) := by
      rw [abs_inv, hdetAbs]

/-- The reciprocal-sine estimate in the division-free real form needed by
the conflict angle algebra. -/
theorem sin_angle_mul_volume_inter_toReal_le_eight_rho_cubed
    {rho : NNReal} (T U : Tube rho) :
    Real.sin (InnerProductGeometry.angle
        T.axis.direction U.axis.direction) *
        (volume (T.carrier ∩ U.carrier)).toReal ≤
      8 * (rho : Real) ^ 3 := by
  let s := Real.sin (InnerProductGeometry.angle
    T.axis.direction U.axis.direction)
  have hsnonneg : 0 ≤ s :=
    InnerProductGeometry.sin_angle_nonneg _ _
  by_cases hs : s = 0
  · change s * (volume (T.carrier ∩ U.carrier)).toReal ≤
      8 * (rho : Real) ^ 3
    rw [hs, zero_mul]
    positivity
  have hspos : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hs)
  have hENN := volume_inter_carrier_le_inv_sin_mul_eight_rho_cubed
    T U hspos
  have hreal := ENNReal.toReal_mono (by finiteness) hENN
  have hreal' :
      (volume (T.carrier ∩ U.carrier)).toReal ≤
        s⁻¹ * (2 * (rho : Real)) * (2 * (rho : Real)) *
          (2 * (rho : Real)) := by
    simpa only [s, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (inv_nonneg.mpr hsnonneg), ENNReal.toReal_ofNat,
      ENNReal.coe_toReal] using hreal
  calc
    s * (volume (T.carrier ∩ U.carrier)).toReal ≤
        s * (s⁻¹ * (2 * (rho : Real)) * (2 * (rho : Real)) *
          (2 * (rho : Real))) := mul_le_mul_of_nonneg_left hreal' hsnonneg
    _ = 8 * (rho : Real) ^ 3 := by
      field_simp [ne_of_gt hspos]
      ring

#print axioms volume_inter_carrier_le_inv_sin_mul_eight_rho_cubed
#print axioms sin_angle_mul_volume_inter_toReal_le_eight_rho_cubed

end
end Family8FiniteRandomRigidMotionPaperTubeOverlapUpperV1
