import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32HardRectangleTangencyV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32HardScaleComparisonV1

/-!
# Converting curvature scales to the cinematic separation scale

Provenance: the hard-regime constant comparison in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.9.  Here `T` is the curve-separation scale,
`kappa >= c*T`, and `M <= C*T`.
-/

/-- The hard critical-product estimate converts to the separation scale
under explicit lower/upper curvature comparability. -/
theorem hard_critical_product_to_separation_scale
    {delta rho Delta M kappa c C T : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hT : 0 < T)
    (hc : 0 < c)
    (hcurvatureLowerScale : c * T <= kappa)
    (hcurvatureUpperScale : M <= C * T)
    (hproduct :
      (Delta - delta) * kappa ^ 2 <= 4 * delta * M * rho)
    (hgap : delta <= Delta) :
    c ^ 2 * (Delta - delta) * T <= 4 * C * delta * rho := by
  have hctNonneg : 0 <= c * T :=
    mul_nonneg (le_of_lt hc) (le_of_lt hT)
  have hkappaNonneg : 0 <= kappa :=
    hctNonneg.trans hcurvatureLowerScale
  have hcurvatureSq : (c * T) ^ 2 <= kappa ^ 2 :=
    (sq_le_sq₀ hctNonneg hkappaNonneg).2 hcurvatureLowerScale
  have hgapNonneg : 0 <= Delta - delta := sub_nonneg.2 hgap
  have hMcomparison : 4 * delta * M * rho <=
      4 * delta * (C * T) * rho := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcurvatureUpperScale
        (mul_nonneg (by norm_num) (le_of_lt hdelta)))
      (le_of_lt hrho)
  have hscaled :
      T * (c ^ 2 * (Delta - delta) * T) <=
        T * (4 * C * delta * rho) := by
    calc
      T * (c ^ 2 * (Delta - delta) * T) =
          (Delta - delta) * (c * T) ^ 2 := by ring
      _ <= (Delta - delta) * kappa ^ 2 :=
        mul_le_mul_of_nonneg_left hcurvatureSq hgapNonneg
      _ <= 4 * delta * M * rho := hproduct
      _ <= 4 * delta * (C * T) * rho := hMcomparison
      _ = T * (4 * C * delta * rho) := by ring
  exact le_of_mul_le_mul_left hscaled hT

/-- If the hard regime has the explicit slack `3*delta <= Delta`, then
`Delta + delta <= 2*(Delta-delta)`, yielding the standard Lemma 3.9
tangency product with constant `8*C/c^2`. -/
theorem hard_critical_product_to_tangency_product
    {delta rho Delta M kappa c C T : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hT : 0 < T)
    (hc : 0 < c)
    (hcurvatureLowerScale : c * T <= kappa)
    (hcurvatureUpperScale : M <= C * T)
    (hproduct :
      (Delta - delta) * kappa ^ 2 <= 4 * delta * M * rho)
    (hsmall : 3 * delta <= Delta) :
    c ^ 2 * (Delta + delta) * T <= 8 * C * delta * rho := by
  have hbase := hard_critical_product_to_separation_scale
    hdelta hrho hT hc hcurvatureLowerScale hcurvatureUpperScale
    hproduct (by linarith)
  have hcompare : Delta + delta <= 2 * (Delta - delta) := by
    linarith
  calc
    c ^ 2 * (Delta + delta) * T <=
        c ^ 2 * (2 * (Delta - delta)) * T := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcompare (sq_nonneg c))
        (le_of_lt hT)
    _ = 2 * (c ^ 2 * (Delta - delta) * T) := by ring
    _ <= 2 * (4 * C * delta * rho) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = 8 * C * delta * rho := by ring

#print axioms hard_critical_product_to_separation_scale
#print axioms hard_critical_product_to_tangency_product

end FamilyStickyCinematicL32HardScaleComparisonV1
