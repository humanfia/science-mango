import Family8Grounding.Family8StickyFiberContractedJohnSourcePowerEndpointV1
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnRelativePowerEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Official relative-scale contracted-John first-factor endpoint

The literal normalized proxy radius is `(3/64) * (delta/rho)`.  This module
uses that exact identity to rewrite both scalar power budgets at the official
relative scale.  The density comparison depends only on the nonnegative gap
`eta - (p + a)`.  The base comparison retains the exact fixed `3/64`
coefficients, so no scale-dependent loss is hidden.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Relative-scale source density and fibre-cardinality power comparisons
produce the same genuine selected Frostman endpoint as the literal proxy
scale theorem. -/
theorem exists_stickyFiberContractedJohn_global_average_le_relativePower_frostmanRHS
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse})
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hp : 0 < p) (ha : 0 < a)
    (hgap : 0 <= eta - (p + a))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hsmallRatio : delta / rho <=
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : C <=
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    (hsourceDensityRatio :
      (((delta : ENNReal) / (rho : ENNReal)) ^ (eta - (p + a))) <=
        (stickyFiberSourceShading S Y k.1).shadingDensity / 93312 / 128)
    (hbaseRatio :
      (3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 * p + a))) <=
        ((3 / 64 : ENNReal) ^ (-eta) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta))) *
          ((Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) *
            (((3 / 64 : ENNReal) ^ 2 *
                (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2))) :
    exists selected : Finset {i // i ∈ S.fiber k.1},
      selected.Nonempty ∧
      (stickyFiberSourceShading S Y k.1).averageMultiplicity <=
        stickyFiberContractedJohnSourceClosedLoss C *
          frostmanMultiplicityRHS
            (contractedJohnProxyRadius delta rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (stickyFiberContractedJohnProxyDatum
                  S Y hrho hrhoOne k)) selected).actualFamilyVolume
            epsilon beta := by
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  let ratio : ENNReal := (delta : ENNReal) / (rho : ENNReal)
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hscale0 : (scale : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hscalePos.ne'
  have hscaleTop : (scale : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hfixedNN : (3 / 64 : NNReal) <= 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  have hsmall : scale <= contractedJohnSourcePowerEndpointThreshold a := by
    calc
      scale = (3 / 64 : NNReal) * (delta / rho) :=
        contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrho
      _ <= 1 * (delta / rho) := mul_le_mul' hfixedNN le_rfl
      _ = delta / rho := one_mul _
      _ <= contractedJohnSourcePowerEndpointThreshold a := hsmallRatio
  have hfixedPos : 0 < (3 / 64 : ENNReal) := by norm_num
  have hfixedOne : (3 / 64 : ENNReal) <= 1 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num
  have hfixedNegative : 1 <= (3 / 64 : ENNReal) ^ (-p) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      hfixedPos hfixedOne (by linarith)
  have hCscale : C <= (scale : ENNReal) ^ (-p) := by
    calc
      C <= ratio ^ (-p) := by simpa only [ratio] using hCratio
      _ = 1 * ratio ^ (-p) := by rw [one_mul]
      _ <= (3 / 64 : ENNReal) ^ (-p) * ratio ^ (-p) :=
        mul_le_mul' hfixedNegative le_rfl
      _ = (scale : ENNReal) ^ (-p) := by
        simpa only [scale, ratio] using
          (contractedJohnProxyRadius_div_eight_rpow_eq
            (delta := delta) hrho (-p)).symm
  have hdensity :
      (scale : ENNReal) ^ eta <=
        ((stickyFiberSourceShading S Y k.1).shadingDensity / 93312 / 128) /
          (scale : ENNReal) ^ (-(p + a)) := by
    have hdenPos : 0 < (scale : ENNReal) ^ (-(p + a)) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hscalePos) ENNReal.coe_ne_top
    have hdenTop : (scale : ENNReal) ^ (-(p + a)) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_ne_zero hscale0 hscaleTop
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hdenPos.ne') (Or.inl hdenTop)).2
    calc
      (scale : ENNReal) ^ eta * (scale : ENNReal) ^ (-(p + a)) =
          (scale : ENNReal) ^ (eta - (p + a)) := by
        rw [← ENNReal.rpow_add _ _ hscale0 hscaleTop]
        congr 1
      _ <= ratio ^ (eta - (p + a)) := by
        simpa only [scale, ratio] using
          contractedJohnProxyRadius_div_eight_rpow_le_ratio_rpow
            (delta := delta) hrho hgap
      _ <= (stickyFiberSourceShading S Y k.1).shadingDensity / 93312 / 128 := by
        simpa only [ratio] using hsourceDensityRatio
  have hbase :
      (scale : ENNReal) ^ (-(2 * p + a)) <=
        (scale : ENNReal) ^ (-eta) *
          ((Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) *
            ((scale : ENNReal) ^ 2 / 2)) := by
    rw [show (scale : ENNReal) ^ (-(2 * p + a)) =
        (3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          ratio ^ (-(2 * p + a)) by
      simpa only [scale, ratio] using
        contractedJohnProxyRadius_div_eight_rpow_eq
          (delta := delta) hrho (-(2 * p + a))]
    rw [show (scale : ENNReal) ^ (-eta) =
        (3 / 64 : ENNReal) ^ (-eta) * ratio ^ (-eta) by
      simpa only [scale, ratio] using
        contractedJohnProxyRadius_div_eight_rpow_eq
          (delta := delta) hrho (-eta)]
    rw [show (scale : ENNReal) ^ 2 =
        (3 / 64 : ENNReal) ^ 2 * ratio ^ 2 by
      rw [show (scale : ENNReal) = (3 / 64 : ENNReal) * ratio by
        simpa only [scale, ratio] using
          coe_contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
            (delta := delta) hrho]
      ring]
    simpa only [ratio] using hbaseRatio
  exact
    exists_stickyFiberContractedJohn_global_average_le_sourcePower_frostmanRHS
      hF S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho k hKT hp ha
        hdelta0 hsmall hCscale (by simpa only [scale] using hdensity)
        (by simpa only [scale] using hbase)

#print axioms
  exists_stickyFiberContractedJohn_global_average_le_relativePower_frostmanRHS

end
end Family8StickyFiberContractedJohnRelativePowerEndpointV1
