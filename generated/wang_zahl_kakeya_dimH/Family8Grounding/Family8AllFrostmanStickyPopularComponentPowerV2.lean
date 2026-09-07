import Family8Grounding.Family8StickyParentPopularCanonicalUnionV1
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllFrostmanStickyPopularComponentPowerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickyParentPopularCanonicalUnionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Componentwise power budget for the Sticky popular-row union route

The popular-row theorem's explicit loss is separated here into the three
genuine quantities an upstream Sticky/dividing-scale construction must
bound: the largest fine fibre, the number of active parents, and the actual
Katz--Tao constant.  The geometric parent-hull bound is automatic, and its
fixed factor `4 * 512 = 2048` is absorbed at an explicit small scale.

V1 was a failed syntax/algebra draft and is deliberately not imported.
-/

def stickyPopularComponentPowerThreshold (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 2048 absorbExponent

theorem stickyPopularComponentPowerThreshold_pos (absorbExponent : Real) :
    0 < stickyPopularComponentPowerThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos 2048 absorbExponent

theorem stickyPopularFineSquareFactor_le_of_componentPowers
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrhoOne : rho <= 1)
    (fiberCap : Nat) (katzTaoError : ENNReal)
    {fiberExponent parentExponent katzTaoExponent absorbExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaThreshold :
      delta <= stickyPopularComponentPowerThreshold absorbExponent)
    (hfiber : (fiberCap : ENNReal) <=
      (delta : ENNReal) ^ (-fiberExponent))
    (hparent :
      (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) <=
        (delta : ENNReal) ^ (-parentExponent))
    (hKT : katzTaoError <=
      (delta : ENNReal) ^ (-katzTaoExponent)) :
    stickyPopularFineSquareFactor S fiberCap katzTaoError <=
      (delta : ENNReal) ^
        (-(2 * fiberExponent + parentExponent + katzTaoExponent +
          absorbExponent)) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hconstant : (2048 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent) := by
    exact finiteConstant_le_delta_negativePower
      (K := (2048 : ENNReal)) (by norm_num) habsorbExponent hD.delta_pos
        (by simpa only [stickyPopularComponentPowerThreshold] using
          hdeltaThreshold)
  have hhull :=
    volume_fullFamilyHullContainer_activeCoarseFamily_le_512
      D hD S hrhoOne
  have hfiberSq : (fiberCap : ENNReal) ^ 2 <=
      ((delta : ENNReal) ^ (-fiberExponent)) ^ 2 := by
    exact pow_le_pow_left' hfiber 2
  calc
    stickyPopularFineSquareFactor S fiberCap katzTaoError <=
        ((delta : ENNReal) ^ (-fiberExponent)) ^ 2 *
          (4 * (delta : ENNReal) ^ (-parentExponent) *
            (delta : ENNReal) ^ (-katzTaoExponent) * 512) := by
      unfold stickyPopularFineSquareFactor
      exact mul_le_mul' hfiberSq
        (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hparent) hKT) hhull)
    _ = 2048 *
        (((delta : ENNReal) ^ (-fiberExponent)) ^ 2 *
          ((delta : ENNReal) ^ (-parentExponent) *
            (delta : ENNReal) ^ (-katzTaoExponent))) := by ring
    _ <= (delta : ENNReal) ^ (-absorbExponent) *
        (((delta : ENNReal) ^ (-fiberExponent)) ^ 2 *
          ((delta : ENNReal) ^ (-parentExponent) *
            (delta : ENNReal) ^ (-katzTaoExponent))) := by
      exact mul_le_mul' hconstant le_rfl
    _ = (delta : ENNReal) ^
        (-(2 * fiberExponent + parentExponent + katzTaoExponent +
          absorbExponent)) := by
      rw [← ENNReal.rpow_natCast
          ((delta : ENNReal) ^ (-fiberExponent)) 2,
        ← ENNReal.rpow_mul,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

theorem allFrostman_unionLower_of_stickyPopularComponentPowers
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {eta gamma fiberExponent parentExponent katzTaoExponent
      absorbExponent : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (hactive :
      (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (fiberCap : Nat)
    (hfiberCard : forall k :
      {k // k ∈ (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k).card <= fiberCap)
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaThreshold :
      delta <= stickyPopularComponentPowerThreshold absorbExponent)
    (hfiberPower : (fiberCap : ENNReal) <=
      (delta : ENNReal) ^ (-fiberExponent))
    (hparentPower :
      (Fintype.card {k // k ∈
          (cover.cover rho hdeltaRho hrhoOne).activeCoarse} : ENNReal) <=
        (delta : ENNReal) ^ (-parentExponent))
    (hKatzTaoPower : katzTaoError <=
      (delta : ENNReal) ^ (-katzTaoExponent))
    (hexponent :
      4 * eta +
        (2 * fiberExponent + parentExponent + katzTaoExponent +
          absorbExponent) <= gamma / 2) :
    (delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion := by
  apply allFrostman_unionLower_of_stickyPopularSquareFactor
    D hD hF cover hsticky rho hdeltaRho hrhoOne hactive fiberCap
      hfiberCard hexponent
  exact stickyPopularFineSquareFactor_le_of_componentPowers
    D hD (cover.cover rho hdeltaRho hrhoOne) hrhoOne fiberCap
      katzTaoError habsorbExponent hdeltaThreshold hfiberPower
        hparentPower hKatzTaoPower

#print axioms stickyPopularComponentPowerThreshold_pos
#print axioms stickyPopularFineSquareFactor_le_of_componentPowers
#print axioms allFrostman_unionLower_of_stickyPopularComponentPowers

end

end Family8AllFrostmanStickyPopularComponentPowerV2
