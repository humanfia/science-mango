import Family8Grounding.Family8Family7FirstCrossingFullCoefficientExactOuterMiddleStructuralBundleV13
import Family8Grounding.Family8ContractedJohnMiddleCardScaleAlgebraV3
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

/-!
# Direct identity-singleton middle bound on the same exact-outer assembly

This successor avoids the graph-bucket loss altogether.  The final shading
over the certificate's literal parent has point multiplicity bounded by the
cardinality of that factorization fibre.  At the endpoint identity cover the
fibre has at most one member, so its average multiplicity is at most one.
The source-retention and same-product fields then give the triple with middle
average `sourceLoss * 4`, on the same `A` and `k` as the Family7 certificate.

There is no critical-ball proxy, new graph, greedy selection, Frostman input,
or proxy-scale `delta0` premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnMiddleCardScaleAlgebraV3
open Family8Family7FirstCrossingFullCoefficientExactOuterMiddleStructuralBundleV13
open Family8FrostmanOneFromPointwisePackingV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- A natural cardinality cap on the literal factorization fibre bounds the
average multiplicity of the final fibre shading. -/
theorem finalFiberShading_averageMultiplicity_le_fiberCard
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real} (A : Assembly P Y r)
    (k : Fin T.coarseCard) :
    (finalFiberShading A k).averageMultiplicity ≤
      ((P.index.fiber k).card : ENNReal) := by
  apply averageMultiplicity_le_natCap_of_pointwise_le
  intro x
  rw [finalFiberShading_pointMultiplicity]
  exact
    Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly.fiberMultiplicity_le_fiber_card
      P A.refinement.shading k x

/-- On a singleton factorization fibre, the exact-outer source triple uses
middle average `sourceLoss * 4`; the graph-bucket loss is absent. -/
theorem FirstCrossingExactOuterMiddleStructuralBundle.identitySingleton_triple
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real} (A : Assembly P Y r)
    (k : Fin T.coarseCard) (axis : Fin 3) (label : Int)
    (CF d graphLoss sourceLoss sourceAverage : ENNReal)
    (B : FirstCrossingExactOuterMiddleStructuralBundle
      F T P Y A k axis label CF d graphLoss sourceLoss sourceAverage)
    (hfiber : (P.index.fiber k).card ≤ 1) :
    sourceAverage ≤
      1 * ((sourceLoss * 4) * A.frozenCoarse.averageMultiplicity) := by
  have hfinalCard :=
    finalFiberShading_averageMultiplicity_le_fiberCard F T P Y A k
  have hcardOne : ((P.index.fiber k).card : ENNReal) ≤ 1 := by
    exact_mod_cast hfiber
  have hfinalOne :
      (finalFiberShading A k).averageMultiplicity ≤ 1 :=
    hfinalCard.trans hcardOne
  calc
    sourceAverage ≤
        sourceLoss * (actualRefinementShading A).averageMultiplicity :=
      B.source_retention
    _ ≤ sourceLoss *
        (4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity)) :=
      mul_le_mul' le_rfl B.certificate.same_product
    _ ≤ sourceLoss *
        (4 * (A.frozenCoarse.averageMultiplicity * 1)) :=
      mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hfinalOne))
    _ = 1 * ((sourceLoss * 4) *
        A.frozenCoarse.averageMultiplicity) := by
      ac_rfl

/-- The singleton relative-scale gain absorbs one honest source-loss power.
No graph or proxy coefficient appears. -/
theorem sourceLoss_four_le_globalPower_mul_sectionEight_singleton
    {globalDelta fineScale coarseScale : NNReal}
    {sourceLoss : ENNReal}
    {gamma globalEta ratioExp lossExp : Real}
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hfine : 0 < fineScale) (hcoarse : 0 < coarseScale)
    (hgammaTwo : gamma ≤ 2)
    (hgain : 0 < 3 * gamma - 2)
    (hratio : (fineScale : ENNReal) / (coarseScale : ENNReal) ≤
      (globalDelta : ENNReal) ^ ratioExp)
    (houter : sourceLoss * 4 ≤
      (globalDelta : ENNReal) ^ (-lossExp))
    (hbudget : 10 * globalEta + lossExp ≤
      ratioExp * (3 * gamma - 2)) :
    sourceLoss * 4 ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          fineScale coarseScale 1 gamma := by
  let d : ENNReal := globalDelta
  let q : ENNReal :=
    (fineScale : ENNReal) / (coarseScale : ENNReal)
  let gain : Real := 3 * gamma - 2
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hglobal.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d ≤ 1 := by
    simpa only [d] using
      (show (globalDelta : ENNReal) ≤ 1 by exact_mod_cast hglobalOne)
  have hratio' : q ≤ d ^ ratioExp := by
    simpa only [q, d] using hratio
  have hratioPower : q ^ gain ≤ (d ^ ratioExp) ^ gain :=
    ENNReal.rpow_le_rpow hratio' (by simpa only [gain] using hgain.le)
  have hnegativeGain : d ^ (-(ratioExp * gain)) ≤ q ^ (-gain) := by
    calc
      d ^ (-(ratioExp * gain)) = ((d ^ ratioExp) ^ gain)⁻¹ := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_mul]
      _ ≤ (q ^ gain)⁻¹ := ENNReal.inv_le_inv' hratioPower
      _ = q ^ (-gain) := by rw [ENNReal.rpow_neg]
  have hexponent : 10 * globalEta - ratioExp * gain ≤ -lossExp := by
    dsimp only [gain]
    linarith
  have hcombine : d ^ (-lossExp) ≤
      d ^ (10 * globalEta) * q ^ (-gain) := by
    calc
      d ^ (-lossExp) ≤ d ^ (10 * globalEta - ratioExp * gain) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdOne hexponent
      _ = d ^ (10 * globalEta) * d ^ (-(ratioExp * gain)) := by
        rw [show 10 * globalEta - ratioExp * gain =
            10 * globalEta + -(ratioExp * gain) by ring,
          ENNReal.rpow_add _ _ hd0 hdTop]
      _ ≤ d ^ (10 * globalEta) * q ^ (-gain) :=
        mul_le_mul' le_rfl hnegativeGain
  calc
    sourceLoss * 4 ≤ d ^ (-lossExp) := by simpa only [d] using houter
    _ ≤ d ^ (10 * globalEta) * q ^ (-gain) := hcombine
    _ = (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          fineScale coarseScale 1 gamma := by
      rw [sectionEightScaleCountFrostmanFactor_eq_ratio_count
        hfine hcoarse hgammaTwo]
      simp only [Nat.cast_one, ENNReal.one_rpow, mul_one]
      dsimp only [d, q, gain]
      congr 2
      ring

/-- Same-object identity-singleton middle fields.  The count is literally
one and the average is `sourceLoss * 4`. -/
theorem FirstCrossingExactOuterMiddleStructuralBundle.identitySingleton_fields
    {tau rho globalDelta : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real} (A : Assembly P Y r)
    (k : Fin T.coarseCard) (axis : Fin 3) (label : Int)
    (CF d graphLoss sourceLoss sourceAverage : ENNReal)
    (B : FirstCrossingExactOuterMiddleStructuralBundle
      F T P Y A k axis label CF d graphLoss sourceLoss sourceAverage)
    (hfiber : (P.index.fiber k).card ≤ 1)
    {gamma globalEta ratioExp lossExp : Real}
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (htau : 0 < tau) (hrho : 0 < rho)
    (hgammaTwo : gamma ≤ 2)
    (hgain : 0 < 3 * gamma - 2)
    (hratio : (tau : ENNReal) / (rho : ENNReal) ≤
      (globalDelta : ENNReal) ^ ratioExp)
    (houter : sourceLoss * 4 ≤
      (globalDelta : ENNReal) ^ (-lossExp))
    (hbudget : 10 * globalEta + lossExp ≤
      ratioExp * (3 * gamma - 2)) :
    sourceAverage ≤
        1 * ((sourceLoss * 4) * A.frozenCoarse.averageMultiplicity) ∧
      sourceLoss * 4 ≤
        (globalDelta : ENNReal) ^ (10 * globalEta) *
          sectionEightScaleCountFrostmanFactor tau rho 1 gamma := by
  constructor
  · exact Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6.FirstCrossingExactOuterMiddleStructuralBundle.identitySingleton_triple F T P Y A k axis label
      CF d graphLoss sourceLoss sourceAverage B hfiber
  · exact sourceLoss_four_le_globalPower_mul_sectionEight_singleton
      hglobal hglobalOne htau hrho hgammaTwo hgain hratio houter hbudget

#print axioms finalFiberShading_averageMultiplicity_le_fiberCard
#print axioms FirstCrossingExactOuterMiddleStructuralBundle.identitySingleton_triple
#print axioms sourceLoss_four_le_globalPower_mul_sectionEight_singleton
#print axioms FirstCrossingExactOuterMiddleStructuralBundle.identitySingleton_fields

end
end Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6
