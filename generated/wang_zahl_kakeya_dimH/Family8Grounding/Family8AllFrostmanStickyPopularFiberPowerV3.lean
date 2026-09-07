import Family8Grounding.Family8KatzTaoDoubledFiberActiveIndexCapV3
import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllFrostmanStickyPopularFiberPowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoDoubledFiberActiveIndexCapV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV7
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open Family8KatzTaoSamplingMultiplicityV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# An actual source-Katz--Tao producer for the popular fine-fibre power

V1 and V2 were failed elaboration drafts and are deliberately not imported.
For an actual scale cover, source Katz--Tao bounds every active parent fibre
by the literal natural ceiling `katzTaoDoubledFiberNatCap`.  This module
removes that ceiling and absorbs its fixed coefficient.  The remaining
scale input is the honest normalized-radius inequality
`rho^2 / (delta^2 / 2) <= 2 * delta^(-2 * scaleLoss)`.
-/

theorem activeIndexFiber_card_and_power_le_of_katzTaoHypotheses
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    {etaKT scaleLoss absorbExponent : Real}
    (hEtaKT : 0 < etaKT)
    (hKT : KatzTaoHypotheses D etaKT)
    (hscale :
      (rho : ENNReal) ^ 2 / ((delta : ENNReal) ^ 2 / 2) <=
        2 * (delta : ENNReal) ^ (-2 * scaleLoss))
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaThreshold :
      delta <= ordinaryFiberNatCapSmallDeltaThreshold absorbExponent) :
    let M := katzTaoDoubledFiberNatCap delta rho
      ((delta : ENNReal) ^ (-etaKT))
    (forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <= M) ∧
    (M : ENNReal) <= (delta : ENNReal) ^
      (-ordinaryFiberPowerEnvelope scaleLoss etaKT absorbExponent) := by
  let A : ENNReal := (delta : ENNReal) ^ (-etaKT)
  let M := katzTaoDoubledFiberNatCap delta rho A
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hAfinite : A ≠ ∞ := by
    dsimp only [A]
    exact ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top
  have hdeltaOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast (hD.delta_le_half.trans (by norm_num))
  have hAone : 1 <= A := by
    dsimp only [A]
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hD.delta_pos) hdeltaOneENN (by linarith)
  have hsourceKT : IsKatzTao A D.family.bodyFamily := by
    dsimp only [A]
    exact
      ((katzTaoHypotheses_iff_density_and_isKatzTao D etaKT).mp hKT).2
  have hfiber : forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <= M := by
    dsimp only [M]
    exact StickyScaleCover.activeIndexFiber_card_le_katzTaoDoubledFiberNatCap
      S hD.delta_pos hD.delta_le_half hrhoOne hAfinite hsourceKT
  have hratioOne : 1 <=
      activeOwnerKatzTaoIncidenceRatio delta rho A :=
    one_le_activeOwnerKatzTaoIncidenceRatio
      hD.delta_pos hdeltaRho hAone
  have hratioFinite :
      activeOwnerKatzTaoIncidenceRatio delta rho A ≠ ∞ :=
    activeOwnerKatzTaoIncidenceRatio_ne_top hD.delta_pos hAfinite
  have hratioPower :
      activeOwnerKatzTaoIncidenceRatio delta rho A <=
        480000 * (delta : ENNReal) ^ (-(etaKT + 2 * scaleLoss)) := by
    exact activeOwnerKatzTaoIncidenceRatio_le_longIntervalPower
      hD.delta_pos (by exact le_rfl) hscale
  have hcap : (M : ENNReal) <=
      2 * activeOwnerKatzTaoIncidenceRatio delta rho A := by
    dsimp only [M]
    rw [katzTaoDoubledFiberNatCap_eq_samplingMultiplicity]
    exact katzTaoSamplingMultiplicity_coe_le_two_mul
      hratioOne hratioFinite
  have hfixed : (M : ENNReal) <=
      ordinaryFiberNatCapFixedConstant *
        (delta : ENNReal) ^ (-(etaKT + 2 * scaleLoss)) := by
    calc
      (M : ENNReal) <=
          2 * activeOwnerKatzTaoIncidenceRatio delta rho A := hcap
      _ <= 2 *
          (480000 * (delta : ENNReal) ^
            (-(etaKT + 2 * scaleLoss))) :=
        mul_le_mul' le_rfl hratioPower
      _ = ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-(etaKT + 2 * scaleLoss)) := by
        unfold ordinaryFiberNatCapFixedConstant
        ring
  refine ⟨hfiber, hfixed.trans ?_⟩
  simpa only [ordinaryFiberPowerEnvelope] using
    (ordinaryFiberNatCapFixedPower_le_absorbedPower
      (p := etaKT + 2 * scaleLoss) hD.delta_pos habsorbExponent
        hdeltaThreshold)

#print axioms activeIndexFiber_card_and_power_le_of_katzTaoHypotheses

end

end Family8AllFrostmanStickyPopularFiberPowerV3
