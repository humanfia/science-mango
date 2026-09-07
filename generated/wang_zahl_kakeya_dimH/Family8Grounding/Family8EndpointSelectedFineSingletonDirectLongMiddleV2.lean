import Family8Grounding.Family8ContractedJohnMiddleCardScaleAlgebraV3
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Direct LongMiddle bound on a singleton endpoint fibre, V2

V1 is a static draft and is never imported.  This successor uses Unicode
disequality throughout and records the necessary positive ratio exponent.

For an endpoint selected-fine cover whose every active fibre has cardinality
one, no low-CF selection or contracted-John base budget is needed.  Pick any
literal active parent, take the full literal fibre, and use
`averageMultiplicity <= indexCard = 1`.  The Section 8 middle factor at count
one is exactly `(fine / coarse) ^ (2 - 3 * gamma)`.  Thus the whole estimate
reduces to the displayed relative-scale gain and one finite factor-four
absorption.

The intended same-assembly instantiation is the literal
`T = activeFineRestrictedScaleCover T0`, `Z = activeFineRestrictedShading T0
Z0` attached to the endpoint `M = 1` assembly.  This theorem does not replace
that object and assumes no Katz--Tao input, low-CF certificate, base power,
active-parent count, or conclusion callback.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointSelectedFineSingletonDirectLongMiddleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ContractedJohnMiddleCardScaleAlgebraV3
open Family8FrostmanOneFromPointwisePackingV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {globalDelta fineScale coarseScale : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily fineScale index}

/-- Pure scalar singleton middle estimate.  The exact net reserve is
`ratioExp * (3 * gamma - 2) - 10 * globalEta`; `absorbExp` pays the literal
factor four. -/
theorem four_le_globalPower_mul_sectionEight_singleton
    {gamma globalEta ratioExp absorbExp : Real}
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hfine : 0 < fineScale) (hcoarse : 0 < coarseScale)
    (hgammaTwo : gamma ≤ 2)
    (hglobalEta : 0 ≤ globalEta)
    (hratioExp : 0 < ratioExp)
    (hratio : (fineScale : ENNReal) / (coarseScale : ENNReal) ≤
      (globalDelta : ENNReal) ^ ratioExp)
    (habsorb : 0 < absorbExp)
    (hbudget : 10 * globalEta + absorbExp ≤
      ratioExp * (3 * gamma - 2))
    (hsmall : globalDelta ≤
      finiteConstantSmallDeltaThreshold 4 absorbExp) :
    (4 : ENNReal) ≤
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
    change (globalDelta : ENNReal) ≤ 1
    exact_mod_cast hglobalOne
  have hratio' : q ≤ d ^ ratioExp := by
    simpa only [q, d] using hratio
  have hgain : 0 < gain := by
    dsimp only [gain]
    nlinarith [hglobalEta]
  have hratioPower : q ^ gain ≤ (d ^ ratioExp) ^ gain :=
    ENNReal.rpow_le_rpow hratio' hgain.le
  have hnegativeGain : d ^ (-(ratioExp * gain)) ≤ q ^ (-gain) := by
    calc
      d ^ (-(ratioExp * gain)) = ((d ^ ratioExp) ^ gain)⁻¹ := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_mul]
      _ ≤ (q ^ gain)⁻¹ := ENNReal.inv_le_inv' hratioPower
      _ = q ^ (-gain) := by rw [ENNReal.rpow_neg]
  have hfour : (4 : ENNReal) ≤ d ^ (-absorbExp) := by
    simpa only [d] using
      (finiteConstant_le_delta_negativePower
        (K := (4 : ENNReal)) (by norm_num) habsorb hglobal hsmall)
  have hexponent : 10 * globalEta - ratioExp * gain ≤ -absorbExp := by
    linarith
  have hcombine : d ^ (-absorbExp) ≤
      d ^ (10 * globalEta) * q ^ (-gain) := by
    calc
      d ^ (-absorbExp) ≤ d ^ (10 * globalEta - ratioExp * gain) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdOne hexponent
      _ = d ^ (10 * globalEta) * d ^ (-(ratioExp * gain)) := by
        rw [show 10 * globalEta - ratioExp * gain =
            10 * globalEta + -(ratioExp * gain) by ring,
          ENNReal.rpow_add _ _ hd0 hdTop]
      _ ≤ d ^ (10 * globalEta) * q ^ (-gain) :=
        mul_le_mul' le_rfl hnegativeGain
  calc
    (4 : ENNReal) ≤ d ^ (-absorbExp) := hfour
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

/-- On a literal fully singleton-fibred Sticky cover, one actual parent and
its full literal fibre give the LongMiddle inequality directly. -/
theorem exists_sameParent_singleton_four_mul_sourceAverage_le_longMiddle
    {gamma globalEta ratioExp absorbExp : Real}
    (S : StickyScaleCover fine coarseScale)
    (Y : Shading fine.bodyFamily)
    (hcoarseNonempty : S.activeCoarse.Nonempty)
    (hcardOne : ∀ q : {q // q ∈ S.activeCoarse},
      Fintype.card {i // i ∈ S.fiber q.1} = 1)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hfine : 0 < fineScale) (hcoarse : 0 < coarseScale)
    (hgammaTwo : gamma ≤ 2)
    (hglobalEta : 0 ≤ globalEta)
    (hratioExp : 0 < ratioExp)
    (hratio : (fineScale : ENNReal) / (coarseScale : ENNReal) ≤
      (globalDelta : ENNReal) ^ ratioExp)
    (habsorb : 0 < absorbExp)
    (hbudget : 10 * globalEta + absorbExp ≤
      ratioExp * (3 * gamma - 2))
    (hsmall : globalDelta ≤
      finiteConstantSmallDeltaThreshold 4 absorbExp) :
    ∃ q : {q // q ∈ S.activeCoarse},
      ∃ selected : Finset {i // i ∈ S.fiber q.1},
        selected.Nonempty ∧ selected.card = 1 ∧
        4 * (stickyFiberSourceShading S Y q.1).averageMultiplicity ≤
          (globalDelta : ENNReal) ^ (10 * globalEta) *
            sectionEightScaleCountFrostmanFactor
              fineScale coarseScale selected.card gamma := by
  classical
  obtain ⟨q0, hq0⟩ := hcoarseNonempty
  let q : {q // q ∈ S.activeCoarse} := ⟨q0, hq0⟩
  let selected : Finset {i // i ∈ S.fiber q.1} := Finset.univ
  have hselectedCard : selected.card = 1 := by
    simpa only [selected, Finset.card_univ] using hcardOne q
  have hselectedNonempty : selected.Nonempty :=
    Finset.card_pos.mp (by omega)
  have havg :
      (stickyFiberSourceShading S Y q.1).averageMultiplicity ≤ 1 := by
    have h := averageMultiplicity_le_indexCard
      (stickyFiberSourceShading S Y q.1)
    simpa only [hcardOne q, Nat.cast_one] using h
  have hfourAvg :
      4 * (stickyFiberSourceShading S Y q.1).averageMultiplicity ≤ 4 := by
    simpa only [mul_one] using mul_le_mul' le_rfl havg
  have hmiddle := four_le_globalPower_mul_sectionEight_singleton
    hglobal hglobalOne hfine hcoarse hgammaTwo hglobalEta hratioExp hratio
      habsorb hbudget hsmall
  refine ⟨q, selected, hselectedNonempty, hselectedCard, ?_⟩
  exact hfourAvg.trans (by simpa only [hselectedCard] using hmiddle)

#print axioms four_le_globalPower_mul_sectionEight_singleton
#print axioms
  exists_sameParent_singleton_four_mul_sourceAverage_le_longMiddle

end
end Family8EndpointSelectedFineSingletonDirectLongMiddleV2
