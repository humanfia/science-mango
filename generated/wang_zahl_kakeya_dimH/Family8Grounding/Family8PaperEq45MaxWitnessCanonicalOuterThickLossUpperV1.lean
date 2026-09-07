import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalDeltaPowerUpperV1
import Mathlib.Tactic

/-!
# Explicit canonical outer/thick-loss envelope

For the actual canonical max-witness `Delta`, the common witness is
isotropic, so the unique-owner thickening count is
`max 1 (216 * Delta)`.  This module combines the canonical finite-cardinality
upper bound for `Delta` with the honest outer retention loss.  The result
retains only the explicit source Frostman constant, witness-cardinality,
fibre-card, and conflict-degree quantities that still require upstream power
bounds.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalOuterThickLossUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8PaperEq45MaxWitnessCanonicalDeltaPowerUpperV1
open Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

universe u

/-- At an isotropic positive width, the canonical thickening power is
bounded by the explicit finite `216 * CF * card` envelope. -/
theorem canonicalMaxWitness_isotropic_thickM_rpow_le_explicitCardEnvelope
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (w : NNReal) (hw : 0 < w) (beta : Real) (hbeta : 0 ≤ beta) :
    (uniqueOwnerLocalDeltaThickM 2
        (canonicalMaxWitnessDelta CF F ambient) w w : ENNReal) ^
        (beta / 2) ≤
      (max 1
        ((216 : ENNReal) * CF * (Fintype.card iota : ENNReal))) ^
          (beta / 2) := by
  have hraw := canonicalMaxWitness_thickM_rpow_le_cardEnvelope
    CF F ambient hCF hcontained hvolume0 2 w w beta hbeta
  have hCFCardTop :
      CF * (Fintype.card iota : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top hCF (by finiteness)
  calc
    (uniqueOwnerLocalDeltaThickM 2
        (canonicalMaxWitnessDelta CF F ambient) w w : ENNReal) ^
        (beta / 2) ≤
      (uniqueOwnerLocalDeltaThickM 2
        (CF * (Fintype.card iota : ENNReal)).toNNReal w w : ENNReal) ^
          (beta / 2) := hraw
    _ = (max 1
        ((216 : ENNReal) * CF * (Fintype.card iota : ENNReal))) ^
          (beta / 2) := by
      have hw0 : w ≠ 0 := hw.ne'
      rw [uniqueOwnerLocalDeltaThickM, div_self hw0]
      simp only [ENNReal.coe_max, ENNReal.coe_one, ENNReal.coe_mul,
        ENNReal.coe_pow, ENNReal.coe_ofNat, ENNReal.coe_toNNReal hCFCardTop]
      congr 2
      norm_num
      ac_rfl

/-- Multiplication by the literal two fibre-card losses and conflict-degree
loss preserves the canonical thickening envelope. -/
theorem canonicalMaxWitness_outerThickLoss_le_explicitCardEnvelope
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (fibreCardCap : Nat) (conflictLoss : ENNReal)
    (w : NNReal) (hw : 0 < w) (beta : Real) (hbeta : 0 ≤ beta) :
    ((((fibreCardCap : ENNReal) * conflictLoss) *
        (fibreCardCap : ENNReal)) *
      (uniqueOwnerLocalDeltaThickM 2
        (canonicalMaxWitnessDelta CF F ambient) w w : ENNReal) ^
          (beta / 2)) ≤
      ((((fibreCardCap : ENNReal) * conflictLoss) *
          (fibreCardCap : ENNReal)) *
        (max 1
          ((216 : ENNReal) * CF * (Fintype.card iota : ENNReal))) ^
            (beta / 2)) := by
  exact mul_le_mul' le_rfl
    (canonicalMaxWitness_isotropic_thickM_rpow_le_explicitCardEnvelope
      CF F ambient hCF hcontained hvolume0 w hw beta hbeta)

#print axioms
  canonicalMaxWitness_isotropic_thickM_rpow_le_explicitCardEnvelope
#print axioms canonicalMaxWitness_outerThickLoss_le_explicitCardEnvelope

end
end Family8PaperEq45MaxWitnessCanonicalOuterThickLossUpperV1
