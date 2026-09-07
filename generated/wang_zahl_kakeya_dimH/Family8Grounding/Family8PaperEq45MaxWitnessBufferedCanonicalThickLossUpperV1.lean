import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalV1
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalDeltaPowerUpperV1
import Mathlib.Tactic

/-!
# Explicit thick-loss envelope for the buffered Equation (45) datum

The buffered producer uses the same literal canonical ambient-density Delta
as the earlier common-scale producer, but its certified comparison constant is
`16`.  At an isotropic positive width this gives the exact coefficient
`27 * 16^3 = 110592`.  The theorem below connects that actual constructor to
the finite `CF * card` envelope used by the scalar power absorption module.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalThickLossUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8PaperEq45MaxWitnessCanonicalDeltaPowerUpperV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

universe u

/-- The actual buffered canonical thick loss has the finite isotropic
`110592 * CF * card` envelope. -/
theorem bufferedCanonicalMaxWitness_isotropic_thickM_rpow_le_explicitCardEnvelope
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (w : NNReal) (hw : 0 < w) (beta : Real) (hbeta : 0 ≤ beta) :
    (uniqueOwnerLocalDeltaThickM 16
        (Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
          CF F ambient) w w : ENNReal) ^ (beta / 2) ≤
      (max 1
        ((110592 : ENNReal) * CF * (Fintype.card iota : ENNReal))) ^
          (beta / 2) := by
  have hraw := canonicalMaxWitness_thickM_rpow_le_cardEnvelope
    CF F ambient hCF hcontained hvolume0 16 w w beta hbeta
  have hCFCardTop :
      CF * (Fintype.card iota : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top hCF (by finiteness)
  calc
    (uniqueOwnerLocalDeltaThickM 16
        (Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
          CF F ambient) w w : ENNReal) ^ (beta / 2) ≤
      (uniqueOwnerLocalDeltaThickM 16
        (CF * (Fintype.card iota : ENNReal)).toNNReal w w : ENNReal) ^
          (beta / 2) := by
      change
        (uniqueOwnerLocalDeltaThickM 16
          (Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.canonicalMaxWitnessDelta
            CF F ambient) w w : ENNReal) ^ (beta / 2) ≤ _
      exact hraw
    _ = (max 1
        ((110592 : ENNReal) * CF * (Fintype.card iota : ENNReal))) ^
          (beta / 2) := by
      have hw0 : w ≠ 0 := hw.ne'
      rw [uniqueOwnerLocalDeltaThickM, div_self hw0]
      simp only [ENNReal.coe_max, ENNReal.coe_one, ENNReal.coe_mul,
        ENNReal.coe_pow, ENNReal.coe_ofNat, ENNReal.coe_toNNReal hCFCardTop]
      congr 2
      norm_num
      ac_rfl

#print axioms
  bufferedCanonicalMaxWitness_isotropic_thickM_rpow_le_explicitCardEnvelope

end
end Family8PaperEq45MaxWitnessBufferedCanonicalThickLossUpperV1
