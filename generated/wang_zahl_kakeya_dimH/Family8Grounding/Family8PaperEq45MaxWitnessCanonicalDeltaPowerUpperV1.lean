import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
import Mathlib.Tactic

/-!
# Power upper envelope for the canonical max-witness thick loss

The actual canonical `Delta` upper envelope is monotone through the
nonnegative paper exponent `beta / 2`.  This is the precise input needed to
replace a generic selected-bucket absorption callback by an honest explicit
cardinality envelope for the `thickM^(beta/2)` loss.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalDeltaPowerUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

universe u

/-- The honest canonical `thickM^(beta/2)` loss is bounded by the same
constructor evaluated at the finite `CF * card` Delta envelope. -/
theorem canonicalMaxWitness_thickM_rpow_le_cardEnvelope
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (comparisonConstant a b : NNReal) (beta : Real) (hbeta : 0 ≤ beta) :
    (uniqueOwnerLocalDeltaThickM comparisonConstant
        (canonicalMaxWitnessDelta CF F ambient) a b : ENNReal) ^ (beta / 2) ≤
      (uniqueOwnerLocalDeltaThickM comparisonConstant
        (CF * (Fintype.card iota : ENNReal)).toNNReal a b : ENNReal) ^
          (beta / 2) := by
  apply ENNReal.rpow_le_rpow
  · exact ENNReal.coe_le_coe.mpr
      (canonicalMaxWitness_thickM_le_cardEnvelope
        CF F ambient hCF hcontained hvolume0 comparisonConstant a b)
  · linarith

#print axioms canonicalMaxWitness_thickM_rpow_le_cardEnvelope

end
end Family8PaperEq45MaxWitnessCanonicalDeltaPowerUpperV1
