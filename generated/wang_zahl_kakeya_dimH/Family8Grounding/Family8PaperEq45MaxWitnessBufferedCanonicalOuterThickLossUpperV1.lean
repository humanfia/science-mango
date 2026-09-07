import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalThickLossUpperV1
import Mathlib.Tactic

/-!
# Full finite outer/thick envelope for the buffered Equation (45) datum

This successor combines the actual canonical buffered thick-loss theorem with
honest upper bounds for the two fibre-card factors, the conflict loss, and the
selected-family cardinality.  All four quantities are replaced by one finite
envelope `N`; no final inequality is accepted as a premise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalOuterThickLossUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8PaperEq45MaxWitnessBufferedCanonicalThickLossUpperV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

universe u

/-- Pure monotonicity for the buffered finite outer/thick envelope. -/
theorem bufferedOuterThickFiniteEnvelope_mono
    (N M loss C W : ENNReal) (beta : Real) (hbeta : 0 ≤ beta)
    (hM : M ≤ N) (hloss : loss ≤ N) (hW : W ≤ N) :
    (((M * loss) * M) *
      (max 1 ((110592 : ENNReal) * C * W)) ^ (beta / 2)) ≤
      (((N * N) * N) *
        (max 1 ((110592 : ENNReal) * C * N)) ^ (beta / 2)) := by
  apply mul_le_mul'
  · exact mul_le_mul' (mul_le_mul' hM hloss) hM
  · apply ENNReal.rpow_le_rpow
    · exact max_le_max le_rfl (mul_le_mul' le_rfl hW)
    · linarith

/-- The complete actual canonical buffered outer/thick product is bounded by
one finite envelope once each literal finite factor is bounded by `N`. -/
theorem bufferedCanonicalMaxWitness_outerThickLoss_le_NEnvelope
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (M loss N : ENNReal)
    (hM : M ≤ N) (hloss : loss ≤ N)
    (hcard : (Fintype.card iota : ENNReal) ≤ N)
    (w : NNReal) (hw : 0 < w) (beta : Real) (hbeta : 0 ≤ beta) :
    (((M * loss) * M) *
      (uniqueOwnerLocalDeltaThickM 16
        (Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
          CF F ambient) w w : ENNReal) ^ (beta / 2)) ≤
      (((N * N) * N) *
        (max 1 ((110592 : ENNReal) * CF * N)) ^ (beta / 2)) := by
  calc
    (((M * loss) * M) *
      (uniqueOwnerLocalDeltaThickM 16
        (Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
          CF F ambient) w w : ENNReal) ^ (beta / 2)) ≤
      (((M * loss) * M) *
        (max 1 ((110592 : ENNReal) * CF *
          (Fintype.card iota : ENNReal))) ^ (beta / 2)) := by
      exact mul_le_mul' le_rfl
        (bufferedCanonicalMaxWitness_isotropic_thickM_rpow_le_explicitCardEnvelope
          CF F ambient hCF hcontained hvolume0 w hw beta hbeta)
    _ ≤ (((N * N) * N) *
        (max 1 ((110592 : ENNReal) * CF * N)) ^ (beta / 2)) := by
      exact bufferedOuterThickFiniteEnvelope_mono
        N M loss CF (Fintype.card iota : ENNReal) beta hbeta
        hM hloss hcard

#print axioms bufferedOuterThickFiniteEnvelope_mono
#print axioms bufferedCanonicalMaxWitness_outerThickLoss_le_NEnvelope

end
end Family8PaperEq45MaxWitnessBufferedCanonicalOuterThickLossUpperV1
