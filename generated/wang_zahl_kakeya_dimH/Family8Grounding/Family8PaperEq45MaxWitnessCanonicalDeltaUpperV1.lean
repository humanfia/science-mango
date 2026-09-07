import Family8Grounding.Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
import Mathlib.Tactic

/-!
# Constructed upper envelope for the canonical max-witness Delta

For a finite family contained in one positive finite-volume ambient body,
the actual ambient family-volume density is at most the index cardinality.
Consequently the canonical `Delta = CF * ambientDensity` used by the genuine
max-witness input has the explicit upper envelope `CF * card`.

This is the missing upper-direction producer needed to control the honest
`thickM^(beta/2)` loss.  It does not apply to an arbitrary manually inflated
input; it applies to the actual canonical `Delta` constructor.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8AmbientFamilyVolumeDensityV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

universe u

/-- Containment bounds the literal actual family-volume density by the
number of indexed members, repetitions included. -/
theorem ambientFamilyVolumeDensity_le_card
    {iota : Type u} [Fintype iota]
    (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0) :
    ambientFamilyVolumeDensity F ambient ≤ (Fintype.card iota : ENNReal) := by
  have hvolumeTop : volume (ambient : Set Space) ≠ ∞ :=
    ambient.isCompact.measure_lt_top.ne
  unfold ambientFamilyVolumeDensity
  apply (ENNReal.div_le_iff hvolume0 hvolumeTop).2
  unfold familyVolume
  calc
    (∑ i, volume (F i : Set Space)) ≤
        ∑ _i : iota, volume (ambient : Set Space) := by
      exact Finset.sum_le_sum fun i _hi => measure_mono (hcontained i)
    _ = (Fintype.card iota : ENNReal) *
        volume (ambient : Set Space) := by simp

/-- ENNReal form of the actual canonical-Delta upper envelope. -/
theorem canonicalMaxWitnessDelta_coe_le_CF_mul_card
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0) :
    (canonicalMaxWitnessDelta CF F ambient : ENNReal) ≤
      CF * (Fintype.card iota : ENNReal) := by
  rw [canonicalMaxWitnessDelta_coe CF F ambient hCF hvolume0]
  exact mul_le_mul' le_rfl
    (ambientFamilyVolumeDensity_le_card F ambient hcontained hvolume0)

/-- Finite NNReal envelope, ready to be inserted into `thickM`. -/
theorem canonicalMaxWitnessDelta_le_toNNReal_CF_mul_card
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0) :
    canonicalMaxWitnessDelta CF F ambient ≤
      (CF * (Fintype.card iota : ENNReal)).toNNReal := by
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_toNNReal]
  · exact canonicalMaxWitnessDelta_coe_le_CF_mul_card
      CF F ambient hCF hcontained hvolume0
  · exact ENNReal.mul_ne_top hCF (by finiteness)

/-- Monotonicity transports the actual canonical-Delta envelope through the
honest unique-owner thickening constructor. -/
theorem canonicalMaxWitness_thickM_le_cardEnvelope
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (comparisonConstant a b : NNReal) :
    uniqueOwnerLocalDeltaThickM comparisonConstant
        (canonicalMaxWitnessDelta CF F ambient) a b ≤
      uniqueOwnerLocalDeltaThickM comparisonConstant
        (CF * (Fintype.card iota : ENNReal)).toNNReal a b := by
  unfold uniqueOwnerLocalDeltaThickM
  gcongr
  exact canonicalMaxWitnessDelta_le_toNNReal_CF_mul_card
    CF F ambient hCF hcontained hvolume0

#print axioms ambientFamilyVolumeDensity_le_card
#print axioms canonicalMaxWitnessDelta_coe_le_CF_mul_card
#print axioms canonicalMaxWitnessDelta_le_toNNReal_CF_mul_card
#print axioms canonicalMaxWitness_thickM_le_cardEnvelope

end
end Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
