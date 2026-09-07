import Family8Grounding.Family8FrostmanAmbientEnlargementV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FrostmanFamilyEnlargementV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6CanonicalFrostmanConstantCoreV1

noncomputable section

universe u

variable {index : Type u} [Fintype index]

/-!
# Frostman transport under controlled family enlargement, V2

V1 omitted the namespace containing the ambient-mass identity and is not
imported.
-/

theorem isFrostmanIn_enlarge_family
    {F G : ConvexFamily index} {K : ConvexBody Space} {C R : ENNReal}
    (hF : IsFrostmanIn C F K)
    (hsubset : ∀ i, (F i : Set Space) ⊆ (G i : Set Space))
    (hcontained : ∀ i, (G i : Set Space) ⊆ (K : Set Space))
    (hvolume : ∀ i, volume (G i : Set Space) ≤
      R * volume (F i : Set Space)) :
    IsFrostmanIn (R * C) G K := by
  classical
  refine ⟨hcontained, ?_⟩
  intro K' hK'
  have hindices : containedIndices G K' ⊆ containedIndices F K' := by
    intro i hi
    rw [mem_containedIndices] at hi ⊢
    exact (hsubset i).trans hi
  have htestMass : containedMass G K' ≤ R * containedMass F K' := by
    calc
      containedMass G K' =
          ∑ i ∈ containedIndices G K', volume (G i : Set Space) := rfl
      _ ≤ ∑ i ∈ containedIndices G K',
          R * volume (F i : Set Space) :=
        Finset.sum_le_sum fun i _hi ↦ hvolume i
      _ = R * ∑ i ∈ containedIndices G K',
          volume (F i : Set Space) := by rw [Finset.mul_sum]
      _ ≤ R * ∑ i ∈ containedIndices F K',
          volume (F i : Set Space) := by
        exact mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hindices)
      _ = R * containedMass F K' := rfl
  have hambientMass : containedMass F K ≤ containedMass G K := by
    rw [containedMass_eq_familyVolume_of_contained F K hF.1,
      containedMass_eq_familyVolume_of_contained G K hcontained]
    unfold familyVolume
    exact Finset.sum_le_sum fun i _hi ↦ measure_mono (hsubset i)
  calc
    containedMass G K' * volume (K : Set Space) ≤
        (R * containedMass F K') * volume (K : Set Space) :=
      mul_le_mul' htestMass le_rfl
    _ = R * (containedMass F K' * volume (K : Set Space)) := by
      ac_rfl
    _ ≤ R * (C * containedMass F K * volume (K' : Set Space)) :=
      mul_le_mul' le_rfl (hF.2 K' hK')
    _ = (R * C) * containedMass F K * volume (K' : Set Space) := by
      ac_rfl
    _ ≤ (R * C) * containedMass G K * volume (K' : Set Space) :=
      mul_le_mul' (mul_le_mul' le_rfl hambientMass) le_rfl

#print axioms isFrostmanIn_enlarge_family

end
end Family8FrostmanFamilyEnlargementV2
