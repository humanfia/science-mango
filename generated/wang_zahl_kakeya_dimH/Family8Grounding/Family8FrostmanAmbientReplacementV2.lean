import Family8Grounding.Family8FrostmanAmbientEnlargementV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FrostmanAmbientReplacementV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6CanonicalFrostmanConstantCoreV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota]

/-!
# Frostman transport between two ambient bodies containing the same family

V1 omitted one namespace qualification and is intentionally not imported.
-/

theorem isFrostmanIn_replace_ambient
    {F : ConvexFamily iota} {K L : ConvexBody Space} {C Q : ENNReal}
    (hF : IsFrostmanIn C F K)
    (hfamilyL : ∀ i, (F i : Set Space) ⊆ (L : Set Space))
    (hvolume : volume (L : Set Space) ≤ Q * volume (K : Set Space)) :
    IsFrostmanIn (Q * C) F L := by
  classical
  refine ⟨hfamilyL, ?_⟩
  intro K' hK'L
  by_cases hempty : containedIndices F K' = ∅
  · have hmass0 : containedMass F K' = 0 := by
      simp [containedMass, hempty]
    simp [hmass0]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hiK' : (F i : Set Space) ⊆ (K' : Set Space) :=
      (mem_containedIndices F K' i).1 hi
    obtain ⟨x, hx⟩ := (F i).nonempty
    let capBody : ConvexBody Space :=
      { carrier := (K : Set Space) ∩ (K' : Set Space)
        convex' := K.convex.inter K'.convex
        isCompact' := K.isCompact.inter_right K'.isClosed
        nonempty' := ⟨x, hF.1 i hx, hiK' hx⟩ }
    have hcapK : (capBody : Set Space) ⊆ (K : Set Space) :=
      inter_subset_left
    have hcapK' : (capBody : Set Space) ⊆ (K' : Set Space) :=
      inter_subset_right
    have hindices : containedIndices F K' = containedIndices F capBody := by
      ext j
      rw [mem_containedIndices, mem_containedIndices]
      constructor
      · intro hj y hy
        exact ⟨hF.1 j hy, hj hy⟩
      · intro hj y hy
        exact (hj hy).2
    have hmassEq : containedMass F K' = containedMass F capBody := by
      unfold containedMass
      rw [hindices]
    have hambientMass : containedMass F K = containedMass F L := by
      rw [containedMass_eq_familyVolume_of_contained F K hF.1,
        containedMass_eq_familyVolume_of_contained F L hfamilyL]
    calc
      containedMass F K' * volume (L : Set Space) =
          containedMass F capBody * volume (L : Set Space) := by
        rw [hmassEq]
      _ ≤ containedMass F capBody *
          (Q * volume (K : Set Space)) := by
        exact mul_le_mul' le_rfl hvolume
      _ = Q *
          (containedMass F capBody * volume (K : Set Space)) := by
        ac_rfl
      _ ≤ Q *
          (C * containedMass F K * volume (capBody : Set Space)) := by
        exact mul_le_mul' le_rfl (hF.2 capBody hcapK)
      _ = (Q * C) * containedMass F K *
          volume (capBody : Set Space) := by
        ac_rfl
      _ ≤ (Q * C) * containedMass F L *
          volume (K' : Set Space) := by
        rw [hambientMass]
        exact mul_le_mul' le_rfl (measure_mono hcapK')

#print axioms isFrostmanIn_replace_ambient

end
end Family8FrostmanAmbientReplacementV2
