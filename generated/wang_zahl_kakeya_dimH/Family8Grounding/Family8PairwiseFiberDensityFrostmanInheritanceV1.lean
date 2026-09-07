import Family8Grounding.Family8FrostmanInheritanceToActiveCoarseV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PairwiseFiberDensityFrostmanInheritanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family8FrostmanInheritanceToActiveCoarseV3

noncomputable section

/-- Pairwise comparison of actual fibre densities is enough for upward
Frostman inheritance.  The common fine mass cancels after summing the
comparison over selected and ambient coarse parents, so no absolute density
floor is required. -/
theorem activeCoarse_isFrostmanOn_of_pairwise_fiberDensity
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]
    {F : ConvexFamily iota} {W : ConvexFamily kappa}
    (P : ConvexFactorization F W) (K : ConvexBody Space)
    {C B : ENNReal}
    (hfine : IsFrostmanOn C F P.index.fine K)
    (hcoarseContained : ∀ k ∈ P.index.coarse,
      (W k : Set Space) ⊆ (K : Set Space))
    (hfineMass0 : bodyMassOn F P.index.fine ≠ 0)
    (hfineMassTop : bodyMassOn F P.index.fine ≠ ∞)
    (hcompare : ∀ k, k ∈ P.index.coarse →
      ∀ l, l ∈ P.index.coarse →
        fiberBodyMass P l * volume (W k : Set Space) ≤
          B * fiberBodyMass P k * volume (W l : Set Space)) :
    IsFrostmanOn (C * B) W P.index.coarse K := by
  classical
  refine ⟨hcoarseContained, ?_⟩
  intro Kprime hKprime
  let inside : Finset kappa :=
    indicesInside W P.index.coarse Kprime
  have hinsideCoarse : ∀ k ∈ inside, k ∈ P.index.coarse := by
    intro k hk
    exact (mem_indicesInside W P.index.coarse Kprime k).1 hk |>.1
  have hinsideCarrier : ∀ k ∈ inside,
      (W k : Set Space) ⊆ (Kprime : Set Space) := by
    intro k hk
    exact (mem_indicesInside W P.index.coarse Kprime k).1 hk |>.2
  have hfineSum :
      bodyMassOn F P.index.fine =
        ∑ l ∈ P.index.coarse, fiberBodyMass P l := by
    unfold bodyMassOn
    simpa [activeBodyMass] using
      activeBodyMass_eq_sum_fiberBodyMass P
  have hselectedFine :
      (∑ k ∈ inside, fiberBodyMass P k) *
          volume (K : Set Space) ≤
        C * (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
          volume (Kprime : Set Space) := by
    calc
      (∑ k ∈ inside, fiberBodyMass P k) *
            volume (K : Set Space) ≤
          containedMassOn F P.index.fine Kprime *
            volume (K : Set Space) := by
        exact mul_le_mul'
          (selectedFiberBodyMass_le_containedMassOn
            P inside Kprime hinsideCarrier) le_rfl
      _ ≤ C * containedMassOn F P.index.fine K *
            volume (Kprime : Set Space) :=
        hfine.2 Kprime hKprime
      _ = C * (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
            volume (Kprime : Set Space) := by
        rw [containedMassOn_eq_bodyMassOn_of_contained
          F P.index.fine K hfine.1, hfineSum]
  have hpair :
      (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
          (∑ k ∈ inside, volume (W k : Set Space)) ≤
        B * (∑ k ∈ inside, fiberBodyMass P k) *
          (∑ l ∈ P.index.coarse, volume (W l : Set Space)) := by
    calc
      (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
            (∑ k ∈ inside, volume (W k : Set Space)) =
          ∑ l ∈ P.index.coarse,
            ∑ k ∈ inside,
              fiberBodyMass P l * volume (W k : Set Space) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
      _ ≤ ∑ l ∈ P.index.coarse,
            ∑ k ∈ inside,
              B * fiberBodyMass P k * volume (W l : Set Space) := by
        apply Finset.sum_le_sum
        intro l hl
        apply Finset.sum_le_sum
        intro k hk
        exact hcompare k (hinsideCoarse k hk) l hl
      _ = ∑ l ∈ P.index.coarse,
            B * (∑ k ∈ inside, fiberBodyMass P k) *
              volume (W l : Set Space) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = B * (∑ k ∈ inside, fiberBodyMass P k) *
            (∑ l ∈ P.index.coarse, volume (W l : Set Space)) := by
        simp only [Finset.mul_sum]
  have htotal0 :
      (∑ l ∈ P.index.coarse, fiberBodyMass P l) ≠ 0 := by
    rw [← hfineSum]
    exact hfineMass0
  have htotalTop :
      (∑ l ∈ P.index.coarse, fiberBodyMass P l) ≠ ∞ := by
    rw [← hfineSum]
    exact hfineMassTop
  rw [← massInside_eq_containedMassOn W P.index.coarse Kprime]
  rw [containedMassOn_eq_bodyMassOn_of_contained
    W P.index.coarse K hcoarseContained]
  unfold bodyMassOn massInside
  have hscaled :
      (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
          ((∑ k ∈ inside, volume (W k : Set Space)) *
            volume (K : Set Space)) ≤
        (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
          ((C * B) * (∑ l ∈ P.index.coarse, volume (W l : Set Space)) *
            volume (Kprime : Set Space)) := by
    calc
    (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
          ((∑ k ∈ inside, volume (W k : Set Space)) *
            volume (K : Set Space)) =
        ((∑ l ∈ P.index.coarse, fiberBodyMass P l) *
          (∑ k ∈ inside, volume (W k : Set Space))) *
            volume (K : Set Space) := by ac_rfl
    _ ≤ (B * (∑ k ∈ inside, fiberBodyMass P k) *
          (∑ l ∈ P.index.coarse, volume (W l : Set Space))) *
            volume (K : Set Space) :=
      mul_le_mul' hpair le_rfl
    _ = B * (∑ l ∈ P.index.coarse, volume (W l : Set Space)) *
          ((∑ k ∈ inside, fiberBodyMass P k) *
            volume (K : Set Space)) := by ac_rfl
    _ ≤ B * (∑ l ∈ P.index.coarse, volume (W l : Set Space)) *
          (C * (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
            volume (Kprime : Set Space)) :=
      mul_le_mul' le_rfl hselectedFine
    _ = (∑ l ∈ P.index.coarse, fiberBodyMass P l) *
          ((C * B) *
            (∑ l ∈ P.index.coarse, volume (W l : Set Space)) *
              volume (Kprime : Set Space)) := by ac_rfl
  apply (ENNReal.mul_le_mul_iff_left htotal0 htotalTop).mp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hscaled

#print axioms activeCoarse_isFrostmanOn_of_pairwise_fiberDensity

end
end Family8PairwiseFiberDensityFrostmanInheritanceV1
