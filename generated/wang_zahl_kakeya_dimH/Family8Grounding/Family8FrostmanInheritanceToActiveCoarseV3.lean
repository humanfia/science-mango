import Submission.Kakeya.ConvexFactoring.JointTubeFactoring
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Mathlib.Tactic

/-!
# Frostman inheritance from fine fibres to the active coarse family

This is the cross-multiplied, finite-family form of Remark 3.3(A) used in the
proof of Proposition 6.6(A).  If an actual convex factorization has comparable
fine-body density in every active parent, then a Frostman certificate for the
active fine family passes to the active coarse bodies.  The loss is exactly
`upper / lower`.

No Frostman conclusion is stored in the factorization, and no multiplicity
estimate is assumed here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FrostmanInheritanceToActiveCoarseV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-- Fine body mass assigned to any selected set of actual parents is bounded
by the fine contained mass in every body containing those parents. -/
theorem selectedFiberBodyMass_le_containedMassOn
    {iota kappa : Type*} [Fintype iota]
    [DecidableEq iota] [DecidableEq kappa]
    {F : ConvexFamily iota} {W : ConvexFamily kappa}
    (P : ConvexFactorization F W) (selected : Finset kappa)
    (K : ConvexBody Space)
    (hinside : ∀ k ∈ selected,
      (W k : Set Space) ⊆ (K : Set Space)) :
    (∑ k ∈ selected, fiberBodyMass P k) ≤
      containedMassOn F P.index.fine K := by
  classical
  have hsum :
      bodyMassOn F
          (selectedFineIndices P.index.fine P.index.parent selected) =
        ∑ k ∈ selected, fiberBodyMass P k := by
    unfold bodyMassOn
    change
      (∑ i ∈ selectedFineIndices P.index.fine P.index.parent selected,
          volume (F i : Set Space)) = _
    calc
      (∑ i ∈ selectedFineIndices P.index.fine P.index.parent selected,
          volume (F i : Set Space)) =
          ∑ k ∈ selected,
            ∑ i ∈
              (selectedIndexFactorization P.index.fine P.index.parent
                selected).fiber k,
              volume (F i : Set Space) := by
        simpa only [selectedIndexFactorization_fine,
          selectedIndexFactorization_coarse] using
          (selectedIndexFactorization P.index.fine P.index.parent selected).sum_fiberwise
            (fun i => volume (F i : Set Space))
      _ = ∑ k ∈ selected, fiberBodyMass P k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [selected_fiber_eq_raw_fiber P.index.fine P.index.parent
          selected hk]
        rfl
  rw [← hsum]
  unfold bodyMassOn containedMassOn
  apply Finset.sum_le_sum_of_subset
  intro i hi
  have hiParts := Finset.mem_filter.mp hi
  rw [@Finset.mem_inter iota (Classical.decEq iota)]
  refine ⟨hiParts.1, (mem_containedIndices F K i).2 ?_⟩
  exact (P.contained i hiParts.1).trans
    (hinside (P.index.parent i) hiParts.2)

/-- Comparable assigned fine mass makes Frostman non-concentration inherit
upwards to the actual active coarse family.  The inverse is safe precisely
under the stated nonzero/non-top hypotheses on the lower density. -/
theorem activeCoarse_isFrostmanOn_of_comparable_fiberDensity
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]
    {F : ConvexFamily iota} {W : ConvexFamily kappa}
    (P : ConvexFactorization F W) (K : ConvexBody Space)
    {C lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfine : IsFrostmanOn C F P.index.fine K)
    (hcoarseContained : ∀ k ∈ P.index.coarse,
      (W k : Set Space) ⊆ (K : Set Space))
    (hlower : ∀ k ∈ P.index.coarse,
      lower * volume (W k : Set Space) ≤ fiberBodyMass P k)
    (hupper : ∀ k ∈ P.index.coarse,
      fiberBodyMass P k ≤ upper * volume (W k : Set Space)) :
    IsFrostmanOn (C * upper * lower⁻¹) W P.index.coarse K := by
  classical
  refine ⟨hcoarseContained, ?_⟩
  intro Kprime hKprime
  let inside : Finset kappa :=
    indicesInside W P.index.coarse Kprime
  have hinsideCoarse : ∀ k ∈ inside,
      k ∈ P.index.coarse := by
    intro k hk
    exact (mem_indicesInside W P.index.coarse Kprime k).1 hk |>.1
  have hinsideCarrier : ∀ k ∈ inside,
      (W k : Set Space) ⊆ (Kprime : Set Space) := by
    intro k hk
    exact (mem_indicesInside W P.index.coarse Kprime k).1 hk |>.2
  have hlowerLocal :
      lower * containedMassOn W P.index.coarse Kprime ≤
        containedMassOn F P.index.fine Kprime := by
    rw [← massInside_eq_containedMassOn W P.index.coarse Kprime]
    change lower * (∑ k ∈ inside, volume (W k : Set Space)) ≤ _
    rw [Finset.mul_sum]
    calc
      (∑ k ∈ inside, lower * volume (W k : Set Space)) ≤
          ∑ k ∈ inside, fiberBodyMass P k := by
        exact Finset.sum_le_sum fun k hk => hlower k (hinsideCoarse k hk)
      _ ≤ containedMassOn F P.index.fine Kprime :=
        selectedFiberBodyMass_le_containedMassOn P inside Kprime
          hinsideCarrier
  have hupperAmbient :
      containedMassOn F P.index.fine K ≤
        upper * containedMassOn W P.index.coarse K := by
    rw [containedMassOn_eq_bodyMassOn_of_contained F P.index.fine K
      hfine.1]
    rw [containedMassOn_eq_bodyMassOn_of_contained W P.index.coarse K
      hcoarseContained]
    unfold bodyMassOn
    calc
      (∑ i ∈ P.index.fine, volume (F i : Set Space)) =
          ∑ k ∈ P.index.coarse, fiberBodyMass P k := by
        simpa [activeBodyMass] using
          activeBodyMass_eq_sum_fiberBodyMass P
      _ ≤ ∑ k ∈ P.index.coarse,
          upper * volume (W k : Set Space) := by
        exact Finset.sum_le_sum fun k hk => hupper k hk
      _ = upper * ∑ k ∈ P.index.coarse,
          volume (W k : Set Space) := by
        rw [Finset.mul_sum]
  have hscaled :
      lower *
          (containedMassOn W P.index.coarse Kprime *
            volume (K : Set Space)) ≤
        C * upper * containedMassOn W P.index.coarse K *
          volume (Kprime : Set Space) := by
    calc
      lower *
            (containedMassOn W P.index.coarse Kprime *
              volume (K : Set Space)) =
          (lower * containedMassOn W P.index.coarse Kprime) *
            volume (K : Set Space) := by ac_rfl
      _ ≤ containedMassOn F P.index.fine Kprime *
            volume (K : Set Space) :=
        mul_le_mul' hlowerLocal le_rfl
      _ ≤ C * containedMassOn F P.index.fine K *
            volume (Kprime : Set Space) :=
        hfine.2 Kprime hKprime
      _ ≤ C * (upper * containedMassOn W P.index.coarse K) *
            volume (Kprime : Set Space) := by
        exact mul_le_mul' (mul_le_mul' le_rfl hupperAmbient) le_rfl
      _ = C * upper * containedMassOn W P.index.coarse K *
            volume (Kprime : Set Space) := by ac_rfl
  have hcancel : lower * lower⁻¹ = (1 : ENNReal) :=
    ENNReal.mul_inv_cancel hlower0 hlowerTop
  calc
    containedMassOn W P.index.coarse Kprime *
          volume (K : Set Space) =
        (lower *
            (containedMassOn W P.index.coarse Kprime *
              volume (K : Set Space))) * lower⁻¹ := by
      calc
        containedMassOn W P.index.coarse Kprime *
              volume (K : Set Space) =
            (lower * lower⁻¹) *
              (containedMassOn W P.index.coarse Kprime *
                volume (K : Set Space)) := by rw [hcancel, one_mul]
        _ = _ := by ac_rfl
    _ ≤ (C * upper * containedMassOn W P.index.coarse K *
          volume (Kprime : Set Space)) * lower⁻¹ :=
      mul_le_mul' hscaled le_rfl
    _ = (C * upper * lower⁻¹) *
          containedMassOn W P.index.coarse K *
            volume (Kprime : Set Space) := by ac_rfl

#print axioms selectedFiberBodyMass_le_containedMassOn
#print axioms activeCoarse_isFrostmanOn_of_comparable_fiberDensity

end

end Family8FrostmanInheritanceToActiveCoarseV3
