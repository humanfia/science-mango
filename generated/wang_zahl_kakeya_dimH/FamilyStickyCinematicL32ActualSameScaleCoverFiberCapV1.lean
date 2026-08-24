import FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
import FamilyStickySameRadiusTubeContainmentCarrierV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickySameRadiusTubeContainmentCarrierV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u} [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}
  (C : @TubeScaleCover delta delta iota _ fine active)

/-!
# Clean same-scale cover fibres for actual coefficient balls

This is the finite/geometric core of the coefficient-fibre cap.  It uses
only the literal same-radius cover containment and global essential
distinctness.  No parent-union volume packing, old coefficient selection,
or final multiplicity conclusion is imported.
-/

/-- Active children assigned to one literal cover parent. -/
def actualCoverParentFiber (q : Fin C.count) : Finset iota :=
  active.filter fun i => C.parent i = q

/-- Cover parents hit by one actual reduced-coefficient fibre. -/
noncomputable def actualNearCoefficientCoverParents
    (center : Tube delta) (scale : Real) : Finset (Fin C.count) := by
  classical
  exact (activeNearCoefficientIndices fine active center scale).image C.parent

@[simp]
theorem mem_actualNearCoefficientCoverParents_iff
    (center : Tube delta) (scale : Real) (q : Fin C.count) :
    q ∈ actualNearCoefficientCoverParents C center scale ↔
      exists i, i ∈ activeNearCoefficientIndices fine active center scale ∧
        C.parent i = q := by
  classical
  simp [actualNearCoefficientCoverParents]

/-- Same-radius carrier rigidity and essential distinctness force every
cover-parent fibre to contain at most one active child. -/
theorem actualCoverParentFiber_card_le_one
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (q : Fin C.count) :
    (actualCoverParentFiber C q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  have hisub : (fine.tubes i).carrier ⊆ (C.tubes q).carrier := by
    simpa only [hi'.2] using C.carrier_subset i hi'.1
  have hjsub : (fine.tubes j).carrier ⊆ (C.tubes q).carrier := by
    simpa only [hj'.2] using C.carrier_subset j hj'.1
  have hieq : (fine.tubes i).carrier = (C.tubes q).carrier :=
    tubeCarrierEqOfSameRadiusCarrierSubset (fine.tubes i) (C.tubes q) hisub
  have hjeq : (fine.tubes j).carrier = (C.tubes q).carrier :=
    tubeCarrierEqOfSameRadiusCarrierSubset (fine.tubes j) (C.tubes q) hjsub
  have hdistinct := hpair hi'.1 hj'.1 hij
  change EssentiallyDistinct (fine.tubes i) (fine.tubes j) at hdistinct
  rw [EssentiallyDistinct, hieq, hjeq, Set.inter_self, max_self] at hdistinct
  let v : ENNReal := volume (C.tubes q).carrier
  have hvPos : 0 < v := (C.tubes q).volume_pos hdelta
  have hvTop : v ≠ ∞ := ne_of_lt (C.tubes q).volume_lt_top
  have hhalfTop : (2 : ENNReal)⁻¹ * v ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hvTop
  have hreal := ENNReal.toReal_mono hhalfTop hdistinct
  have hvRealPos : 0 < v.toReal := ENNReal.toReal_pos hvPos.ne' hvTop
  change v.toReal ≤ (((2 : ENNReal)⁻¹ * v).toReal) at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at hreal
  norm_num at hreal
  linarith

/-- An actual coefficient fibre is the disjoint sum of its fibres over the
parents that it hits. -/
theorem activeNearCoefficientIndices_card_le_parent_card_mul_fiberCap
    (center : Tube delta) (scale : Real) (fiberCap : Nat)
    (hfiber : forall q : Fin C.count,
      (actualCoverParentFiber C q).card ≤ fiberCap) :
    (activeNearCoefficientIndices fine active center scale).card ≤
      (actualNearCoefficientCoverParents C center scale).card * fiberCap := by
  classical
  let source := activeNearCoefficientIndices fine active center scale
  let parents := actualNearCoefficientCoverParents C center scale
  have hmaps : forall i, i ∈ source -> C.parent i ∈ parents := by
    intro i hi
    exact (mem_actualNearCoefficientCoverParents_iff C center scale
      (C.parent i)).mpr ⟨i, hi, rfl⟩
  calc
    source.card = ∑ q ∈ parents,
        (source.filter fun i => C.parent i = q).card := by
      exact Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _q ∈ parents, fiberCap := by
      apply Finset.sum_le_sum
      intro q hq
      apply (Finset.card_le_card ?_).trans (hfiber q)
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hi'.1).1, hi'.2⟩
    _ = parents.card * fiberCap := by simp

/-- With essential distinctness, only the number of hit cover parents
remains in the coefficient-fibre bound. -/
theorem activeNearCoefficientIndices_card_le_parent_card
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (center : Tube delta) (scale : Real) :
    (activeNearCoefficientIndices fine active center scale).card ≤
      (actualNearCoefficientCoverParents C center scale).card := by
  have h := activeNearCoefficientIndices_card_le_parent_card_mul_fiberCap
    C center scale 1 (actualCoverParentFiber_card_le_one C hdelta hpair)
  simpa using h

/-- Every literal parallel cluster is bounded by the full finite parent
count; this is the callback-free crude numerical producer. -/
theorem actualParallelCluster_card_le_count (U : Tube delta) :
    (C.parallelCluster U).card ≤ C.count := by
  calc
    (C.parallelCluster U).card ≤
        (Finset.univ : Finset (Fin C.count)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = C.count := Fintype.card_fin C.count

#print axioms actualCoverParentFiber_card_le_one
#print axioms activeNearCoefficientIndices_card_le_parent_card_mul_fiberCap
#print axioms activeNearCoefficientIndices_card_le_parent_card
#print axioms actualParallelCluster_card_le_count

end

end FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1
