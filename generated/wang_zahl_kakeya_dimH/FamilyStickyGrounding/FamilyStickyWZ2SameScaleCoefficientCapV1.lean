import FamilyStickyGrounding.FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
import FamilyStickyGrounding.FamilyStickySameRadiusTubeContainmentCompatibleV1
import FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
import Family6Grounding.Family6ProjectiveSineTriangleV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace FamilyStickyWZ2SameScaleCoefficientCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
open Family6ProjectiveSineTriangleV1
open FamilyStickySameRadiusTubeContainmentCompatibleV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u} [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}
  (Q : @TubeScaleCover delta delta iota _ fine active)

/-!
# Same-scale coefficient caps from WZ2 separation

This is the same-scale-cover part of the Cinematic coefficient cap with the
volume-overlap hypothesis replaced by the exact property used in the proof:
WZ2-separated children cannot have equal carriers.  All finite fibres and
the `13^3` coefficient-cover loss remain unchanged.
-/

/-- Active children assigned to one literal cover parent. -/
def actualCoverParentFiber (q : Fin Q.count) : Finset iota :=
  active.filter fun i => Q.parent i = q

/-- Cover parents hit by one actual reduced-coefficient fibre. -/
noncomputable def actualNearCoefficientCoverParents
    (center : Tube delta) (scale : Real) : Finset (Fin Q.count) := by
  classical
  exact (activeNearCoefficientIndices fine active center scale).image Q.parent

@[simp]
theorem mem_actualNearCoefficientCoverParents_iff
    (center : Tube delta) (scale : Real) (q : Fin Q.count) :
    q ∈ actualNearCoefficientCoverParents Q center scale ↔
      exists i, i ∈ activeNearCoefficientIndices fine active center scale ∧
        Q.parent i = q := by
  classical
  simp [actualNearCoefficientCoverParents]

/-- Same-radius carrier rigidity and WZ2 noncontainment force every literal
cover-parent fibre to contain at most one active child. -/
theorem actualCoverParentFiber_card_le_one_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (q : Fin Q.count) :
    (actualCoverParentFiber Q q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  have hisub : (fine.tubes i).carrier ⊆ (Q.tubes q).carrier := by
    simpa only [hi'.2] using Q.carrier_subset i hi'.1
  have hjsub : (fine.tubes j).carrier ⊆ (Q.tubes q).carrier := by
    simpa only [hj'.2] using Q.carrier_subset j hj'.1
  have hieq : (fine.tubes i).carrier = (Q.tubes q).carrier :=
    tubeCarrierEqOfSameRadiusCarrierSubset
      (fine.tubes i) (Q.tubes q) hisub
  have hjeq : (fine.tubes j).carrier = (Q.tubes q).carrier :=
    tubeCarrierEqOfSameRadiusCarrierSubset
      (fine.tubes j) (Q.tubes q) hjsub
  exact (hpair hi'.1 hj'.1 hij).carrier_ne (hieq.trans hjeq.symm)

/-- An actual coefficient fibre is the disjoint sum of its fibres over the
parents that it hits. -/
theorem activeNearCoefficientIndices_card_le_parent_card_mul_fiberCap
    (center : Tube delta) (scale : Real) (fiberCap : Nat)
    (hfiber : forall q : Fin Q.count,
      (actualCoverParentFiber Q q).card ≤ fiberCap) :
    (activeNearCoefficientIndices fine active center scale).card ≤
      (actualNearCoefficientCoverParents Q center scale).card * fiberCap := by
  classical
  let source := activeNearCoefficientIndices fine active center scale
  let parents := actualNearCoefficientCoverParents Q center scale
  have hmaps : forall i, i ∈ source -> Q.parent i ∈ parents := by
    intro i hi
    exact (mem_actualNearCoefficientCoverParents_iff Q center scale
      (Q.parent i)).mpr ⟨i, hi, rfl⟩
  calc
    source.card = ∑ q ∈ parents,
        (source.filter fun i => Q.parent i = q).card := by
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

/-- WZ2 separation leaves only the number of hit cover parents in an
arbitrary coefficient-fibre bound. -/
theorem activeNearCoefficientIndices_card_le_parent_card_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (center : Tube delta) (scale : Real) :
    (activeNearCoefficientIndices fine active center scale).card ≤
      (actualNearCoefficientCoverParents Q center scale).card := by
  have h := activeNearCoefficientIndices_card_le_parent_card_mul_fiberCap
    Q center scale 1
      (actualCoverParentFiber_card_le_one_of_pairwise_wz2 Q hpair)
  simpa using h

/-- Every literal parallel cluster is bounded by the full finite parent
count. -/
theorem actualParallelCluster_card_le_count (U : Tube delta) :
    (Q.parallelCluster U).card ≤ Q.count := by
  calc
    (Q.parallelCluster U).card ≤
        (Finset.univ : Finset (Fin Q.count)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Q.count := Fintype.card_fin Q.count

/-- Parent localization for a half-scale coefficient fibre centered at an
arbitrary active tube. -/
theorem actualNearCoefficientCoverParents_subset_parallelCluster_of_activeCenter
    {scale : Real} (j : iota) (hj : j ∈ active)
    (hnear : forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j) scale ->
        EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j)) :
    actualNearCoefficientCoverParents Q (fine.tubes j) scale ⊆
      Q.parallelCluster (Q.tubes (Q.parent j)) := by
  classical
  intro q hq
  obtain ⟨i, hiNear, rfl⟩ :=
    (mem_actualNearCoefficientCoverParents_iff Q
      (fine.tubes j) scale q).mp hq
  have hi : i ∈ active := (Finset.mem_filter.mp hiNear).1
  have hnearIJ := hnear i hiNear
  have hchildI :=
    Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset
      (fine.tubes i) (Q.tubes (Q.parent i)) (Q.carrier_subset i hi)
  have hchildJ :=
    Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset
      (fine.tubes j) (Q.tubes (Q.parent j)) (Q.carrier_subset j hj)
  have hmiddle : Real.sin (InnerProductGeometry.angle
      (fine.tubes i).axis.direction
      (Q.tubes (Q.parent j)).axis.direction) ≤ (delta : Real) := by
    calc
      Real.sin (InnerProductGeometry.angle
          (fine.tubes i).axis.direction
          (Q.tubes (Q.parent j)).axis.direction) ≤
        Real.sin (InnerProductGeometry.angle
          (fine.tubes i).axis.direction
          (fine.tubes j).axis.direction) +
        Real.sin (InnerProductGeometry.angle
          (fine.tubes j).axis.direction
          (Q.tubes (Q.parent j)).axis.direction) :=
            sin_angle_triangle_projective _ _ _
      _ ≤ (delta : Real) + 0 := add_le_add hnearIJ hchildJ.le
      _ = (delta : Real) := add_zero _
  have hchildIFirst : Real.sin (InnerProductGeometry.angle
      (Q.tubes (Q.parent i)).axis.direction
      (fine.tubes i).axis.direction) = 0 := by
    simpa only [InnerProductGeometry.angle_comm] using hchildI
  have hparents : Real.sin (InnerProductGeometry.angle
      (Q.tubes (Q.parent i)).axis.direction
      (Q.tubes (Q.parent j)).axis.direction) ≤ (delta : Real) := by
    calc
      Real.sin (InnerProductGeometry.angle
          (Q.tubes (Q.parent i)).axis.direction
          (Q.tubes (Q.parent j)).axis.direction) ≤
        Real.sin (InnerProductGeometry.angle
          (Q.tubes (Q.parent i)).axis.direction
          (fine.tubes i).axis.direction) +
        Real.sin (InnerProductGeometry.angle
          (fine.tubes i).axis.direction
          (Q.tubes (Q.parent j)).axis.direction) :=
            sin_angle_triangle_projective _ _ _
      _ ≤ 0 + (delta : Real) := add_le_add hchildIFirst.le hmiddle
      _ = (delta : Real) := zero_add _
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparents⟩

/-- Active-centred half coefficient fibres are bounded by the same-scale
cover count under WZ2 separation. -/
theorem activeNearCoefficientIndices_card_le_coverCount_of_activeCenter_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} (j : iota) (hj : j ∈ active)
    (hnear : forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j) scale ->
        EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j)) :
    (activeNearCoefficientIndices fine active (fine.tubes j) scale).card ≤
      Q.count := by
  have hfibre :=
    activeNearCoefficientIndices_card_le_parent_card_of_pairwise_wz2
      Q hpair (fine.tubes j) scale
  have hparents :=
    actualNearCoefficientCoverParents_subset_parallelCluster_of_activeCenter
      Q j hj hnear
  exact hfibre.trans <|
    (Finset.card_le_card hparents).trans
      (actualParallelCluster_card_le_count Q (Q.tubes (Q.parent j)))

/-- The full-radius indexed coefficient cap, with the explicit three-
coordinate half-scale cover loss, needs only WZ2 separation. -/
theorem activeNearCoefficientIndices_card_le_coverLoss_mul_count_wz2
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hhalfParallel : forall j, j ∈ active -> forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j)
        ((delta : Real) / 2) ->
      EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j))
    (center : Tube delta) :
    (activeNearCoefficientIndices fine active center (delta : Real)).card ≤
      actualHalfScaleCoefficientCoverLoss * Q.count := by
  apply activeNearCoefficientIndices_card_le_full_of_half
    fine active hdelta
  intro j hj
  exact activeNearCoefficientIndices_card_le_coverCount_of_activeCenter_wz2
    Q hpair j hj (hhalfParallel j hj)

/-- Numerical domination turns the WZ2 same-scale-cover bound into the
requested multiplicity cap. -/
theorem activeNearCoefficientIndices_card_le_multiplicity_wz2
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hhalfParallel : forall j, j ∈ active -> forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j)
        ((delta : Real) / 2) ->
      EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j))
    {multiplicity : Nat}
    (hcount : actualHalfScaleCoefficientCoverLoss * Q.count ≤ multiplicity)
    (center : Tube delta) :
    (activeNearCoefficientIndices fine active center (delta : Real)).card ≤
      multiplicity :=
  (activeNearCoefficientIndices_card_le_coverLoss_mul_count_wz2
    Q hdelta hpair hhalfParallel center).trans hcount

#print axioms actualCoverParentFiber_card_le_one_of_pairwise_wz2
#print axioms activeNearCoefficientIndices_card_le_parent_card_of_pairwise_wz2
#print axioms actualNearCoefficientCoverParents_subset_parallelCluster_of_activeCenter
#print axioms activeNearCoefficientIndices_card_le_coverLoss_mul_count_wz2
#print axioms activeNearCoefficientIndices_card_le_multiplicity_wz2

end

end FamilyStickyWZ2SameScaleCoefficientCapV1
