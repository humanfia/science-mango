import FamilyStickyGrounding.FamilyStickyAllParentLayerCollisionRandomMotionV1

namespace FamilyStickyAllParentLayerJointRepetitionsV1

open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerNumericsV1.AllParentLayerData
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomWZCommonNeighbourPackingV1

noncomputable section

/-!
# A nondegenerate repetition selector shared by both Appendix estimates

GWZ lines 2655--2706 use one repetition count `J` for the `100 T₀`
collision events and the convex-body concentration events.  Selecting `J`
from the analytic caps alone can be too large by a `Delta_max` factor.  The
faithful finite selector is therefore the minimum of:

* the existing heterogeneous analytic cap/mean selector;
* the infimum of `C_WZ / collisionMean(parent)` over active parents.

If every one-step analytic and collision mean is below its cap, both counts
are at least one, hence their minimum is nondegenerate.  No probability
conclusion occurs in this module.
-/

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

def positiveCollisionParents
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) : Finset parent :=
  L.activeParents.filter fun p => 0 < parentCollisionMean L motionRadius p

def collisionRepetitions
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) : Nat :=
  if h : (positiveCollisionParents L motionRadius).Nonempty then
    Nat.floor ((positiveCollisionParents L motionRadius).inf' h fun p =>
      (commonHundredNeighbourPackingConstant : Real) /
        parentCollisionMean L motionRadius p)
  else 1

theorem collisionRepetitions_mul_mean_le_cap
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) :
    forall p, p ∈ L.activeParents ->
      (collisionRepetitions L motionRadius : Real) *
          parentCollisionMean L motionRadius p <=
        (commonHundredNeighbourPackingConstant : Real) := by
  intro p hp
  have hcapNonneg : (0 : Real) <= commonHundredNeighbourPackingConstant :=
    Nat.cast_nonneg _
  by_cases hmeanPos : 0 < parentCollisionMean L motionRadius p
  · have hppos : p ∈ positiveCollisionParents L motionRadius :=
      Finset.mem_filter.mpr ⟨hp, hmeanPos⟩
    have hpositive : (positiveCollisionParents L motionRadius).Nonempty :=
      ⟨p, hppos⟩
    let budget : Real :=
      (positiveCollisionParents L motionRadius).inf' hpositive fun q =>
        (commonHundredNeighbourPackingConstant : Real) /
          parentCollisionMean L motionRadius q
    have hbudgetNonneg : 0 <= budget := by
      apply Finset.le_inf' hpositive
      intro q hq
      exact div_nonneg hcapNonneg
        (parentCollisionMean_nonneg L motionRadius q)
    have hfloor : (Nat.floor budget : Real) <= budget :=
      Nat.floor_le hbudgetNonneg
    have hbudgetp : budget <=
        (commonHundredNeighbourPackingConstant : Real) /
          parentCollisionMean L motionRadius p :=
      Finset.inf'_le
        (fun q => (commonHundredNeighbourPackingConstant : Real) /
          parentCollisionMean L motionRadius q) hppos
    have hJ : (collisionRepetitions L motionRadius : Real) =
        Nat.floor budget := by
      simp only [collisionRepetitions, dif_pos hpositive, budget]
    rw [hJ]
    exact (le_div_iff₀ hmeanPos).mp (hfloor.trans hbudgetp)
  · have hmeanZero : parentCollisionMean L motionRadius p = 0 :=
      le_antisymm (le_of_not_gt hmeanPos)
        (parentCollisionMean_nonneg L motionRadius p)
    simp [hmeanZero, hcapNonneg]

theorem one_le_collisionRepetitions_of_mean_le_cap
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal)
    (hunit : forall p, p ∈ L.activeParents ->
      parentCollisionMean L motionRadius p <=
        (commonHundredNeighbourPackingConstant : Real)) :
    1 <= collisionRepetitions L motionRadius := by
  by_cases hpositive :
      (positiveCollisionParents L motionRadius).Nonempty
  · rw [collisionRepetitions, dif_pos hpositive]
    apply Nat.le_floor
    apply Finset.le_inf' hpositive
    intro p hp
    have hpactive : p ∈ L.activeParents := (Finset.mem_filter.mp hp).1
    have hmpos : 0 < parentCollisionMean L motionRadius p :=
      (Finset.mem_filter.mp hp).2
    exact (le_div_iff₀ hmpos).2 (by simpa using hunit p hpactive)
  · simp [collisionRepetitions, hpositive]

/-- One `J` satisfying both source estimates. -/
def jointRepetitions
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) : Nat :=
  min
    (paperRepetitions L (L.paperMean motionRadius))
    (collisionRepetitions L motionRadius)

theorem jointRepetitions_le_paperRepetitions
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) :
    jointRepetitions L motionRadius <=
      paperRepetitions L (L.paperMean motionRadius) :=
  Nat.min_le_left _ _

theorem jointRepetitions_le_collisionRepetitions
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) :
    jointRepetitions L motionRadius <= collisionRepetitions L motionRadius :=
  Nat.min_le_right _ _

theorem jointRepetitions_mul_analyticMean_le_cap
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) :
    forall q, q ∈ L.activeTests ->
      (jointRepetitions L motionRadius : Real) * L.paperMean motionRadius q <=
        L.paperCap q := by
  intro q hq
  have hmean := L.paperMean_nonneg motionRadius q
  have hcast : (jointRepetitions L motionRadius : Real) <=
      paperRepetitions L (L.paperMean motionRadius) := by
    exact_mod_cast jointRepetitions_le_paperRepetitions L motionRadius
  exact (mul_le_mul_of_nonneg_right hcast hmean).trans
    (paperRepetitions_mul_mean_le_cap L (L.paperMean motionRadius)
      (fun r _hr => L.paperMean_nonneg motionRadius r) q hq)

theorem jointRepetitions_mul_collisionMean_le_cap
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) :
    forall p, p ∈ L.activeParents ->
      (jointRepetitions L motionRadius : Real) *
          parentCollisionMean L motionRadius p <=
        (commonHundredNeighbourPackingConstant : Real) := by
  intro p hp
  have hmean := parentCollisionMean_nonneg L motionRadius p
  have hcast : (jointRepetitions L motionRadius : Real) <=
      collisionRepetitions L motionRadius := by
    exact_mod_cast jointRepetitions_le_collisionRepetitions L motionRadius
  exact (mul_le_mul_of_nonneg_right hcast hmean).trans
    (collisionRepetitions_mul_mean_le_cap L motionRadius p hp)

theorem one_le_jointRepetitions
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal)
    (hanalytic : forall q, q ∈ L.activeTests ->
      L.paperMean motionRadius q <= L.paperCap q)
    (hcollision : forall p, p ∈ L.activeParents ->
      parentCollisionMean L motionRadius p <=
        (commonHundredNeighbourPackingConstant : Real)) :
    1 <= jointRepetitions L motionRadius := by
  rw [jointRepetitions]
  exact Nat.le_min.mpr ⟨
    one_le_paperRepetitions_of_mean_le_cap
      L (L.paperMean motionRadius) hanalytic,
    one_le_collisionRepetitions_of_mean_le_cap
      L motionRadius hcollision⟩

#print axioms collisionRepetitions_mul_mean_le_cap
#print axioms one_le_collisionRepetitions_of_mean_le_cap
#print axioms jointRepetitions_mul_analyticMean_le_cap
#print axioms jointRepetitions_mul_collisionMean_le_cap
#print axioms one_le_jointRepetitions

end

end FamilyStickyAllParentLayerJointRepetitionsV1
