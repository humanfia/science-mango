import FamilyStickyGrounding.FamilyStickyHierarchySuffixWidenedCollisionRoutingV1

set_option autoImplicit false

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyPathFirstDivergenceV1
open FamilyStickyHierarchySuffixWidenedCollisionRoutingV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Finite counting interface for widened cross-parent collisions

An ordered pair of distinct-path final occurrences with equal final carriers
is sent to its canonical first divergent layer.  At that layer the two paths
have one literal common prefix, different current choices, and the second
prefix-translated layer child lies in the explicit
`crossParentRoutingRadius` thickening of the first.

The resulting relation is cross-parent-capable: it deliberately imposes no
equality of hierarchy parents.  We expose it as finite partner sets, finite
per-layer ordered-pair sets, and their finite union.  The internally computed
maximum partner cardinality is named
`widenedCrossParentPackingConstant`; it is not supplied by the caller and is
bounded by the final occurrence cardinality.

The existing B8/WZ local packing constant controls a different relation: two
children in one literal parent fibre with containment in a literal
`hundredTube`.  Neither common-parent membership nor a comparison of
`crossParentRoutingRadius` with that `100`-tube radius follows here.  Thus the
new finite constant precisely isolates the remaining widened geometric
packing seam instead of silently reusing the local constant.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- A directed final-occurrence pair, represented as a sigma so its finite
cardinality decomposes exactly into partner fibres. -/
abbrev FinalOrderedPair := Sigma fun _ : C.FinalIndex => C.FinalIndex

/-- The source collision relation which must be routed: different paths and
literal equality of the two final carriers. -/
def DistinctPathFinalCarrierCollision (a b : C.FinalIndex) : Prop :=
  a.1 ≠ b.1 ∧ (C.finalTube a).carrier = (C.finalTube b).carrier

/-- Explicit layer relation produced by suffix routing.  It retains the
common-prefix and first-different-choice data as well as the widened carrier
containment, but it does not assert a common hierarchy parent. -/
def WidenedCrossParentCollisionAtLayer
    (k : Fin depth) (a b : C.FinalIndex) : Prop :=
  (forall i : Fin depth, i < k -> a.1 i = b.1 i) ∧
    a.1 k ≠ b.1 k ∧
    (prefixTranslatedLayerChild C b k).carrier ⊆
      Metric.cthickening (crossParentRoutingRadius (H := H) k : Real)
        (prefixTranslatedLayerChild C a k).carrier

/-- All widened partners of one first occurrence at one layer. -/
noncomputable def widenedCrossParentPartnersAtLayer
    (k : Fin depth) (a : C.FinalIndex) : Finset C.FinalIndex := by
  classical
  exact Finset.univ.filter fun b =>
    WidenedCrossParentCollisionAtLayer C k a b

/-- All directed widened collision pairs at one layer. -/
noncomputable def widenedCrossParentCollisionsAtLayer
    (k : Fin depth) : Finset (FinalOrderedPair C) := by
  classical
  exact Finset.univ.sigma fun a =>
    widenedCrossParentPartnersAtLayer C k a

/-- The union of the explicit widened relations over all hierarchy layers. -/
noncomputable def widenedCrossParentCollisionUnion :
    Finset (FinalOrderedPair C) := by
  classical
  exact Finset.univ.biUnion fun k =>
    widenedCrossParentCollisionsAtLayer C k

/-- All directed distinct-path exact final-carrier collisions. -/
noncomputable def distinctPathFinalCarrierCollisions :
    Finset (FinalOrderedPair C) := by
  classical
  exact Finset.univ.sigma fun a =>
    Finset.univ.filter fun b => DistinctPathFinalCarrierCollision C a b

@[simp] theorem mem_widenedCrossParentPartnersAtLayer
    (k : Fin depth) (a b : C.FinalIndex) :
    b ∈ widenedCrossParentPartnersAtLayer C k a ↔
      WidenedCrossParentCollisionAtLayer C k a b := by
  classical
  simp [widenedCrossParentPartnersAtLayer]

@[simp] theorem mem_widenedCrossParentCollisionsAtLayer
    (k : Fin depth) (q : (FinalOrderedPair C)) :
    q ∈ widenedCrossParentCollisionsAtLayer C k ↔
      WidenedCrossParentCollisionAtLayer C k q.1 q.2 := by
  classical
  simp [widenedCrossParentCollisionsAtLayer]

@[simp] theorem mem_widenedCrossParentCollisionUnion
    (q : (FinalOrderedPair C)) :
    q ∈ widenedCrossParentCollisionUnion C ↔
      exists k : Fin depth,
        WidenedCrossParentCollisionAtLayer C k q.1 q.2 := by
  classical
  simp [widenedCrossParentCollisionUnion]

@[simp] theorem mem_distinctPathFinalCarrierCollisions
    (q : (FinalOrderedPair C)) :
    q ∈ distinctPathFinalCarrierCollisions C ↔
      DistinctPathFinalCarrierCollision C q.1 q.2 := by
  classical
  simp [distinctPathFinalCarrierCollisions]

/-- A distinct-path exact final-carrier collision lies in the widened
relation at its canonical first divergence. -/
theorem distinctPathFinalCarrierCollision_at_firstDivergence
    (a b : C.FinalIndex)
    (hcollision : DistinctPathFinalCarrierCollision C a b) :
    WidenedCrossParentCollisionAtLayer C
      (hierarchyFirstDivergenceLayer C a.1 b.1 hcollision.1) a b := by
  let k := hierarchyFirstDivergenceLayer C a.1 b.1 hcollision.1
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hierarchyFirstDivergence_eq_before C a.1 b.1 hcollision.1 i hi
  · exact hierarchyFirstDivergence_choice_ne C a.1 b.1 hcollision.1
  · exact firstDivergence_layerChild_carrier_subset_crossParentWidening
      C a b hcollision.1 hcollision.2

/-- Every source collision is contained in the explicit finite union of
widened per-layer relations. -/
theorem distinctPathFinalCarrierCollisions_subset_widenedUnion :
    distinctPathFinalCarrierCollisions C ⊆
      widenedCrossParentCollisionUnion C := by
  intro q hq
  have hcollision :=
    (mem_distinctPathFinalCarrierCollisions C q).1 hq
  apply (mem_widenedCrossParentCollisionUnion C q).2
  exact ⟨hierarchyFirstDivergenceLayer C q.1.1 q.2.1 hcollision.1,
    distinctPathFinalCarrierCollision_at_firstDivergence C q.1 q.2 hcollision⟩

/-- First union bound: exact final collisions are no more numerous than the
finite widened union. -/
theorem distinctPathFinalCarrierCollisions_card_le_widenedUnion :
    (distinctPathFinalCarrierCollisions C).card <=
      (widenedCrossParentCollisionUnion C).card :=
  Finset.card_le_card
    (distinctPathFinalCarrierCollisions_subset_widenedUnion C)

/-- Second union bound: overlap between layer relations can only reduce the
cardinality of their union. -/
theorem widenedCrossParentCollisionUnion_card_le_sum_layers :
    (widenedCrossParentCollisionUnion C).card <=
      ∑ k : Fin depth,
        (widenedCrossParentCollisionsAtLayer C k).card := by
  classical
  unfold widenedCrossParentCollisionUnion
  exact Finset.card_biUnion_le

/-- Direct collision-to-layer cardinality bound. -/
theorem distinctPathFinalCarrierCollisions_card_le_sum_layers :
    (distinctPathFinalCarrierCollisions C).card <=
      ∑ k : Fin depth,
        (widenedCrossParentCollisionsAtLayer C k).card :=
  (distinctPathFinalCarrierCollisions_card_le_widenedUnion C).trans
    (widenedCrossParentCollisionUnion_card_le_sum_layers C)

/-- The actual finite widened multiplicity at one layer.  This is produced
from the explicit relation, not accepted as a cardinality callback. -/
noncomputable def widenedCrossParentPackingConstant (k : Fin depth) : Nat :=
  Finset.univ.sup fun a : C.FinalIndex =>
    (widenedCrossParentPartnersAtLayer C k a).card

theorem widenedCrossParentPartnersAtLayer_card_le_packingConstant
    (k : Fin depth) (a : C.FinalIndex) :
    (widenedCrossParentPartnersAtLayer C k a).card <=
      widenedCrossParentPackingConstant C k := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun b : C.FinalIndex =>
      (widenedCrossParentPartnersAtLayer C k b).card)
    (Finset.mem_univ a)

/-- Finiteness alone gives a transparent fallback bound for the new
hierarchy-dependent packing constant. -/
theorem widenedCrossParentPackingConstant_le_finalIndex_card
    (k : Fin depth) :
    widenedCrossParentPackingConstant C k <= Fintype.card C.FinalIndex := by
  unfold widenedCrossParentPackingConstant
  apply Finset.sup_le
  intro a _ha
  exact Finset.card_le_card fun b _hb => Finset.mem_univ b

/-- Per-layer directed widened pairs are controlled by the number of first
occurrences times the new maximal widened partner multiplicity. -/
theorem widenedCrossParentCollisionsAtLayer_card_le
    (k : Fin depth) :
    (widenedCrossParentCollisionsAtLayer C k).card <=
      Fintype.card C.FinalIndex * widenedCrossParentPackingConstant C k := by
  classical
  unfold widenedCrossParentCollisionsAtLayer
  rw [Finset.card_sigma]
  calc
    (∑ a ∈ Finset.univ,
        (widenedCrossParentPartnersAtLayer C k a).card) <=
      ∑ _a ∈ (Finset.univ : Finset C.FinalIndex),
        widenedCrossParentPackingConstant C k := by
      exact Finset.sum_le_sum fun a _ha =>
        widenedCrossParentPartnersAtLayer_card_le_packingConstant C k a
    _ = Fintype.card C.FinalIndex *
        widenedCrossParentPackingConstant C k := by simp

/-- Final callback-free counting interface.  A future geometric packing
theorem only has to replace the explicit widened constants by a uniform
dimension/scale bound. -/
theorem distinctPathFinalCarrierCollisions_card_le_packingConstants :
    (distinctPathFinalCarrierCollisions C).card <=
      Fintype.card C.FinalIndex *
        ∑ k : Fin depth, widenedCrossParentPackingConstant C k := by
  calc
    (distinctPathFinalCarrierCollisions C).card <=
        ∑ k : Fin depth,
          (widenedCrossParentCollisionsAtLayer C k).card :=
      distinctPathFinalCarrierCollisions_card_le_sum_layers C
    _ <= ∑ k : Fin depth,
        Fintype.card C.FinalIndex *
          widenedCrossParentPackingConstant C k := by
      exact Finset.sum_le_sum fun k _hk =>
        widenedCrossParentCollisionsAtLayer_card_le C k
    _ = Fintype.card C.FinalIndex *
        ∑ k : Fin depth, widenedCrossParentPackingConstant C k := by
      rw [Finset.mul_sum]

#print axioms distinctPathFinalCarrierCollision_at_firstDivergence
#print axioms distinctPathFinalCarrierCollisions_subset_widenedUnion
#print axioms distinctPathFinalCarrierCollisions_card_le_sum_layers
#print axioms widenedCrossParentPartnersAtLayer_card_le_packingConstant
#print axioms widenedCrossParentPackingConstant_le_finalIndex_card
#print axioms widenedCrossParentCollisionsAtLayer_card_le
#print axioms distinctPathFinalCarrierCollisions_card_le_packingConstants

end
end FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1
