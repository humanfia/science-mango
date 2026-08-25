import FamilyStickyGrounding.FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1

set_option autoImplicit false

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyWidenedCrossParentSourceBoundV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Hierarchy-source bound for widened cross-parent multiplicity

Fixing the first occurrence and a layer fixes every path coordinate strictly
before that layer.  A widened partner is therefore encoded injectively by:

* its remaining path choices from the current layer through the suffix; and
* its original active fine source index.

The hierarchy branching-product theorem then bounds the latter by the actual
parent count at level `k + 1` times the product of branching factors from
level zero through `k`.  This replaces the fallback `Kwide <= #FinalIndex`
by an explicit source-data bound with the already fixed prefix removed.

No load, probability, packing-cardinality, or final-cardinality callback is
an input.  The existing WZ separation is fibrewise and does not improve the
cross-parent factor: singleton parent fibres make it vacuous.  The finite
countermodel at the end records the resulting sharp parent/repetition
obstruction.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- Layers at or after `k`; these are exactly the path coordinates not fixed
by the first-divergence prefix condition. -/
abbrev SuffixLayer (k : Fin depth) := {i : Fin depth // k <= i}

/-- Remaining dependent path choices from layer `k` onward. -/
abbrev SuffixChoice (k : Fin depth) :=
  forall i : SuffixLayer k,
    Fin (C.output.toComposition.repetitions i.1)

/-- Explicit product of all remaining repetition counts. -/
def suffixRepetitionProduct (k : Fin depth) : Nat :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin depth => k <= i),
    C.output.toComposition.repetitions i

theorem suffixChoice_card (k : Fin depth) :
    Fintype.card (SuffixChoice C k) = suffixRepetitionProduct C k := by
  classical
  unfold SuffixChoice suffixRepetitionProduct SuffixLayer
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  simpa only [Finset.subtype_univ] using
    (Finset.prod_subtype_eq_prod_filter
      (s := (Finset.univ : Finset (Fin depth)))
      (p := fun i : Fin depth => k <= i)
      (f := fun i => C.output.toComposition.repetitions i))

/-- Actual active hierarchy parent count at the next level. -/
def hierarchyLayerParentCount (k : Fin depth) : Nat :=
  (H.step k.1 k.2).combinatorics.index.coarse.card

/-- Source-data-only widened multiplicity bound at one layer. -/
def widenedCrossParentSourceBound (k : Fin depth) : Nat :=
  suffixRepetitionProduct C k *
    (hierarchyLayerParentCount (H := H) k *
      H.branchingProduct 0 (k.1 + 1) (by omega))

/-- The initial active fine source cardinality is controlled by the current
parent count and the honest prefix branching product. -/
theorem initialFine_card_le_parentCount_mul_branchingProduct
    (k : Fin depth) :
    (H.family 0).refinement.refined.card <=
      hierarchyLayerParentCount (H := H) k *
        H.branchingProduct 0 (k.1 + 1) (by omega) := by
  have h := H.activeCard_le_mul_branchingProduct
    0 (k.1 + 1) (by omega)
  unfold hierarchyLayerParentCount
  rw [(H.step k.1 k.2).combinatorics.coarse_eq_refined]
  have hfamily :
      (H.family (0 + (k.1 + 1))).refinement.refined.card =
        (H.family (k.1 + 1)).refinement.refined.card := by
    exact congrArg
      (fun l => (H.family l).refinement.refined.card)
      (Nat.zero_add (k.1 + 1))
  rw [hfamily] at h
  exact h

/-- Encode a widened partner by its unfixed suffix choices and its original
fine source index. -/
def widenedPartnerSuffixSourceCode
    (k : Fin depth) (a : C.FinalIndex) :
    {b // b ∈ widenedCrossParentPartnersAtLayer C k a} ->
      SuffixChoice C k ×
        {i // i ∈ (H.family 0).refinement.refined} :=
  fun b =>
    ⟨fun i => b.1.1 i.1, b.1.2⟩

theorem widenedPartnerSuffixSourceCode_injective
    (k : Fin depth) (a : C.FinalIndex) :
    Function.Injective (widenedPartnerSuffixSourceCode C k a) := by
  intro b c hcode
  apply Subtype.ext
  apply Prod.ext
  · funext i
    by_cases hi : k <= i
    · have hsuffix := congrArg Prod.fst hcode
      exact congrFun hsuffix ⟨i, hi⟩
    · have hb :=
        (mem_widenedCrossParentPartnersAtLayer C k a b.1).1 b.2
      have hc :=
        (mem_widenedCrossParentPartnersAtLayer C k a c.1).1 c.2
      have hik : i < k := lt_of_not_ge hi
      exact (hb.1 i hik).symm.trans (hc.1 i hik)
  · simpa [widenedPartnerSuffixSourceCode] using congrArg Prod.snd hcode

/-- Prefix removal already improves each partner fibre from all paths to only
the suffix path product. -/
theorem widenedCrossParentPartnersAtLayer_card_le_suffix_mul_initialFine
    (k : Fin depth) (a : C.FinalIndex) :
    (widenedCrossParentPartnersAtLayer C k a).card <=
      Fintype.card (SuffixChoice C k) *
        (H.family 0).refinement.refined.card := by
  classical
  have hcard := Fintype.card_le_of_injective
    (widenedPartnerSuffixSourceCode C k a)
    (widenedPartnerSuffixSourceCode_injective C k a)
  simpa only [Fintype.card_coe, Fintype.card_prod] using hcard

/-- Main source bound: suffix repetitions times current parent count times
the certified prefix branching product. -/
theorem widenedCrossParentPartnersAtLayer_card_le_sourceBound
    (k : Fin depth) (a : C.FinalIndex) :
    (widenedCrossParentPartnersAtLayer C k a).card <=
      widenedCrossParentSourceBound C k := by
  calc
    (widenedCrossParentPartnersAtLayer C k a).card <=
        Fintype.card (SuffixChoice C k) *
          (H.family 0).refinement.refined.card :=
      widenedCrossParentPartnersAtLayer_card_le_suffix_mul_initialFine C k a
    _ = suffixRepetitionProduct C k *
        (H.family 0).refinement.refined.card := by
      rw [suffixChoice_card C k]
    _ <= suffixRepetitionProduct C k *
        (hierarchyLayerParentCount (H := H) k *
          H.branchingProduct 0 (k.1 + 1) (by omega)) :=
      Nat.mul_le_mul_left _
        (initialFine_card_le_parentCount_mul_branchingProduct (H := H) k)
    _ = widenedCrossParentSourceBound C k := rfl

/-- The internally computed widened packing constant obeys the same explicit
hierarchy-source bound. -/
theorem widenedCrossParentPackingConstant_le_sourceBound
    (k : Fin depth) :
    widenedCrossParentPackingConstant C k <=
      widenedCrossParentSourceBound C k := by
  unfold widenedCrossParentPackingConstant
  apply Finset.sup_le
  intro a _ha
  exact widenedCrossParentPartnersAtLayer_card_le_sourceBound C k a

/-- Global collision bound with no final-index cardinal on the right except
for the unavoidable number of possible first occurrences. -/
theorem distinctPathFinalCarrierCollisions_card_le_sourceBounds :
    (distinctPathFinalCarrierCollisions C).card <=
      Fintype.card C.FinalIndex *
        ∑ k : Fin depth, widenedCrossParentSourceBound C k := by
  calc
    (distinctPathFinalCarrierCollisions C).card <=
        Fintype.card C.FinalIndex *
          ∑ k : Fin depth, widenedCrossParentPackingConstant C k :=
      distinctPathFinalCarrierCollisions_card_le_packingConstants C
    _ <= Fintype.card C.FinalIndex *
        ∑ k : Fin depth, widenedCrossParentSourceBound C k := by
      gcongr with k
      exact widenedCrossParentPackingConstant_le_sourceBound C k

/-!
## Sharp interface-level obstruction

Take `J` current choices and `P` singleton parent fibres.  Put identical unit
tubes in the distinct parents and use zero current motion.  WZ separation in
each singleton fibre is vacuous, while every occurrence with a different
current choice satisfies the widened containment.  The following finite
model records the resulting `(J - 1) * P` partner multiplicity; requiring the
second parent to be different still leaves `(J - 1) * (P - 1)` partners.
-/

/-- Abstract occurrence coordinates in the singleton-parent obstruction. -/
abbrev UnitCrossParentOccurrence (J P : Nat) := Fin J × Fin P

/-- Every different current choice is a widened partner; the parent label is
unrestricted because the geometric relation is cross-parent-capable. -/
noncomputable def unitCrossParentPartners
    {J P : Nat} (a : UnitCrossParentOccurrence J P) :
    Finset (UnitCrossParentOccurrence J P) := by
  classical
  exact Finset.univ.filter fun b => b.1 ≠ a.1

/-- Strictly cross-parent part of the same obstruction. -/
noncomputable def strictUnitCrossParentPartners
    {J P : Nat} (a : UnitCrossParentOccurrence J P) :
    Finset (UnitCrossParentOccurrence J P) := by
  classical
  exact Finset.univ.filter fun b => b.1 ≠ a.1 ∧ b.2 ≠ a.2

theorem unitCrossParentPartners_card
    {J P : Nat} (a : UnitCrossParentOccurrence J P) :
    (unitCrossParentPartners a).card = (J - 1) * P := by
  classical
  rw [show unitCrossParentPartners a =
      (Finset.univ.erase a.1).product Finset.univ by
    ext b
    simp [unitCrossParentPartners]]
  simp

theorem strictUnitCrossParentPartners_card
    {J P : Nat} (a : UnitCrossParentOccurrence J P) :
    (strictUnitCrossParentPartners a).card =
      (J - 1) * (P - 1) := by
  classical
  rw [show strictUnitCrossParentPartners a =
      (Finset.univ.erase a.1).product (Finset.univ.erase a.2) by
    ext b
    simp [strictUnitCrossParentPartners]]
  simp

/-- WZ-type pairwise separation places no restriction on a singleton parent
fibre, for any proposed separation relation. -/
theorem singletonParent_pairwise_vacuous
    {alpha : Type*} (x : alpha) (R : alpha -> alpha -> Prop) :
    Set.Pairwise ({x} : Set alpha) R := by
  simp [Set.Pairwise]

/-- Identical tubes automatically satisfy every nonnegative widened carrier
containment, including the unit term in `crossParentRoutingRadius`. -/
theorem identicalTube_widenedContainment
    {delta r : NNReal} (T : Tube delta) :
    T.carrier ⊆ Metric.cthickening (r : Real) T.carrier :=
  Metric.self_subset_cthickening T.carrier

#print axioms suffixChoice_card
#print axioms initialFine_card_le_parentCount_mul_branchingProduct
#print axioms widenedPartnerSuffixSourceCode_injective
#print axioms widenedCrossParentPackingConstant_le_sourceBound
#print axioms distinctPathFinalCarrierCollisions_card_le_sourceBounds
#print axioms unitCrossParentPartners_card
#print axioms strictUnitCrossParentPartners_card
#print axioms singletonParent_pairwise_vacuous
#print axioms identicalTube_widenedContainment

end
end FamilyStickyHierarchyWidenedCrossParentSourceBoundV1
