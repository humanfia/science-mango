import FamilyStickyGrounding.FamilyStickyHierarchyTerminalCarrierDedupV1
import FamilyStickyGrounding.FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
import FamilyStickyGrounding.FamilyStickyHierarchyLevelWZSeparationCoreV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyTerminalSamePathWZEliminationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Removing the terminal same-path source-cardinality loss by WZ packing

For a fixed initial source, every source with the same literal carrier lies
in one literal `100`-tube container.  Level-zero pairwise WZ endpoint
separation therefore injects this exact-carrier fibre into the existing
common-neighbour packing set.  Its cardinality is bounded by the fixed WZ
constant, independently of the total source cardinality.

This replaces `initialSourceExactCarrierMultiplicity` in every terminal
representative cardinality and weighted-load endpoint by
`commonHundredNeighbourPackingConstant`.  No multiplicity, packing-cardinality,
or terminal-load conclusion is supplied by the caller.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- The exact-carrier fibre, regarded as a uniform family solely for applying
the source packing theorem. -/
def initialSourceExactCarrierFamily
    (i : InitialActiveSource (H := H)) :
    UniformTubeFamily (H.effectiveRadius 0)
      (InitialSourceExactCarrierFiber (H := H) i) where
  tubes := fun j => (H.effectiveFamily 0).tubes j.1.1
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem initialSourceExactCarrierFamily_tubes
    (i : InitialActiveSource (H := H))
    (j : InitialSourceExactCarrierFiber (H := H) i) :
    (initialSourceExactCarrierFamily (H := H) i).tubes j =
      (H.effectiveFamily 0).tubes j.1.1 := rfl

/-- Carrier equality gives the entire exact fibre one literal common
hundred-fold container, centred on the distinguished source tube. -/
def initialSourceExactCarrierSharedHundredContainer
    (i : InitialActiveSource (H := H)) :
    SharedHundredSourceContainer
      (initialSourceExactCarrierFamily (H := H) i) where
  container := (H.effectiveFamily 0).tubes i.1
  carrier_subset := by
    intro j
    change ((H.effectiveFamily 0).tubes j.1.1).carrier <=
      (hundredTube ((H.effectiveFamily 0).tubes i.1)).carrier
    rw [j.2]
    exact carrier_subset_hundredTube _

/-- Level-zero WZ separation restricts to every exact-carrier source fibre. -/
theorem initialSourceExactCarrierFamily_pairwise_WZSeparated
    (W : HierarchyLevelWZSeparationData H)
    (i : InitialActiveSource (H := H)) :
    Set.Pairwise
      (Set.univ : Set (InitialSourceExactCarrierFiber (H := H) i))
      fun a b => WZEndpointParameterSeparated
        ((initialSourceExactCarrierFamily (H := H) i).tubes a)
        ((initialSourceExactCarrierFamily (H := H) i).tubes b) := by
  intro a _ha b _hb hab
  have habIndex : a.1.1 ≠ b.1.1 := by
    intro hindex
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    exact hindex
  exact W.separated 0 (Nat.zero_le depth) a.1.2 b.1.2 habIndex

/-- Each same-carrier source fibre has the fixed dimension-only WZ size. -/
theorem initialSourceExactCarrierFiber_card_le_WZConstant
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (i : InitialActiveSource (H := H)) :
    Fintype.card (InitialSourceExactCarrierFiber (H := H) i) <=
      commonHundredNeighbourPackingConstant := by
  exact fintype_card_le_commonHundredNeighbourPackingConstant
    (initialSourceExactCarrierFamily (H := H) i) hdelta
    (initialSourceExactCarrierFamily_pairwise_WZSeparated (H := H) W i)
    (initialSourceExactCarrierSharedHundredContainer (H := H) i)

/-- The computed same-path supremum is itself bounded by the fixed WZ
packing constant. -/
theorem initialSourceExactCarrierMultiplicity_le_WZConstant
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    initialSourceExactCarrierMultiplicity (H := H) <=
      commonHundredNeighbourPackingConstant := by
  unfold initialSourceExactCarrierMultiplicity
  apply Finset.sup_le
  intro i _hi
  exact initialSourceExactCarrierFiber_card_le_WZConstant
    (H := H) hdelta W i

/-- Terminal exact-carrier loss with no dependence on the source
cardinality. -/
def terminalExactCarrierWZMultiplicityBound : Nat :=
  commonHundredNeighbourPackingConstant +
    ∑ k : Fin depth, widenedCrossParentPackingConstant C k

theorem terminalExactCarrierMultiplicityBound_le_WZMultiplicityBound
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    terminalExactCarrierMultiplicityBound C <=
      terminalExactCarrierWZMultiplicityBound C := by
  unfold terminalExactCarrierMultiplicityBound
    terminalExactCarrierWZMultiplicityBound
  exact Nat.add_le_add_right
    (initialSourceExactCarrierMultiplicity_le_WZConstant
      (H := H) hdelta W) _

/-- Exact terminal fibres now have a fixed WZ same-path term plus the honest
first-divergence widened terms. -/
theorem terminalExactCarrierFiber_card_le_WZMultiplicityBound
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (a : C.FinalIndex) :
    Fintype.card (TerminalExactCarrierFiber C a) <=
      terminalExactCarrierWZMultiplicityBound C := by
  exact (terminalExactCarrierFiber_card_le C a).trans
    (terminalExactCarrierMultiplicityBound_le_WZMultiplicityBound
      C hdelta W)

/-- Exact-carrier representative count with the source-cardinality seam
removed. -/
theorem finalIndex_card_le_WZMultiplicity_mul_representatives
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card C.FinalIndex <=
      terminalExactCarrierWZMultiplicityBound C *
        (terminalRepresentatives C).card := by
  exact (finalIndex_card_le_terminalMultiplicity_mul_representatives C).trans
    (Nat.mul_le_mul_right _
      (terminalExactCarrierMultiplicityBound_le_WZMultiplicityBound
        C hdelta W))

/-- Carrier-dependent weighted loads obey the same fixed WZ terminal loss. -/
theorem terminal_weighted_load_le_WZMultiplicity_mul_representative_load
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (w : Set Space -> Nat) :
    (∑ a : C.FinalIndex, w (terminalCarrier C a)) <=
      terminalExactCarrierWZMultiplicityBound C *
        ∑ a ∈ terminalRepresentatives C, w (terminalCarrier C a) := by
  exact (terminal_weighted_load_le_mul_representative_load C w).trans
    (Nat.mul_le_mul_right _
      (terminalExactCarrierMultiplicityBound_le_WZMultiplicityBound
        C hdelta W))

/-- The two-stage strong-refinement endpoint inherits the same removal of
the global source-cardinality term. -/
theorem finalIndex_card_le_WZMultiplicity_mul_terminalStrongRepresentatives
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card C.FinalIndex <=
      terminalExactCarrierWZMultiplicityBound C *
        (terminalStrongMultiplicity C *
          (terminalStrongRepresentatives C).card) := by
  exact (finalIndex_card_le_terminalStrongRepresentatives C).trans
    (Nat.mul_le_mul_right _
      (terminalExactCarrierMultiplicityBound_le_WZMultiplicityBound
        C hdelta W))

#print axioms initialSourceExactCarrierFamily_tubes
#print axioms initialSourceExactCarrierFamily_pairwise_WZSeparated
#print axioms initialSourceExactCarrierFiber_card_le_WZConstant
#print axioms initialSourceExactCarrierMultiplicity_le_WZConstant
#print axioms terminalExactCarrierMultiplicityBound_le_WZMultiplicityBound
#print axioms terminalExactCarrierFiber_card_le_WZMultiplicityBound
#print axioms finalIndex_card_le_WZMultiplicity_mul_representatives
#print axioms terminal_weighted_load_le_WZMultiplicity_mul_representative_load
#print axioms finalIndex_card_le_WZMultiplicity_mul_terminalStrongRepresentatives

end
end FamilyStickyHierarchyTerminalSamePathWZEliminationV1
