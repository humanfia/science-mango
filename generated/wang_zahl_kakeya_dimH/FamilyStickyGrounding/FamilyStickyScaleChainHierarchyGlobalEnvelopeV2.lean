import FamilyStickyGrounding.FamilyStickyScaleChainSelectedNumericalAllocationProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainHierarchyGlobalEnvelopeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy

noncomputable section

/-!
# Hierarchy envelope for the actual global scale-chain product

The local `fiberDeltaMax` in an effective hierarchy step is bounded by the
certified branching factor of that same step.  Multiplying these pointwise
bounds gives a completely explicit hierarchy envelope for the actual global
product.  The test-body dimensional losses and endpoint normalization remain
visible: combinatorial branching alone does not control them.
-/

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {card : Nat -> Nat}

/-- The genuine fiber `Delta_max` of an effective hierarchy cover is bounded
by the certified one-step branching factor. -/
theorem effective_fiberDeltaMax_le_branchingFactor
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l)))
    (l : Nat) (hl : l < depth) :
    fiberDeltaMax (effectiveStickyScaleCover H l hl) <=
      ((H.step l hl).combinatorics.branchingFactor : ENNReal) := by
  apply fiberDeltaMax_le
  intro k hk
  calc
    maximalConcentration
        ((effectiveStickyScaleCover H l hl).fiberFamily k) <=
        (Fintype.card
          {i // i ∈ (effectiveStickyScaleCover H l hl).fiber k} :
            ENNReal) :=
      maximalConcentration_le_card
        ((effectiveStickyScaleCover H l hl).fiberFamily k)
    _ = ((effectiveStickyScaleCover H l hl).fiber k).card := by
      exact_mod_cast Fintype.card_coe
        ((effectiveStickyScaleCover H l hl).fiber k)
    _ <= ((H.step l hl).combinatorics.index.fiber k).card := by
      exact_mod_cast Finset.card_le_card (by
        intro i hi
        have hiPrime :=
          (effectiveStickyScaleCover H l hl).mem_fiber i k |>.mp hi
        apply (H.step l hl).combinatorics.index.mem_fiber i k |>.mpr
        refine ⟨?_, hiPrime.2⟩
        rw [(H.step l hl).combinatorics.fine_eq_refined]
        exact hiPrime.1)
    _ <= ((H.step l hl).combinatorics.branchingFactor : ENNReal) := by
      exact_mod_cast
        (H.step l hl).combinatorics.fiber_card_le_loss_mul_branching
          k (by
            rw [(H.step l hl).combinatorics.coarse_eq_refined]
            exact hk)

end MultiscaleTubeHierarchy

variable {outerDepth chainDepth : Nat}

/-- The hierarchy-visible upper envelope for the literal selected global
product.  Each local `fiberDeltaMax` is replaced by its certified branching
factor; the dimensional and endpoint losses are deliberately retained. -/
def hierarchyGlobalEnvelopeAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) : ENNReal :=
  (∏ l ∈ Finset.range chainDepth,
    (B.datum m).dimensionalLoss l *
      if hl : l < chainDepth then
        ((B.hierarchy m).step l hl).combinatorics.branchingFactor
      else 1) *
    actualGlobalEndpointRatioAt B m

/-- The actual global product is bounded by the explicit hierarchy envelope
at every selected outer interval. -/
theorem actualGlobalProductAt_le_hierarchyGlobalEnvelopeAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) :
    actualGlobalProductAt B m <= hierarchyGlobalEnvelopeAt B m := by
  unfold actualGlobalProductAt hierarchyGlobalEnvelopeAt
  apply mul_le_mul' ?_ le_rfl
  apply Finset.prod_le_prod
  · intro l hl
    exact bot_le
  · intro l hl
    have hlt : l < chainDepth := Finset.mem_range.mp hl
    simp only [
      FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor,
      dif_pos hlt]
    exact mul_le_mul' le_rfl
      (MultiscaleTubeHierarchy.effective_fiberDeltaMax_le_branchingFactor
        (B.hierarchy m) l hlt)

#print axioms MultiscaleTubeHierarchy.effective_fiberDeltaMax_le_branchingFactor
#print axioms hierarchyGlobalEnvelopeAt
#print axioms actualGlobalProductAt_le_hierarchyGlobalEnvelopeAt

end
end FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
