import Family8Grounding.Family8GreedyHighPrefixActualOccurrenceV1
import Family8Grounding.Family8SelectedParentJohnPlankProductionV18
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankProductionV18
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-!
# Exact high-occurrence to selected-parent John/plank connector

The active parent family and its literal parent-aggregated shading form an
actual tube datum at scale `rho`.  Restricting this datum to a greedy block is
definitionally the selected parent family and shading used by the V18
John/plank constructor.  Consequently a dependent high-occurrence
certificate for an index and a block `q` can be consumed at that *same* `q`;
there is no re-selection, reindexing, or equality callback.
-/

/-- The actual datum whose indices are the active parents of `S`, with the
literal parent-aggregated shading. -/
def activeParentActualTubeDatum
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    ActualTubeDatum rho (ActiveParentIndex S) where
  family :=
    { tubes := fun p => S.coarse.tubes p.1
      refinement := UniformRefinement.ofFinset Finset.univ }
  shading := parentAggregatedShading S Y

@[simp] theorem activeParentActualTubeDatum_family_bodyFamily
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (activeParentActualTubeDatum S Y).family.bodyFamily =
      S.activeCoarseFamily :=
  rfl

/-- Restriction of the active-parent datum has exactly the selected-parent
body family used downstream. -/
@[simp] theorem restrict_activeParentActualTubeDatum_family_bodyFamily
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) :
    (restrictActualTubeDatum (activeParentActualTubeDatum S Y) B).family.bodyFamily =
      selectedCoarseFamily S.activeCoarseFamily B :=
  rfl

/-- Restriction of the active-parent datum has exactly the actual selected
parent shading used by V18. -/
@[simp] theorem restrict_activeParentActualTubeDatum_shading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) :
    (restrictActualTubeDatum (activeParentActualTubeDatum S Y) B).shading =
      selectedParentActualShading S Y B :=
  rfl

/-- A high occurrence at `q` is already the V18 selected parent block at the
same `q`.  In particular its constant-one Frostman conclusion needs no
transport beyond definitional reduction. -/
theorem actualHighOccurrence_isFrostmanIn_selectedParentBlock
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks S.activeCoarseFamily P).length)
    (hocc : ActualHighConcentrationOccurrence
      (activeParentActualTubeDatum S Y) P A q) :
    A < blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q) ∧
      IsFrostmanIn 1
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q).fiber)
        (blockAt S.activeCoarseFamily P q).body := by
  exact ⟨hocc.1, hocc.2.2⟩

/-- Consume one dependent `q`-block certificate from the high branch in the
literal V18 constructor.  The input `hplank` is exactly V18's genuine
memberwise plank premise, and the output retains the originating index's
membership, high density, constant-one Frostman certificate, and the exact
average-multiplicity identification. -/
theorem exists_selectedParentJohnPlankFamily_of_qBlockCertificate
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks S.activeCoarseFamily P).length)
    (i : ActiveParentIndex S)
    (hiq : i ∈ (blockAt S.activeCoarseFamily P q).fiber)
    (hocc : ActualHighConcentrationOccurrence
      (activeParentActualTubeDatum S Y) P A q)
    (C a b : NNReal)
    (hplank : ∀ p :
        {p // p ∈ (blockAt S.activeCoarseFamily P q).fiber},
      IsPlank C a b
        (selectedParentAffineFamily
          (selectedParentGreedyBlockJohnFrame S hrho P q).affineEquiv S
          (blockAt S.activeCoarseFamily P q).fiber p)) :
    ∃ Q : ShadedConvexPlankFamily
        {p // p ∈ (blockAt S.activeCoarseFamily P q).fiber} a b,
      i ∈ (blockAt S.activeCoarseFamily P q).fiber ∧
      Q.shading.averageMultiplicity =
        (selectedParentActualShading S Y
          (blockAt S.activeCoarseFamily P q).fiber).averageMultiplicity ∧
      A < blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q) ∧
      IsFrostmanIn 1
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q).fiber)
        (blockAt S.activeCoarseFamily P q).body := by
  let Q := selectedParentGreedyBlockJohnPlankFamily
    S Y hrho P q C a b hplank
  refine ⟨Q, hiq, ?_, ?_⟩
  · exact selectedParentGreedyBlockJohnPlankFamily_averageMultiplicity
      S Y hrho P q C a b hplank
  · exact actualHighOccurrence_isFrostmanIn_selectedParentBlock
      S Y P A q hocc

#print axioms activeParentActualTubeDatum
#print axioms activeParentActualTubeDatum_family_bodyFamily
#print axioms restrict_activeParentActualTubeDatum_family_bodyFamily
#print axioms restrict_activeParentActualTubeDatum_shading
#print axioms actualHighOccurrence_isFrostmanIn_selectedParentBlock
#print axioms exists_selectedParentJohnPlankFamily_of_qBlockCertificate

end
end Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
