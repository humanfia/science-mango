import Family8Grounding.Family8ExactAssemblySourceAverageRetentionV1
import Family8Grounding.Family8IdentifiedDividingWitnessFirstOuterParentTransportV1
import Family8Grounding.Family8SelectedParentGreedyBlockFiberIdentityV2
import Mathlib.Tactic

/-!
# Source-to-tau transport into the same greedy exact assembly

The source Katz--Tao fibre cap first transports the original average to the
actual tau-parent shading.  The greedy occurrence factorization is active on
the whole tau-parent index type, so exact-assembly retention then transports
that same average to the literal refinement estimated by the Eq45/Eq46 line.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SourceTauGreedyExactAssemblyRetainedProductV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Family8ExactAssemblySourceAverageRetentionV1.ExactAssembly
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

/-- The actual source-to-tau first factor and the exact assembly's genuine
retention loss compose on the same greedy refinement consumed by Eq45/Eq46. -/
theorem fullRefinement_averageMultiplicity_le_firstCap_mul_loss_mul_greedyRefinement
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family C N
        stoppingEpsilon stoppingEta Sseq)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) C Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) C Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) C Sseq W).activeCoarseFamily)
      Finset.univ)
    {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) C Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) C Sseq W)
        (fullRefinementDatum D).shading) loss)
    {etaKT : Real} (hKT : KatzTaoHypotheses D etaKT) :
    D.shading.averageMultiplicity ≤
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (Sseq.tau W.m)
          ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
        ((loss : ENNReal) * A.refinement.shading.averageMultiplicity) := by
  have hfirst :=
    fullRefinement_averageMultiplicity_le_hypothesisCap_mul_sourceTauParent
      D hD C Sseq W.m hKT
  have hretained :=
    restrictTo_source_averageMultiplicity_le_loss_mul_refinement A
  have hfine :
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) C Sseq W)
        Pgreedy).index.fine = Finset.univ := by
    rfl
  have hmiddle :
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) C Sseq W)
        (fullRefinementDatum D).shading).averageMultiplicity ≤
        (loss : ENNReal) * A.refinement.shading.averageMultiplicity := by
    rw [hfine, restrictTo_univ_averageMultiplicity] at hretained
    exact hretained
  exact hfirst.trans (mul_le_mul' le_rfl hmiddle)

#print axioms
  fullRefinement_averageMultiplicity_le_firstCap_mul_loss_mul_greedyRefinement

end
end Family8SourceTauGreedyExactAssemblyRetainedProductV1
