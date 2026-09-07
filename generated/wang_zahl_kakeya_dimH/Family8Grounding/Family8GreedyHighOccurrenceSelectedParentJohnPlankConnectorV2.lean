import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankProductionV18
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-!
# High greedy block to V18 without active-parent admissibility

Every greedy occurrence block is constant-one Frostman in its literal
winning hull.  Applying the generic restriction adapter to the active-parent
datum is therefore purely definitional and needs no admissibility hypothesis.
The same block index `q` is then consumed by the V18 John/plank constructor.
-/

/-- The selected parent family on any literal greedy occurrence is
constant-one Frostman in that occurrence's winning hull.  This is automatic
from the greedy partition and does not use `ActualTubeDatum.IsAdmissible`. -/
theorem selectedParentBlock_isFrostmanIn_one
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length) :
    IsFrostmanIn 1
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q).fiber)
      (blockAt S.activeCoarseFamily P q).body := by
  apply isFrostmanIn_restrictActualTubeDatum_of_isFrostmanOn
    (activeParentActualTubeDatum S Y)
    (blockAt S.activeCoarseFamily P q).fiber
    (blockAt S.activeCoarseFamily P q).body 1
  exact blockAt_isFrostmanOn_one_of_subset
    S.activeCoarseFamily Finset.univ P (fun _ hi => hi) q

/-- Consume one high-density `q`-block directly in V18.  The theorem accepts
only the genuine high-density inequality, the originating index membership,
positive parent scale, and V18's unchanged memberwise plank premise. -/
theorem exists_selectedParentJohnPlankFamily_of_high_qBlock
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks S.activeCoarseFamily P).length)
    (i : ActiveParentIndex S)
    (hiq : i ∈ (blockAt S.activeCoarseFamily P q).fiber)
    (hhigh : A < blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P q))
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
  refine ⟨Q, hiq, ?_, hhigh, ?_⟩
  · exact selectedParentGreedyBlockJohnPlankFamily_averageMultiplicity
      S Y hrho P q C a b hplank
  · exact selectedParentBlock_isFrostmanIn_one S Y P q

#print axioms selectedParentBlock_isFrostmanIn_one
#print axioms exists_selectedParentJohnPlankFamily_of_high_qBlock

end
end Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2
