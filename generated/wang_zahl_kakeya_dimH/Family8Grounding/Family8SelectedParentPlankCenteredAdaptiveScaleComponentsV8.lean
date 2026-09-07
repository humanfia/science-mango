import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4
import Family8Grounding.Family8CanonicalBufferedGlobalRelativeScaleGainV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8CanonicalBufferedGlobalRelativeScaleGainV1.Witness

noncomputable section

/-!
# The radius component at the actual canonical buffered scale

The occupied-bucket geometry gives `radiusFloor ≤ 31104 * delta / rho`.
For the actual long-interval canonical radius, the already grounded scale
chain gives `delta / rho ≤ delta^(epsilon^2)`.  Their composition is wholly
callback-free.
-/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

/-- At the actual canonical lower buffered radius, the literal radius floor
has the long-interval power gain `epsilon^2`. -/
theorem selectedParentCenteredHalfPostRadiusFloor_canonicalBuffered_le
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (D : IdentifiedFrostmanDividingWitness
      fine C N epsilon eta scaleSequence)
    (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (G : StickyScaleCover fine (canonicalBufferedRadius D))
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks G.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G
          (canonicalBufferedRadius_pos D hdelta hepsilon) P k) r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (canonicalBufferedRadius_pos D hdelta hepsilon) label}) :
    selectedParentCenteredHalfPostRadiusFloor
        delta (canonicalBufferedRadius D) r label ≤
      31104 * delta ^ (epsilon ^ 2) := by
  let hrho := canonicalBufferedRadius_pos D hdelta hepsilon
  have hrhoOne : canonicalBufferedRadius D ≤ 1 :=
    canonicalBufferedRadius_le_one D hdelta hepsilon hepsilonHalf
  calc
    selectedParentCenteredHalfPostRadiusFloor
          delta (canonicalBufferedRadius D) r label ≤
        31104 * delta / canonicalBufferedRadius D :=
      selectedParentCenteredHalfPostRadiusFloor_le
        hfineContained G hrho hrhoOne P k r hr label W
    _ = 31104 * (delta / canonicalBufferedRadius D) := by
      rw [mul_div_assoc]
    _ ≤ 31104 * delta ^ (epsilon ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (delta_div_canonicalBufferedRadius_le_rpow_sq D hdelta hepsilon)
        bot_le

#print axioms selectedParentCenteredHalfPostRadiusFloor_canonicalBuffered_le

end
end Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV8
