import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV8
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessAdaptiveBoundV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8CanonicalBufferedGlobalRelativeScaleGainV1.Witness

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedParent_adaptiveProxyScale_le_of_bucketShortA_le
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (target : NNReal) (hshort : bucketShortA label ≤ target) :
    selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label ≤
      max (191102976 * target) (31104 * delta / rho) := by
  calc
    selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label ≤
        max (191102976 * bucketShortA label) (31104 * delta / rho) :=
      selectedParentCenteredHalfPostAdaptiveProxyScale_le_components
        hfineContained S hrho hrhoOne P k r hr label W
    _ ≤ max (191102976 * target) (31104 * delta / rho) := by
      exact max_le_max (by gcongr) le_rfl

theorem selectedParent_paperHullThin_or_adaptiveFlat
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (tau : Real) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    hullShortestSide J ≤ rho ^ (1 - tau) ∨
      selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label ≤
        max (191102976 * (286654464 * rho ^ tau))
          (31104 * delta / rho) := by
  dsimp only
  rcases selectedParent_paperHullThin_or_bucketFlat
      hfineContained S hrho hrhoOne P k r hr label W tau with hthin | hflat
  · exact Or.inl hthin
  · right
    exact selectedParent_adaptiveProxyScale_le_of_bucketShortA_le
      hfineContained S hrho hrhoOne P k r hr label W
        (286654464 * rho ^ tau) hflat

variable {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

theorem selectedParent_canonicalBuffered_paperHullThin_or_adaptiveFlat
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
        (canonicalBufferedRadius_pos D hdelta hepsilon) label})
    (tau : Real) :
    let rho := canonicalBufferedRadius D
    let J := selectedParentGreedyBlockJohnFrame G
      (canonicalBufferedRadius_pos D hdelta hepsilon) P k
    hullShortestSide J ≤ rho ^ (1 - tau) ∨
      selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label ≤
        max (191102976 * (286654464 * rho ^ tau))
          (31104 * delta ^ (epsilon ^ 2)) := by
  dsimp only
  let rho := canonicalBufferedRadius D
  let hrho := canonicalBufferedRadius_pos D hdelta hepsilon
  have hrhoOne : rho ≤ 1 :=
    canonicalBufferedRadius_le_one D hdelta hepsilon hepsilonHalf
  rcases selectedParent_paperHullThin_or_adaptiveFlat
      hfineContained G hrho hrhoOne P k r hr label W tau with hthin | hflat
  · exact Or.inl hthin
  · right
    calc
      selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label ≤
          max (191102976 * (286654464 * rho ^ tau))
            (31104 * delta / rho) := hflat
      _ ≤ max (191102976 * (286654464 * rho ^ tau))
          (31104 * delta ^ (epsilon ^ 2)) := by
        exact max_le_max le_rfl (by
          rw [mul_div_assoc]
          gcongr
          exact delta_div_canonicalBufferedRadius_le_rpow_sq
            D hdelta hepsilon)

#print axioms selectedParent_adaptiveProxyScale_le_of_bucketShortA_le
#print axioms selectedParent_paperHullThin_or_adaptiveFlat
#print axioms selectedParent_canonicalBuffered_paperHullThin_or_adaptiveFlat

end
end Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessAdaptiveBoundV1
