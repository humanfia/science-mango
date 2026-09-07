import Family8Grounding.Family8MassPopularSelectedAdaptiveSourceReserveV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessPowerV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleThinGeometryV1
import Mathlib.Tactic

/-!
# Canonical-buffered hull flatness feeds the actual source reserve

For one actual member of one selected side-shape bucket, the paper hull
flatness dichotomy now has a source-cap terminal.  If the hull is not thin,
its adaptive-power certificate either detects that the label-dependent
threshold is already below `delta`, or forces the same actual bucket into the
small-packing regime and retains `C * (b / a)^2` in its full-fibre cap.

The member, label, adaptive scale, and local cap are definitionally the same
throughout.  No target-valued callback or all-bucket hypothesis is used.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentCanonicalBufferedHullThinOrSourceReserveV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8MassPopularSelectedAdaptiveSourceReserveV1
open Family8SelectedParentAdaptiveActualCapSourceAspectLowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessPowerV1
open Family8SelectedParentPlankCenteredAdaptiveScaleThinGeometryV1
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

theorem selectedParent_canonicalBuffered_paperHullThin_or_thresholdSmall_or_sourceReserve
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (D : IdentifiedFrostmanDividingWitness
      fine Cmulti N epsilon eta scaleSequence)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
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
    (Csource : ENNReal) (hCfinite : Csource ≠ ∞)
    (tau scaleExponent : Real) (htau : 0 ≤ tau)
    (hscaleExponent : 0 < scaleExponent)
    (hgap : 0 <
      min ((epsilon * (1 - epsilon)) * tau) (epsilon ^ 2) *
        scaleExponent - 1)
    (hdeltaSmall : delta ≤ finiteConstantSmallDeltaThreshold
      ((((max (191102976 * 286654464) 31104 : NNReal) : ENNReal) ^
        scaleExponent))
      (min ((epsilon * (1 - epsilon)) * tau) (epsilon ^ 2) *
        scaleExponent - 1)) :
    let rho := canonicalBufferedRadius D
    let J := selectedParentGreedyBlockJohnFrame G
      (canonicalBufferedRadius_pos D hdelta hepsilon) P k
    hullShortestSide J ≤ rho ^ (1 - tau) ∨
      (adaptiveThinGeometryThreshold label) ^ scaleExponent < delta ∨
      SelectedBucketActualSourceAspectReserve G
        (canonicalBufferedRadius_pos D hdelta hepsilon)
        P k r hr label Csource := by
  dsimp only
  let rho := canonicalBufferedRadius D
  let hrho : 0 < rho := canonicalBufferedRadius_pos D hdelta hepsilon
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame G hrho P k) r hr
  let B := (blockAt G.activeCoarseFamily P k).fiber
  have hWmem : (W.1 : {p // p ∈ B}) ∈
      selectedParentPlankBucketIndices e G B hrho label := by
    simpa only [rho, hrho, e, B] using W.2
  have hWshape : sideShapeLabel
      (selectedParentLongRelabeledSide e G B hrho W.1) = label := by
    change (W.1 : {p // p ∈ B}) ∈ sideShapeBucket Finset.univ
      (fun p => selectedParentLongRelabeledSide e G B hrho p) label at hWmem
    exact (mem_sideShapeBucket_iff _ _ _ _).mp hWmem |>.2
  have hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset {p // p ∈ B})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide e G B hrho p)) :=
    mem_occupiedWeightBuckets_iff.mpr ⟨W.1, Finset.mem_univ _, hWshape⟩
  rcases selectedParent_canonicalBuffered_paperHullThin_or_adaptivePower
      hfineContained D hdelta hepsilon hepsilonHalf G P k r hr label W
        tau scaleExponent htau hscaleExponent.le hgap hdeltaSmall with
    hthin | hpower
  · exact Or.inl hthin
  · right
    by_cases hdeltaThreshold :
        delta ≤ (adaptiveThinGeometryThreshold label) ^ scaleExponent
    · right
      have hsThreshold :
          selectedParentCenteredHalfPostAdaptiveProxyScale
              delta rho r label ≤ adaptiveThinGeometryThreshold label :=
        scale_le_of_power_le hscaleExponent hpower hdeltaThreshold
          (adaptiveThinGeometryThreshold_pos label)
      have hsmall :=
        (small_and_thin_of_le_adaptiveThinGeometryThreshold
          label hsThreshold).1
      exact
        exists_sourceKatzTaoConstant_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap
          G hrho P k r hr label (by
            simpa only [rho, e, B] using hoccupied)
          hdelta hdeltaHalf hsmall Csource hCfinite
    · left
      exact lt_of_not_ge hdeltaThreshold

#print axioms
  selectedParent_canonicalBuffered_paperHullThin_or_thresholdSmall_or_sourceReserve

end
end Family8SelectedParentCanonicalBufferedHullThinOrSourceReserveV1
