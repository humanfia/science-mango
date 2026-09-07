import Family8Grounding.Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV1

/-!
# Uniform source-tau power residual or an actual hull-thin witness

Finite logic lifts the per-bucket geometric dichotomy to the exact uniform
shape needed by the global power consumer: either one occupied bucket is
paper hull-thin, or every occupied bucket satisfies the global-cap residual.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {stoppingEpsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

theorem selectedParent_sourceTau_exists_occupied_paperHullThin_or_forall_globalPowerResidual
    (D : IdentifiedFrostmanDividingWitness
      fine Cmulti N stoppingEpsilon eta scaleSequence)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hstoppingEpsilon : 0 < stoppingEpsilon)
    (G : StickyScaleCover fine (scaleSequence.tau D.m))
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r)
    (adaptiveC : ENNReal)
    (innerEpsilon beta absorbExponent coefficientExponent etaF : Real)
    (hinnerEpsilon : 0 ≤ innerEpsilon)
    (hbetaStrict : beta < 2 / 3)
    (habsorbExponent : 0 < absorbExponent)
    (hreserve : 0 ≤
      absorbExponent + coefficientExponent + 2 + 2 * etaF)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    let paperTau := selectedParentSourceTauEq46PaperTau stoppingEpsilon
      innerEpsilon beta absorbExponent coefficientExponent etaF
    (∃ k : Fin (blocks G.activeCoarseFamily P).length,
      ∃ label : Fin 3 → Int,
        SelectedBucketOccupied G
          (hdelta.trans_le (scaleSequence.delta_le_tau D.m))
          P k r hr label ∧
        hullShortestSide
          (selectedParentGreedyBlockJohnFrame G
            (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) P k) ≤
          scaleSequence.tau D.m ^ (1 - paperTau)) ∨
      (∀ k : Fin (blocks G.activeCoarseFamily P).length,
        ∀ label : Fin 3 → Int,
          SelectedBucketOccupied G
            (hdelta.trans_le (scaleSequence.delta_le_tau D.m))
            P k r hr label →
          (delta : ENNReal) ^ (-coefficientExponent) ≤
            (delta : ENNReal) ^ 2 *
              ((delta : ENNReal) ^ (2 * etaF) *
                proposition66AInnerFactor (scaleSequence.tau D.m)
                  (bucketShortA label) (bucketShortB label)
                  (centeredAdaptiveGlobalFullFiberNatCap G
                    (hdelta.trans_le (scaleSequence.delta_le_tau D.m))
                    P r hr adaptiveC) innerEpsilon beta)) := by
  dsimp only
  let paperTau := selectedParentSourceTauEq46PaperTau stoppingEpsilon
    innerEpsilon beta absorbExponent coefficientExponent etaF
  by_cases hthin : ∃ k : Fin (blocks G.activeCoarseFamily P).length,
      ∃ label : Fin 3 → Int,
        SelectedBucketOccupied G
          (hdelta.trans_le (scaleSequence.delta_le_tau D.m))
          P k r hr label ∧
        hullShortestSide
          (selectedParentGreedyBlockJohnFrame G
            (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) P k) ≤
          scaleSequence.tau D.m ^ (1 - paperTau)
  · exact Or.inl hthin
  · right
    intro k label hoccupied
    rcases selectedParent_sourceTau_paperHullThin_or_globalPowerResidual
        D hfineContained hdelta hdeltaHalf hstoppingEpsilon G P k r hr
        label hoccupied adaptiveC innerEpsilon beta absorbExponent
        coefficientExponent etaF hinnerEpsilon hbetaStrict
        habsorbExponent hreserve hsmall with hlocalThin | hresidual
    · exfalso
      apply hthin
      exact ⟨k, label, hoccupied, by
        simpa only [paperTau] using hlocalThin⟩
    · exact hresidual

#print axioms
  selectedParent_sourceTau_exists_occupied_paperHullThin_or_forall_globalPowerResidual

end
end Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV2
