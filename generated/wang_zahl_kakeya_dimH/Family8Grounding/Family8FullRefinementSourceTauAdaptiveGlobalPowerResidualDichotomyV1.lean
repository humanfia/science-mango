import Family8Grounding.Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV2
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
import Mathlib.Tactic

/-!
# Full-refinement source-tau power-residual dichotomy

This is the exact object-specialized input for the global card-weighted
power endpoint.  Either an actual occupied source-tau bucket is paper
hull-thin, or the endpoint's complete coefficient exponent is absorbed by
the actual global adaptive inner factor for every occupied bucket.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8FullRefinementSourceTauAdaptiveGlobalPowerResidualDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
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
open Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

theorem fullRefinement_sourceTau_exists_occupied_paperHullThin_or_forall_powerResidual
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (hstoppingEpsilon : 0 < stoppingEpsilon)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
      Finset.univ)
    (r : NNReal) (hr : 0 < r) (adaptiveC : ENNReal)
    {etaF etaKT lossEta absorbEta epsilon beta : Real}
    {lossExponent coarseKTExponent innerKTExponent
      constantAbsorbExponent : Real}
    (hetaF : 0 ≤ etaF) (hepsilon : 0 ≤ epsilon)
    (hbetaStrict : beta < 2 / 3)
    (hetaKT : 0 < etaKT) (hlossEta : 0 < lossEta)
    (habsorbEta : 0 < absorbEta)
    (hlossExponent : 0 ≤ lossExponent)
    (hcoarseKTExponent : 0 ≤ coarseKTExponent)
    (hinnerKTExponent : 0 ≤ innerKTExponent)
    (hconstantAbsorbExponent : 0 < constantAbsorbExponent)
    (hscaleSmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta
        constantAbsorbExponent) :
    let coefficientExponent := etaKT + (lossEta + absorbEta) +
      lossExponent + coarseKTExponent + innerKTExponent +
        constantAbsorbExponent
    let paperTau := selectedParentSourceTauEq46PaperTau stoppingEpsilon
      epsilon beta constantAbsorbExponent coefficientExponent etaF
    (∃ k : Fin (blocks
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
          Pgreedy).length,
      ∃ label : Fin 3 → Int,
        ActualSelectedParentBucketOccupied
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy k r hr label ∧
        hullShortestSide
          (selectedParentGreedyBlockJohnFrame
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
            Pgreedy k) ≤
          Sseq.tau W.m ^ (1 - paperTau)) ∨
      (∀ k label,
        ActualSelectedParentBucketOccupied
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy k r hr label →
        (delta : ENNReal) ^ (-coefficientExponent) ≤
          (delta : ENNReal) ^ 2 *
            ((delta : ENNReal) ^ (2 * etaF) *
              proposition66AInnerFactor (Sseq.tau W.m)
                (bucketShortA label) (bucketShortB label)
                (centeredAdaptiveGlobalFullFiberNatCap
                  (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                  (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                  Pgreedy r hr adaptiveC) epsilon beta)) := by
  dsimp only
  let E := fullRefinementDatum D
  let S := tauScaleCover E Cmulti Sseq W
  let coefficientExponent : Real := etaKT + (lossEta + absorbEta) +
    lossExponent + coarseKTExponent + innerKTExponent +
      constantAbsorbExponent
  have hreserve : 0 ≤ constantAbsorbExponent +
      coefficientExponent + 2 + 2 * etaF := by
    dsimp only [coefficientExponent]
    linarith
  have hdichotomy :=
    selectedParent_sourceTau_exists_occupied_paperHullThin_or_forall_globalPowerResidual
      W (fullRefinementDatum_isAdmissible hD).contained_in_unit_ball
      hD.delta_pos hD.delta_le_half hstoppingEpsilon S Pgreedy r hr
      adaptiveC epsilon beta constantAbsorbExponent coefficientExponent etaF
      hepsilon hbetaStrict hconstantAbsorbExponent hreserve hscaleSmall
  rcases hdichotomy with hthin | hresidual
  · left
    obtain ⟨k, label, hoccupied, hgeometry⟩ := hthin
    exact ⟨k, label, by
      simpa only [ActualSelectedParentBucketOccupied,
        SelectedBucketOccupied, S, E] using hoccupied, by
      simpa only [S, E, coefficientExponent,
        selectedParentSourceTauEq46PaperTau] using hgeometry⟩
  · right
    intro k label hoccupied
    have hoccupied' : SelectedBucketOccupied S
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy k r hr label := by
      simpa only [ActualSelectedParentBucketOccupied,
        SelectedBucketOccupied, S, E] using hoccupied
    simpa only [S, E, coefficientExponent] using
      hresidual k label hoccupied'

#print axioms
  fullRefinement_sourceTau_exists_occupied_paperHullThin_or_forall_powerResidual

end
end Family8FullRefinementSourceTauAdaptiveGlobalPowerResidualDichotomyV1
