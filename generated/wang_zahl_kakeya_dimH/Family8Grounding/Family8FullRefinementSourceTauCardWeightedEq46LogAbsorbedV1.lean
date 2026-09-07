import Family8Grounding.Family8FullRefinementSourceTauCardWeightedEq46ExactCapV1
import Family8Grounding.Family8FullRefinementSourceTauMassPopularEq46RelativeCapCancellationV3
import Family8Grounding.Family8SelectedParentCardWeightedFixedEnvelopeLogAbsorptionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauCardWeightedEq46LogAbsorbedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCardWeightedCordobaCoreV2
open Family8SelectedParentCardWeightedFixedEnvelopeLogAbsorptionV1
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8FullRefinementSourceTauCardWeightedEq46ExactCapV1.Witness
open Family8FullRefinementSourceTauMassPopularEq46RelativeCapCancellationV3

noncomputable section

/-!
# Canonical source-tau one-count Equation (46) residual

The exact source cap, actual John-container Jacobian, and fixed logarithmic
losses have all been discharged.  The only count left is the total number of
active tau-scale parents.  In particular neither `Pgreedy.length` nor the
selected plank-bucket cardinality appears in the scalar premise.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

theorem fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_residualScalar
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
      Finset.univ)
    (k : Fin
      (blocks
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
        Pgreedy).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal)
    (tubesPerPlank : Nat)
    {etaF etaKT lossEta absorbEta epsilon beta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : 0 < etaKT) (habsorbEta : 0 < absorbEta)
    (htauThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hscalar :
      (ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        ((Sseq.tau W.m : ENNReal) ^ (-(lossEta + absorbEta)) *
          ((loss : ENNReal) *
            (Fintype.card
              (ActiveParentIndex
                (tauScaleCover
                  (fullRefinementDatum D) Cmulti Sseq W)) : ENNReal) * KT)) ≤
      (((delta : ENNReal) / (Sseq.tau W.m : ENNReal)) ^ 2) *
        ((delta : ENNReal) ^ (2 * etaF) *
          proposition66AInnerFactor (Sseq.tau W.m)
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) :
    CardWeightedCrossEq46Budget
      (fullRefinementDatum D)
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      Pgreedy k r hr A label KT lossEta
      tubesPerPlank epsilon beta := by
  let E := fullRefinementDatum D
  let S := tauScaleCover E Cmulti Sseq W
  let hrho : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  let J : ENNReal := affineJacobian
    (bucketNormalizedAffineEquiv
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho Pgreedy k) r hr)
      label)
  let core : ENNReal :=
    (Sseq.tau W.m : ENNReal) ^ (-lossEta) *
      selectedParentCardWeightedCordobaCoreBudget
        E S hrho Pgreedy k r A label KT
  let inner : ENNReal := proposition66AInnerFactor (Sseq.tau W.m)
    (bucketShortA label) (bucketShortB label)
    tubesPerPlank epsilon beta
  have hscaled :
      (ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) * core ≤
        (((delta : ENNReal) / (Sseq.tau W.m : ENNReal)) ^ 2) *
          ((J * (delta : ENNReal) ^ (2 * etaF)) * inner) := by
    dsimp only [core, J, inner, E, S, hrho]
    exact relativeScaled_cardWeightedCordobaCore_le_of_residualEnvelope
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m)
      Pgreedy k r hr A label KT tubesPerPlank
      habsorbEta htauThreshold hscalar
  have hcross :
      (katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
          ((delta : ENNReal) ^ (-etaKT)) : ENNReal) * core ≤
        (J * (delta : ENNReal) ^ (2 * etaF)) * inner := by
    exact katzTaoSourceCap_mul_core_le_of_relativeSquare
      hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      (Sseq.delta_le_tau W.m) hetaKT hscaled
  apply fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_exactSourceCap
    D hD Cmulti Sseq W Pgreedy k r hr A label KT tubesPerPlank
    hFsource hKTsource
  simpa only [core, J, inner, E, S, hrho] using hcross

#print axioms
  fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_residualScalar

end Witness
end
end Family8FullRefinementSourceTauCardWeightedEq46LogAbsorbedV1
