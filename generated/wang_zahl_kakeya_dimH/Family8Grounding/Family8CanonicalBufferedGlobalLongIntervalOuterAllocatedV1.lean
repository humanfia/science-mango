import Family8Grounding.Family8CanonicalGlobalOuterParameterAllocationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalLongIntervalOuterAllocatedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ParameterLadderV1
open Family8LongIntervalBootstrapNumericsV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ExplicitConcentrationGeneralizedReturnV1
open Family8ExplicitConcentrationCanonicalScalarBudgetsV1
open Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1
open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3

noncomputable section

/-!
# Uniformly allocated canonical long-interval outer endpoint

This is the property-level specialization of the literal `T_b` estimate.
Every auxiliary polynomial-John, fresh-selection, return-scale and
coefficient exponent is the same datum-independent quantum
`min propertyEta P.epsilon / 100`.  The only remaining assumptions are the
genuine small-scale thresholds and the three source estimates consumed by
the long-interval bootstrap.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma propertyEta : Real}

theorem canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_longIntervalTarget_allocated
    {delta0 : NNReal}
    (P : ParameterLadder epsilon0 beta gamma)
    (hKTP : KatzTaoAtParameters beta (sectionEightFixedNu P)
      propertyEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (A : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hpropertyEta : 0 < propertyEta)
    (hfine : D.family.refinement.refined.Nonempty)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    (hAone : 1 <= (A : ENNReal))
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale (A : ENNReal))
    (hscalarSmall : canonicalBufferedRadius W / 8 <=
      canonicalOuterScalarThreshold (A : ENNReal)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta))
    (houterSmall : canonicalBufferedRadius W / 8 <=
      explicitConcentrationGeneralizedReturnThreshold
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (sectionEightFixedNu P) beta)
    (hdelta0 : canonicalBufferedRadius W / 64 <= delta0)
    (hlongScaleSmall : canonicalBufferedRadius W <=
      Family8ExplicitConcentrationFreshReturnNormalizationV2.explicitConcentrationFreshReturnScaleThreshold
        (canonicalFullCoarseGeneralizedLoss (sectionEightFixedNu P) beta
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta))
        (canonicalGlobalOuterQuantum P propertyEta))
    (hcoefficientPower : 128 * (A : ENNReal) <=
      (Sseq.tau W.m : ENNReal) ^
        (-canonicalGlobalOuterQuantum P propertyEta))
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hAKT : 1024 * A <=
      Sseq.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta)))) :
    (Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness.canonicalBufferedGlobalFullCoarseDatum
        D Cmulti Sseq W hD.delta_pos P.epsilon_pos.le
          hepsilonHalf).shading.averageMultiplicity <=
      longIntervalFrostmanTargetENNReal
        (Sseq.tau W.m) (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf))
        (10 * P.eta W.stage / (P.epsilon * beta)) gamma := by
  have hbetaOne : beta <= 1 := by
    have hgap := P.epsilon_gap
    have heps := P.epsilon_pos
    linarith
  let q := canonicalGlobalOuterQuantum P propertyEta
  have hq : 0 < q := canonicalGlobalOuterQuantum_pos P hpropertyEta
  exact
    Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1.Witness.canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_longIntervalTarget
      hKTP D hD Cmulti Sseq P W A hbeta hgamma hepsilonHalf hfine
        hbufferedSixteenth hAone hKTEvery hq hq
        (sectionEightFixedNu_pos P).le hq hq hpropertyEta.le hq hq hq hq hq
        hq (canonicalGlobalOuter_density_budget P hpropertyEta)
        (canonicalGlobalOuter_coefficient_budget P hpropertyEta)
        hscalarSmall houterSmall hdelta0 hlongScaleSmall hcoefficientPower
        (canonicalGlobalOuter_longInterval_loss_budget P hbeta hbetaOne
          hpropertyEta W.stage)
        hC htauSmall hAKT

#print axioms
  canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_longIntervalTarget_allocated

end Witness
end
end Family8CanonicalBufferedGlobalLongIntervalOuterAllocatedV1
