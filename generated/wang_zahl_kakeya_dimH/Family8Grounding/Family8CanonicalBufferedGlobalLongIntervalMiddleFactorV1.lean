import Family8Grounding.Family8IdentifiedDividingWitnessLongIntervalGainV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalLongIntervalMiddleFactorV1

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
# The literal `T_b` estimate in the middle-factor interface

Equation (66) is kept on the actual full-shading active coarse datum.  Its
local long-interval power is converted to the single global
`delta^(10 eta_stage)` gain, and only associativity is used to expose the
remaining `b`--`X` factor.  Thus this theorem has exactly the shape consumed
by the existing three-factor composition, with no average-identification or
conclusion callback.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma propertyEta : Real}

theorem canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_middleFactor
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
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        ((canonicalBufferedRadius W : ENNReal) ^ (-2 * gamma) *
          (activeCoarseCardScaleMass
            (canonicalBufferedGlobalCover W hD.delta_pos
              P.epsilon_pos.le hepsilonHalf) : ENNReal) ^
                (1 - gamma / 2)) := by
  have htarget :=
    Family8CanonicalBufferedGlobalLongIntervalOuterAllocatedV1.Witness.canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_longIntervalTarget_allocated
      P hKTP D hD Cmulti Sseq W A hbeta hgamma hepsilonHalf hpropertyEta
        hfine hbufferedSixteenth hAone hKTEvery hscalarSmall houterSmall
        hdelta0 hlongScaleSmall hcoefficientPower hC htauSmall hAKT
  have hbetaOne : beta <= 1 := by
    have hgap := P.epsilon_gap
    have heps := P.epsilon_pos
    linarith
  have hgain :=
    Family8IdentifiedDividingWitnessLongIntervalGainV1.Witness.tau_longIntervalGain_le_globalTenEta
      Cmulti Sseq P W hbeta hbetaOne
  have htarget' :
      (Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness.canonicalBufferedGlobalFullCoarseDatum
          D Cmulti Sseq W hD.delta_pos P.epsilon_pos.le
            hepsilonHalf).shading.averageMultiplicity <=
        (Sseq.tau W.m : ENNReal) ^
            (10 * (10 * P.eta W.stage / (P.epsilon * beta))) *
          ((canonicalBufferedRadius W : ENNReal) ^ (-2 * gamma) *
            (activeCoarseCardScaleMass
              (canonicalBufferedGlobalCover W hD.delta_pos
                P.epsilon_pos.le hepsilonHalf) : ENNReal) ^
                  (1 - gamma / 2)) := by
    simpa only [longIntervalFrostmanTargetENNReal, mul_assoc] using htarget
  exact htarget'.trans (mul_le_mul' hgain le_rfl)

#print axioms
  canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_middleFactor

end Witness
end
end Family8CanonicalBufferedGlobalLongIntervalMiddleFactorV1
