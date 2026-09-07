import Family8Grounding.Family8LowerParentMassCoarseKatzTaoV1
import Family8Grounding.Family8NormalizedLongIntervalCoreBootstrapV1

/-!
# Long-core bootstrap from source Katz--Tao and aggregated parent mass

This specializes the common normalized long-core bootstrap to the reverse
mass-localization producer.  At the canonical buffered radius, a uniform
positive lower bound for the actual assigned mass of every parent produces
the coarse Katz--Tao input directly from source Katz--Tao.  The displayed
constant is `sourceA / lower`; no radius-enlargement ratio occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalCoreLowerParentMassBootstrapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8CanonicalLowerBufferedScaleV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8LowerParentMassCoarseKatzTaoV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Finite coarse Katz--Tao coefficient obtained by dividing the source
coefficient by the retained parent-mass density. -/
def aggregatedCoarseKatzTaoNNReal
    (sourceA lower : NNReal) : NNReal :=
  sourceA / lower

@[simp] theorem coe_aggregatedCoarseKatzTaoNNReal
    (sourceA lower : NNReal) (hlower : 0 < lower) :
    (aggregatedCoarseKatzTaoNNReal sourceA lower : ENNReal) =
      (sourceA : ENNReal) * (lower : ENNReal)⁻¹ := by
  unfold aggregatedCoarseKatzTaoNNReal
  rw [ENNReal.coe_div hlower.ne']
  rfl

/-- At the canonical buffered radius, a genuine lower assigned-mass density
discharges the coarse Katz--Tao input from the source estimate. -/
theorem canonicalBufferedGlobalCover_isKatzTaoAtScale_of_source_lowerParentMass
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (sourceA lower : NNReal) (hlower : 0 < lower)
    (hlowerMass : forall k,
      k ∈ (canonicalBufferedGlobalCover W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse ->
      (lower : ENNReal) * volume
          ((canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf).coarse.tubes k).carrier <=
        familyVolume
          ((canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf).fiberFamily k))
    (hKTsource : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily) :
    (canonicalBufferedGlobalCover W hD.delta_pos
      P.epsilon_pos.le hepsilonHalf).IsKatzTaoAtScale
        (aggregatedCoarseKatzTaoNNReal sourceA lower : ENNReal) := by
  rw [coe_aggregatedCoarseKatzTaoNNReal sourceA lower hlower]
  exact isKatzTaoAtScale_of_lowerParentMass
    (canonicalBufferedGlobalCover W hD.delta_pos
      P.epsilon_pos.le hepsilonHalf)
    (ENNReal.coe_ne_zero.mpr hlower.ne') ENNReal.coe_ne_top
    hlowerMass hKTsource

/-- Common-core long bootstrap with the coarse Katz--Tao premise synthesized
from source Katz--Tao and a paper-strength parent-mass floor.  The remaining
scalar premise is now exactly `1024 * (sourceA / lower)`, rather than the
identity-cover radius loss. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_core_source_lowerParentMass
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (sourceA lower : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hlower : 0 < lower)
    (hlowerMass : forall k,
      k ∈ (canonicalBufferedGlobalCover W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse ->
      (lower : ENNReal) * volume
          ((canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf).coarse.tubes k).carrier <=
        familyVolume
          ((canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf).fiberFamily k))
    (hKTsource : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily)
    (hAKT : 1024 * aggregatedCoarseKatzTaoNNReal sourceA lower <=
      S.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta)))) :
    longIntervalKatzTaoRHSENNReal
        (S.tau W.m) (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf))
        P.epsilon (10 * P.eta W.stage / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        (S.tau W.m) (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf))
        (10 * P.eta W.stage / (P.epsilon * beta)) gamma := by
  apply
    Family8NormalizedLongIntervalCoreBootstrapV1.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_coreActual
      D hD C S P W (aggregatedCoarseKatzTaoNNReal sourceA lower)
      hbeta hgamma hepsilonHalf hrhoHalf hfine hC htauSmall
  · exact canonicalBufferedGlobalCover_isKatzTaoAtScale_of_source_lowerParentMass
      D hD C S P W hepsilonHalf sourceA lower hlower hlowerMass hKTsource
  · exact hAKT

#print axioms coe_aggregatedCoarseKatzTaoNNReal
#print axioms
  canonicalBufferedGlobalCover_isKatzTaoAtScale_of_source_lowerParentMass
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_core_source_lowerParentMass

end
end Family8CanonicalCoreLowerParentMassBootstrapV1
