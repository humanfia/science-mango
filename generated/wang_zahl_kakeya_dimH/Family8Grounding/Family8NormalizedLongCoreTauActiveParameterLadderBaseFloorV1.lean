import Family8Grounding.Family8NormalizedLongIntervalCoreXLowerV1
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2

/-!
# Parameter-ladder base floor on the normalized-core tau-active cover

The normalized long-core `X` lower bound is stated on the canonical global
`delta -> b` cover.  Coherence makes the active `b` parents in the canonical
`tau -> b` cover definitionally identical, so the same bound holds on the
literal cover used by the bounded frozen assembly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreTauActiveParameterLadderBaseFloorV1

open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The genuine parameter-ladder base floor on the exact normalized-core
tau-active cover used by the later same-assembly endpoint. -/
theorem parameterLadder_global_rpow_coe_le_coreCanonicalBufferedTauActiveCardScaleMass
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hbeta : 0 < beta)
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
        P W.stage) :
    ((S.tau W.m ^ (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) <=
      (activeCoarseCardScaleMass
        (canonicalBufferedTauActiveCover
          D hD C S W P.epsilon_pos.le hepsilonHalf) : ENNReal) := by
  have hglobal :=
    Family8NormalizedLongIntervalCoreXLowerV1.parameterLadder_global_rpow_le_coreCanonicalBufferedCardScaleMass
      D hD C S P W hbeta hepsilonHalf hrhoHalf hfine hC htauSmall
  exact_mod_cast hglobal

#print axioms
  parameterLadder_global_rpow_coe_le_coreCanonicalBufferedTauActiveCardScaleMass

end
end Family8NormalizedLongCoreTauActiveParameterLadderBaseFloorV1
