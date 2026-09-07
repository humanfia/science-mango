import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalXLowerV2
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedTauActiveParameterLadderBaseFloorV2

open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Parameter-ladder base floor on the literal canonical tau-active cover

The canonical Frostman `X` lower bound was stated on the global `delta -> b`
cover.  The frozen outer endpoint uses the definitionally identical active
coarse set through the tau-active `tau -> b` cover.  This module transports
the bound onto that literal endpoint object; no quantitative conclusion is
accepted as a premise.  V1 only missed the namespace of the fixed four-ball
test body and is intentionally not imported.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem parameterLadder_global_rpow_coe_le_canonicalBufferedTauActiveCardScaleMass
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hbeta : 0 < beta)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody ≤
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage) :
    ((S.tau W.m ^ (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) ≤
      (activeCoarseCardScaleMass
        (canonicalBufferedTauActiveCover
          D hD C S W P.epsilon_pos.le hepsilonHalf) : ENNReal) := by
  have hglobal :=
    Family8IdentifiedDividingWitnessCanonicalXLowerV2.Witness.parameterLadder_global_rpow_le_canonicalBufferedCardScaleMass
      D hD C S P W hbeta hepsilonHalf hrhoHalf hfine hC htauSmall
  exact_mod_cast hglobal

#print axioms
  parameterLadder_global_rpow_coe_le_canonicalBufferedTauActiveCardScaleMass

end Witness
end
end Family8CanonicalBufferedTauActiveParameterLadderBaseFloorV2
