import Family8Grounding.Family8NormalizedFirstCrossingFullRefinementAssemblyV1
import Family8Grounding.Family8NormalizedCFDividingWitnessActualCoverBridgeV3

/-!
# The first actual crossing is a literal normalized Frostman scale

The stopping witness stores a strict upper bound for the computed
parent-normalized fibre concentration on its selected buffered interval
cover.  This file exposes that field as the actual at-scale Frostman
predicate and, separately, as the corresponding absolute fibre bound with
the computed parent-mass loss.  No comparison or geometry callback is added.

V1 omitted several defining namespaces and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FirstActualCrossingNormalizedFrostmanV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

namespace FirstActualNormalizedCrossingWitness

/-- The selected strict crossing is exactly an at-scale Frostman estimate on
the witness's literal buffered interval cover. -/
theorem selectedBufferedIntervalCover_isFrostmanAtScale
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    (bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered).IsFrostmanAtScale
        ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)) := by
  apply
    (isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (bufferedIntervalCover
        D hD C S epsilon hepsilon W.m W.rho W.buffered)
      (hD.delta_pos.trans_le (S.delta_le_tau W.m)) _).2
  exact W.strict_crossing.le

/-- The same strict crossing in the absolute `fiberDeltaMax` normalization;
the only extra coefficient is the literal computed parent-mass loss. -/
theorem selectedBufferedIntervalCover_fiberDeltaMax_le
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.fiberDeltaMax
        (bufferedIntervalCover
          D hD C S epsilon hepsilon W.m W.rho W.buffered) <=
      (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage) *
        FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover.actualParentFiberMassLoss
          (bufferedIntervalCover
            D hD C S epsilon hepsilon W.m W.rho W.buffered) := by
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < W.rho :=
    htau.trans_le
      (actualDatum_tau_le_of_isBuffered
        D hD S hepsilon W.m W.rho W.buffered)
  exact
    Family8NormalizedCFDividingWitnessActualCoverBridgeV3.StickyScaleCover.fiberDeltaMax_le_error_mul_actualParentLoss_of_isFrostmanAtScale
      (bufferedIntervalCover
        D hD C S epsilon hepsilon W.m W.rho W.buffered)
      htau hrho
      (selectedBufferedIntervalCover_isFrostmanAtScale
        D hD C S epsilon hepsilon eta N W)

#print axioms selectedBufferedIntervalCover_isFrostmanAtScale
#print axioms selectedBufferedIntervalCover_fiberDeltaMax_le

end FirstActualNormalizedCrossingWitness

end
end Family8FirstActualCrossingNormalizedFrostmanV2
