import Family8Grounding.Family8BufferedNormalizedLongTerminalWitnessV1
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2

/-!
# The buffered long witness's source upper bound as an actual Frostman field

The terminal witness stores the paper-normalized maximum on the literal
`delta -> tau` cover.  This file exposes its definitionally equivalent
`IsFrostmanAtScale` certificate, so downstream source selectors can consume
the bound without replacing it by a Katz--Tao cardinality cap.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8BufferedLongSourceUpperFrostmanV1

open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8ParameterLadderV1
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- `source_upper` is exactly Frostman control on the actual source-to-tau
cover selected by the buffered witness. -/
theorem BufferedNormalizedLongTerminalWitness.source_isFrostmanAtScale
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : BufferedNormalizedLongTerminalWitness D C P S) :
    StickyScaleCover.IsFrostmanAtScale
      (longTauCover D C S W.m)
      (((S.tau W.m / delta : NNReal) : ENNReal) ^
        P.eta (W.stage - 1)) := by
  exact
    (isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (longTauCover D C S W.m) hD.delta_pos _).mpr W.source_upper

#print axioms
  BufferedNormalizedLongTerminalWitness.source_isFrostmanAtScale

end
end Family8BufferedLongSourceUpperFrostmanV1
