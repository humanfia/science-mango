import Family8Grounding.Family8BufferedLongSourceUpperFrostmanV1
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1

/-!
# Fibrewise form of the buffered source upper bound

The normalized source maximum controls every actual source-to-tau fibre.
This successor exposes that control in the `IsFrostmanOn` form consumed by
finite selected-family and multiplicity endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8BufferedLongSourceUpperFiberFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedLongSourceUpperFrostmanV1
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8ParameterLadderV1
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Every actual source fibre of the buffered witness carries its sharp
parent-normalized Frostman certificate. -/
theorem BufferedNormalizedLongTerminalWitness.source_fiber_isFrostmanOn
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : BufferedNormalizedLongTerminalWitness D C P S)
    (k : Fin (longTauCover D C S W.m).coarseCard)
    (hk : k ∈ (longTauCover D C S W.m).activeCoarse) :
    IsFrostmanOn
      (((S.tau W.m / delta : NNReal) : ENNReal) ^
        P.eta (W.stage - 1))
      D.family.bodyFamily ((longTauCover D C S W.m).fiber k)
      ((longTauCover D C S W.m).coarse.tubes k).body := by
  let S0 := longTauCover D C S W.m
  have hAt := Family8BufferedLongSourceUpperFrostmanV1.BufferedNormalizedLongTerminalWitness.source_isFrostmanAtScale D hD C S P W
  have hIn : IsFrostmanIn
      (((S.tau W.m / delta : NNReal) : ENNReal) ^
        P.eta (W.stage - 1))
      (S0.fiberFamily k) (S0.coarse.tubes k).body := by
    apply isFrostmanIn_iff_concentration_le.mpr
    exact ⟨S0.fiber_carrier_subset_parent k, hAt k hk⟩
  exact
    (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      D.family.bodyFamily (S0.fiber k) (S0.coarse.tubes k).body).mpr hIn

#print axioms
  BufferedNormalizedLongTerminalWitness.source_fiber_isFrostmanOn

end
end Family8BufferedLongSourceUpperFiberFrostmanV1
