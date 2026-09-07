import Family8Grounding.Family8BufferedLongSourceUpperFiberFrostmanV1
import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Mathlib.Tactic

/-!
# Sharp source Frostman control on the shading-aware selected fibres

The shading-aware logarithmic selector retains whole source fibres.  Hence
the buffered witness's sharp parent-normalized bound transports to every
fibre of its literal selected partition without a Katz--Tao replacement.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8BufferedLongShadingAwareSelectedFiberFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedLongSourceUpperFiberFrostmanV1
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Each selected partition fibre is literally one source fibre and inherits
the buffered witness's sharp source constant. -/
theorem BufferedNormalizedLongTerminalWitness.shadingAware_selectedFiber_isFrostmanOn
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : BufferedNormalizedLongTerminalWitness D C P S)
    (sourceA : ENNReal) (hsourceA0 : sourceA ≠ 0)
    (hsourceAtop : sourceA ≠ ∞)
    (hactive : (longTauCover D C S W.m).activeFine.Nonempty)
    (hmass : shadingMassOn D.shading
      (longTauCover D C S W.m).activeFine ≠ 0) :
    let S0 := longTauCover D C S W.m
    let Ppart := shadingAwareLogPartition S0 D.shading sourceA
      hsourceA0 hsourceAtop
      (hD.delta_pos.trans_le (S.delta_le_tau W.m))
      (S.delta_le_tau W.m) hactive hmass
    ∀ k, k ∈ Ppart.coarseIndices ->
      IsFrostmanOn
        (((S.tau W.m / delta : NNReal) : ENNReal) ^
          P.eta (W.stage - 1))
        D.family.bodyFamily (Ppart.fiber k) (S0.coarse.tubes k).body := by
  dsimp only
  let S0 := longTauCover D C S W.m
  let Ppart := shadingAwareLogPartition S0 D.shading sourceA
    hsourceA0 hsourceAtop
    (hD.delta_pos.trans_le (S.delta_le_tau W.m))
    (S.delta_le_tau W.m) hactive hmass
  intro k hk
  have hkSelected : k ∈ shadingAwareSelectedParents S0 D.shading sourceA
      hsourceA0 hsourceAtop
      (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass := by
    simpa only [Ppart, shadingAwareLogPartition_coarseIndices] using hk
  have hkSource : k ∈ S0.activeCoarse :=
    shadingAwareSelectedParents_subset_activeCoarse S0 D.shading sourceA
      hsourceA0 hsourceAtop
      (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass hkSelected
  have hsource :=
    Family8BufferedLongSourceUpperFiberFrostmanV1.BufferedNormalizedLongTerminalWitness.source_fiber_isFrostmanOn
      D hD C S P W k hkSource
  have hrawFiberEq :
      (rawIndexFactorization S0.activeFine S0.parent).fiber k =
        S0.fiber k := by
    ext i
    simp only [IndexFactorization.mem_fiber, rawIndexFactorization,
      StickyScaleCover.mem_fiber]
  have hselectedFiberEq : Ppart.fiber k = S0.fiber k := by
    change
      (selectedIndexFactorization S0.activeFine S0.parent
        (shadingAwareSelectedParents S0 D.shading sourceA
          hsourceA0 hsourceAtop
          (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass)).fiber k =
        S0.fiber k
    rw [selected_fiber_eq_raw_fiber S0.activeFine S0.parent
      (shadingAwareSelectedParents S0 D.shading sourceA
        hsourceA0 hsourceAtop
        (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass)
      hkSelected]
    exact hrawFiberEq
  simpa only [Ppart, S0, hselectedFiberEq] using hsource

#print axioms
  BufferedNormalizedLongTerminalWitness.shadingAware_selectedFiber_isFrostmanOn

end
end Family8BufferedLongShadingAwareSelectedFiberFrostmanV1
