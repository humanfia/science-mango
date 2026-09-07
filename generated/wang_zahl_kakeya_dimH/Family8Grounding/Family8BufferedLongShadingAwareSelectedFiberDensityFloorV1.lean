import Family8Grounding.Family8BufferedLongShadingAwareSelectedFiberFrostmanV1
import Family8Grounding.Family8StickyShadingAwareSelectedFiberDensityFloorV1
import Mathlib.Tactic

/-!
# Shading-aware source-fibre density floor on the buffered long witness

This is the literal `delta -> tau` specialization of the generic selected
fibre density floor. The statement retains the raw buffered terminal witness
and is independent of any later choice of intermediate buffered scale.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8BufferedLongShadingAwareSelectedFiberDensityFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareSelectedFiberDensityFloorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Every parent in the literal shading-aware source partition has the
explicit source-density floor, written with that partition's actual common
branching number. -/
theorem BufferedNormalizedLongTerminalWitness.shadingAware_selectedFiber_density_floor
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : BufferedNormalizedLongTerminalWitness D C P S)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (htauHalf : S.tau W.m ≤ (2 : NNReal)⁻¹)
    (hactive : (longTauCover D C S W.m).activeFine.Nonempty)
    (hmass : shadingMassOn D.shading
      (longTauCover D C S W.m).activeFine ≠ 0) :
    let S0 := longTauCover D C S W.m
    let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m))
      (S.delta_le_tau W.m) hactive hmass
    ∀ k, k ∈ Ppart.coarseIndices ->
      ((sourceA : ENNReal) *
          (((S.tau W.m : NNReal) : ENNReal) ^ 2 / 2)) /
          ((2 * stickyShadingAwareCoverLoss
              S0 D.shading (sourceA : ENNReal)) *
            (((2 * Ppart.branching : Nat) : ENNReal) *
              (8 * (delta : ENNReal) ^ 2))) ≤
        (stickyFiberSourceShading S0 D.shading k).shadingDensity := by
  dsimp only
  let S0 := longTauCover D C S W.m
  let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (hD.delta_pos.trans_le (S.delta_le_tau W.m))
    (S.delta_le_tau W.m) hactive hmass
  intro k hk
  have hkSelected : k ∈
      Family8StickyShadingAwareCanonicalLogBucketSelectedV1.shadingAwareSelectedParents
        S0 D.shading (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass := by
    simpa only [Ppart, shadingAwareLogPartition_coarseIndices] using hk
  have hfloor := shadingAwareSelectedParent_density_floor
    S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m)) htauHalf
      hactive hmass hD.delta_le_half k hkSelected
  simpa only [S0, Ppart, shadingAwareLogPartition_branching] using hfloor

#print axioms
  BufferedNormalizedLongTerminalWitness.shadingAware_selectedFiber_density_floor

end
end Family8BufferedLongShadingAwareSelectedFiberDensityFloorV1
