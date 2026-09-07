import Family8Grounding.Family8BufferedLongShadingAwareSelectedFiberDensityFloorV1
import Family8Grounding.Family8StickyShadingAwareSelectedBaseRatioPowerV3
import Mathlib.Tactic

/-!
# Same-parent base ratio and density floor on a buffered long witness

The mass-popular parent selected by the global base-envelope cancellation is
also in the literal shading-aware logarithmic partition. The uniform density
floor can therefore be attached to that exact same parent.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8BufferedLongShadingAwareSelectedBaseDensityBundleV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareSelectedBaseRatioPowerV3
open Family8StickyShadingAwareSelectedFiberDensityFloorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The buffered long source scale has a single actual shading-aware parent
carrying both the power-produced base ratio and the quantitative source
density floor. -/
theorem BufferedNormalizedLongTerminalWitness.exists_shadingAwareSelected_baseRatio_and_densityFloor_of_powerCaps
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : BufferedNormalizedLongTerminalWitness D C P S)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (htauHalf : S.tau W.m ≤ (2 : NNReal)⁻¹)
    (hactive : (longTauCover D C S W.m).activeFine.Nonempty)
    (hmass : shadingMassOn D.shading
      (longTauCover D C S W.m).activeFine ≠ 0)
    {eta p a etaF lossExp xExp absorbExp scaleExp : Real}
    (hloss :
      (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) ≤
        (delta : ENNReal) ^ (-lossExp))
    (hX :
      (activeCoarseCardScaleMass (longTauCover D C S W.m) : ENNReal) ≤
        (delta : ENNReal) ^ (-xExp))
    (hconstant : massPopularBaseFixedConstant eta p a ≤
      (delta : ENNReal) ^ (-absorbExp))
    (hq : ((delta : ENNReal) / (S.tau W.m : ENNReal)) ≤
      (delta : ENNReal) ^ scaleExp)
    (hgain : 0 ≤ eta - (2 * p + a))
    (hbudget : 2 * etaF + lossExp + xExp + absorbExp ≤
      scaleExp * (eta - (2 * p + a)))
    (hsource : (delta : ENNReal) ^ (2 * etaF) ≤
      shadingMassOn D.shading
        (longTauCover D C S W.m).activeFine) :
    let S0 := longTauCover D C S W.m
    let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m))
      (S.delta_le_tau W.m) hactive hmass
    let q : ENNReal := (delta : ENNReal) / (S.tau W.m : ENNReal)
    let base : ENNReal :=
      (3 / 64 : ENNReal) ^ (-(2 * p + a)) * q ^ (-(2 * p + a))
    let scale : ENNReal := (3 / 64 : ENNReal) ^ (-eta) * q ^ (-eta)
    let unit : ENNReal :=
      ((3 / 64 : ENNReal) ^ (2 : Nat) * q ^ (2 : Nat)) / 2
    ∃ k ∈ Ppart.coarseIndices,
      base ≤ scale *
          ((Fintype.card {i // i ∈ S0.fiber k} : ENNReal) * unit) ∧
        ((sourceA : ENNReal) * ((S.tau W.m : ENNReal) ^ 2 / 2)) /
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
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  obtain ⟨k, hkSelected, hbase⟩ :=
    exists_shadingAwareSelected_massPopular_baseRatio_of_powerCaps
      S0 D.shading (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        hD.delta_pos hD.delta_le_half htau hactive hmass
        hloss hX hconstant hq hgain hbudget hsource
  have hkPpart : k ∈ Ppart.coarseIndices := by
    simpa only [Ppart, S0, shadingAwareLogPartition_coarseIndices] using
      hkSelected
  have hfloorRaw := shadingAwareSelectedParent_density_floor
    S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      htau htauHalf hactive hmass hD.delta_le_half k hkSelected
  have hfloor :
      ((sourceA : ENNReal) * ((S.tau W.m : ENNReal) ^ 2 / 2)) /
          ((2 * stickyShadingAwareCoverLoss
              S0 D.shading (sourceA : ENNReal)) *
            (((2 * Ppart.branching : Nat) : ENNReal) *
              (8 * (delta : ENNReal) ^ 2))) ≤
        (stickyFiberSourceShading S0 D.shading k).shadingDensity := by
    simpa only [Ppart, shadingAwareLogPartition_branching] using hfloorRaw
  refine ⟨k, ?_, ?_, ?_⟩
  · simpa only [Ppart, S0] using hkPpart
  · simpa only [S0] using hbase
  · simpa only [Ppart, S0] using hfloor

#print axioms
  BufferedNormalizedLongTerminalWitness.exists_shadingAwareSelected_baseRatio_and_densityFloor_of_powerCaps

end
end Family8BufferedLongShadingAwareSelectedBaseDensityBundleV4
