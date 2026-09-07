import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1
import Family8Grounding.Family8IdentifiedDividingWitnessActiveLogLossV3
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveBoundedAssemblyPowerLossV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1
open Family8IdentifiedDividingWitnessActiveLogLossV3.Witness
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3

noncomputable section

/-!
# Power envelope for the literal bounded frozen-assembly loss

The canonical assembly contributes its two-level logarithmic loss, while the
bounded partition contributes one exact Katz--Tao fibre cap and branching
equal to one. Existing small-delta producers bound these two genuine factors;
this module combines them on the literal `Pcoarse/A` used downstream.

V1 is a failed namespace draft and is not imported.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBufferedTauActive_boundedAssemblyLoss_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {CKT : ENNReal} {etaKT lossEta absorbEta : Real}
    (hCKTone : 1 ≤ CKT)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (hlossEta : 0 < lossEta) (habsorbEta : 0 < absorbEta)
    (hdeltaLog : delta ≤
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta)
    (hdeltaFiber : delta ≤ ordinaryFiberNatCapSmallDeltaThreshold absorbEta)
    (Pcoarse : CoarseTubePartition
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf)).coarse)
    (hbranchingLoss : Pcoarse.branchingLoss =
      katzTaoDoubledFiberNatCap (Sseq.tau W.m)
        (canonicalBufferedRadius W) CKT)
    (hbranching : Pcoarse.branching = 1)
    {r : Real}
    (Y : Shading
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf)).bodyFamily)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y r)
    (hAloss : A.loss = frozenComparableLoss
      {i // i ∈ (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf).activeFine}
      (Fin (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf)).coarseCard)) :
    (A.loss : ENNReal) *
        ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) ≤
      (delta : ENNReal) ^
        (-(lossEta + ordinaryFiberPowerEnvelope
          P.epsilon etaKT absorbEta)) := by
  let U0 := canonicalBufferedTauActiveCover D hD Cmulti Sseq W
    P.epsilon_pos.le hepsilonHalf
  have hlogRaw :
      (frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U0.activeCoarse.card) : ENNReal) ≤
          (delta : ENNReal) ^ (-lossEta) :=
    canonicalBuffered_activeFrozenLoss_le_original_rpow
      D hD Cmulti Sseq P W hepsilonHalf hlossEta hdeltaLog
  have hcoarseCard :
      (activeFineRestrictedScaleCover U0).coarseCard = U0.activeCoarse.card := by
    rfl
  have hlog : (A.loss : ENNReal) ≤
      (delta : ENNReal) ^ (-lossEta) := by
    rw [hAloss, hcoarseCard]
    exact hlogRaw
  have hfiber :
      (katzTaoDoubledFiberNatCap (Sseq.tau W.m)
          (canonicalBufferedRadius W) CKT : ENNReal) ≤
        (delta : ENNReal) ^
          (-ordinaryFiberPowerEnvelope P.epsilon etaKT absorbEta) := by
    simpa only [canonicalBufferedRadius] using
      (canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_powerEnvelope
        hD.delta_pos (Sseq.delta_le_tau W.m) (Sseq.tau_le_theta W.m)
          (Sseq.theta_le_one W.m) P.epsilon_pos.le habsorbEta
            hdeltaFiber hCKTone hCKT)
  have hbranchingCap :
      ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) ≤
        (delta : ENNReal) ^
          (-ordinaryFiberPowerEnvelope P.epsilon etaKT absorbEta) := by
    rw [hbranchingLoss, hbranching, Nat.mul_one]
    exact hfiber
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (A.loss : ENNReal) *
        ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) ≤
        (delta : ENNReal) ^ (-lossEta) *
          (delta : ENNReal) ^
            (-ordinaryFiberPowerEnvelope P.epsilon etaKT absorbEta) :=
      mul_le_mul' hlog hbranchingCap
    _ = (delta : ENNReal) ^
        ((-lossEta) +
          (-ordinaryFiberPowerEnvelope P.epsilon etaKT absorbEta)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^
        (-(lossEta + ordinaryFiberPowerEnvelope
          P.epsilon etaKT absorbEta)) := by
      congr 1
      ring

#print axioms canonicalBufferedTauActive_boundedAssemblyLoss_le_power

end Witness
end
end Family8CanonicalBufferedTauActiveBoundedAssemblyPowerLossV2
