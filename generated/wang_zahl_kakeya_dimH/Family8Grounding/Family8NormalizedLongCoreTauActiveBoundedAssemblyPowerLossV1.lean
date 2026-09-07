import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Mathlib.Tactic

/-!
# Bounded frozen-assembly power loss on the normalized long core

The canonical assembly contributes the genuine two-level logarithmic loss,
and the literal bounded partition contributes its exact Katz--Tao fibre cap
with branching one.  This module combines the existing normalized-core log
bound and the numerical fibre-cap envelope on the same dependent objects.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreTauActiveBoundedAssemblyPowerLossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ParameterLadderV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The literal normalized-core bounded assembly loss and branching cap have
the claimed joint power envelope. -/
theorem canonicalBufferedTauActive_boundedAssemblyLoss_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {CKT : ENNReal} {etaKT lossEta absorbEta : Real}
    (hCKTone : 1 <= CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hlossEta : 0 < lossEta) (habsorbEta : 0 < absorbEta)
    (hdeltaLog : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta)
    (hdeltaFiber : delta <= ordinaryFiberNatCapSmallDeltaThreshold absorbEta)
    (Pcoarse : CoarseTubePartition
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD C S W
          P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD C S W
          P.epsilon_pos.le hepsilonHalf)).coarse)
    (hbranchingLoss : Pcoarse.branchingLoss =
      katzTaoDoubledFiberNatCap (S.tau W.m)
        (canonicalBufferedRadius W) CKT)
    (hbranching : Pcoarse.branching = 1)
    {r : Real}
    (Y : Shading
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD C S W
          P.epsilon_pos.le hepsilonHalf)).bodyFamily)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y r)
    (hAloss : A.loss = frozenComparableLoss
      {i // i ∈ (canonicalBufferedTauActiveCover D hD C S W
        P.epsilon_pos.le hepsilonHalf).activeFine}
      (Fin (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD C S W
          P.epsilon_pos.le hepsilonHalf)).coarseCard)) :
    (A.loss : ENNReal) *
        ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) <=
      (delta : ENNReal) ^
        (-(lossEta + ordinaryFiberPowerEnvelope
          P.epsilon etaKT absorbEta)) := by
  let U0 := canonicalBufferedTauActiveCover D hD C S W
    P.epsilon_pos.le hepsilonHalf
  have hlogRaw :
      (frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U0.activeCoarse.card) : ENNReal) <=
          (delta : ENNReal) ^ (-lossEta) :=
    canonicalBufferedTauActive_frozenLoss_le_power
      D hD C S P W hepsilonHalf hlossEta hdeltaLog
  have hcoarseCard :
      (activeFineRestrictedScaleCover U0).coarseCard = U0.activeCoarse.card := by
    rfl
  have hlog : (A.loss : ENNReal) <=
      (delta : ENNReal) ^ (-lossEta) := by
    rw [hAloss, hcoarseCard]
    exact hlogRaw
  have hfiber :
      (katzTaoDoubledFiberNatCap (S.tau W.m)
          (canonicalBufferedRadius W) CKT : ENNReal) <=
        (delta : ENNReal) ^
          (-ordinaryFiberPowerEnvelope P.epsilon etaKT absorbEta) := by
    simpa only [canonicalBufferedRadius] using
      (canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_powerEnvelope
        hD.delta_pos (S.delta_le_tau W.m) (S.tau_le_theta W.m)
          (S.theta_le_one W.m) P.epsilon_pos.le habsorbEta
            hdeltaFiber hCKTone hCKT)
  have hbranchingCap :
      ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) <=
        (delta : ENNReal) ^
          (-ordinaryFiberPowerEnvelope P.epsilon etaKT absorbEta) := by
    rw [hbranchingLoss, hbranching, Nat.mul_one]
    exact hfiber
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (A.loss : ENNReal) *
        ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) <=
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

end
end Family8NormalizedLongCoreTauActiveBoundedAssemblyPowerLossV1
