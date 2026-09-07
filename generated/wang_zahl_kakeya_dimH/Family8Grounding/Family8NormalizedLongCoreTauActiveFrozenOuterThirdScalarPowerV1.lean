import Family8Grounding.Family8FrozenOuterThirdKatzTaoDensityPowerEnvelopeV3
import Family8Grounding.Family8NormalizedLongCoreTauActiveBoundedAssemblyPowerLossV1
import Mathlib.Tactic

/-!
# Joint frozen-outer scalar envelope on the normalized long core

The fixed normalized-conflict density cost and the exact bounded assembly
loss occur multiplicatively in the Core-native third-factor endpoint.  This
module combines their independently proved power bounds on the same literal
partition and assembly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreTauActiveFrozenOuterThirdScalarPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenOuterThirdKatzTaoDensityPowerEnvelopeV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBoundedAssemblyPowerLossV1
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

/-- Joint power bound for the exact scalar multiplying the radius gain in
the normalized-core frozen third-factor density hypothesis. -/
theorem canonicalBufferedTauActive_frozenOuterThirdScalar_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {CKT : ENNReal} {etaKT lossEta fiberAbsorbEta conflictAbsorbEta : Real}
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 <= CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hlossEta : 0 < lossEta)
    (hfiberAbsorbEta : 0 < fiberAbsorbEta)
    (hconflictAbsorbEta : 0 < conflictAbsorbEta)
    (hdeltaLog : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta)
    (hdeltaFiber : delta <= ordinaryFiberNatCapSmallDeltaThreshold fiberAbsorbEta)
    (hdeltaConflict : delta <=
      frozenOuterThirdKatzTaoDensitySmallDeltaThreshold conflictAbsorbEta)
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
    (((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) * 128) *
        (((A.loss : ENNReal) *
            ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
          (8 * (1024 * CKT))) <=
      (delta : ENNReal) ^
        (-(lossEta + ordinaryFiberPowerEnvelope
            P.epsilon etaKT fiberAbsorbEta +
          (2 * etaKT + conflictAbsorbEta))) := by
  have hassembly :
      (A.loss : ENNReal) *
          ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) <=
        (delta : ENNReal) ^
          (-(lossEta + ordinaryFiberPowerEnvelope
            P.epsilon etaKT fiberAbsorbEta)) :=
    canonicalBufferedTauActive_boundedAssemblyLoss_le_power
      D hD C S P W hepsilonHalf hCKTone hCKT
        hlossEta hfiberAbsorbEta hdeltaLog hdeltaFiber
        Pcoarse hbranchingLoss hbranching Y A hAloss
  have hconflict :
      ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal) * 128) * (8 * (1024 * CKT))) <=
        (delta : ENNReal) ^ (-(2 * etaKT + conflictAbsorbEta)) :=
    fixedConflict_densityScalar_le_delta_negativePower
      hD.delta_pos hCKTfinite hCKTone hCKT hconflictAbsorbEta hdeltaConflict
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) * 128) *
        (((A.loss : ENNReal) *
            ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
          (8 * (1024 * CKT))) =
        ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal) * 128) * (8 * (1024 * CKT))) *
          ((A.loss : ENNReal) *
            ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) := by
      ring
    _ <= (delta : ENNReal) ^ (-(2 * etaKT + conflictAbsorbEta)) *
        (delta : ENNReal) ^
          (-(lossEta + ordinaryFiberPowerEnvelope
            P.epsilon etaKT fiberAbsorbEta)) :=
      mul_le_mul' hconflict hassembly
    _ = (delta : ENNReal) ^
        ((-(2 * etaKT + conflictAbsorbEta)) +
          (-(lossEta + ordinaryFiberPowerEnvelope
            P.epsilon etaKT fiberAbsorbEta))) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^
        (-(lossEta + ordinaryFiberPowerEnvelope
            P.epsilon etaKT fiberAbsorbEta +
          (2 * etaKT + conflictAbsorbEta))) := by
      congr 1
      ring

#print axioms canonicalBufferedTauActive_frozenOuterThirdScalar_le_power

end
end Family8NormalizedLongCoreTauActiveFrozenOuterThirdScalarPowerV1
