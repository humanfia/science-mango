import Family8Grounding.Family8CanonicalBufferedTauActiveBoundedAssemblyPowerLossV2
import Family8Grounding.Family8FrozenOuterThirdKatzTaoDensityPowerEnvelopeV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveFrozenOuterThirdScalarPowerV1

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
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8CanonicalBufferedTauActiveBoundedAssemblyPowerLossV2.Witness
open Family8FrozenOuterThirdKatzTaoDensityPowerEnvelopeV3

noncomputable section

/-!
# Joint power envelope for the literal frozen outer third scalar

The fixed normalized-conflict/density scalar and the loss of the actual
bounded frozen assembly occur multiplicatively in the third-factor density
hypothesis.  This module combines their independently produced power bounds
on the same literal `Pcoarse/A` data.  The remaining radius gain and source
mass floor are deliberately not weakened here; those are the Section 6.5
outer--inner product interface.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBufferedTauActive_frozenOuterThirdScalar_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {CKT : ENNReal} {etaKT lossEta fiberAbsorbEta conflictAbsorbEta : Real}
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 ≤ CKT)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (hlossEta : 0 < lossEta)
    (hfiberAbsorbEta : 0 < fiberAbsorbEta)
    (hconflictAbsorbEta : 0 < conflictAbsorbEta)
    (hdeltaLog : delta ≤
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta)
    (hdeltaFiber : delta ≤ ordinaryFiberNatCapSmallDeltaThreshold fiberAbsorbEta)
    (hdeltaConflict : delta ≤
      frozenOuterThirdKatzTaoDensitySmallDeltaThreshold conflictAbsorbEta)
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
    (((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) * 128) *
        (((A.loss : ENNReal) *
            ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
          (8 * (1024 * CKT))) ≤
      (delta : ENNReal) ^
        (-(lossEta + ordinaryFiberPowerEnvelope
            P.epsilon etaKT fiberAbsorbEta +
          (2 * etaKT + conflictAbsorbEta))) := by
  have hassembly :
      (A.loss : ENNReal) *
          ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal) ≤
        (delta : ENNReal) ^
          (-(lossEta + ordinaryFiberPowerEnvelope
            P.epsilon etaKT fiberAbsorbEta)) :=
    canonicalBufferedTauActive_boundedAssemblyLoss_le_power
      D hD Cmulti Sseq P W hepsilonHalf hCKTone hCKT
        hlossEta hfiberAbsorbEta hdeltaLog hdeltaFiber
        Pcoarse hbranchingLoss hbranching Y A hAloss
  have hconflict :
      ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal) * 128) * (8 * (1024 * CKT))) ≤
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
    _ ≤ (delta : ENNReal) ^ (-(2 * etaKT + conflictAbsorbEta)) *
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

end Witness
end
end Family8CanonicalBufferedTauActiveFrozenOuterThirdScalarPowerV1
