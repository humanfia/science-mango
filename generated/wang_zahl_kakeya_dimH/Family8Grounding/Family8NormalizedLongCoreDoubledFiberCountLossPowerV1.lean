import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import Mathlib.Tactic

/-!
# Canonical-buffer doubled-fibre count-loss power

This projection records only the source-delta power bound for the natural
doubled-fibre cap used as the honest selected-middle count loss.  It avoids
re-elaborating any frozen assembly or selected-fibre witness.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreDoubledFiberCountLossPowerV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The literal doubled-fibre natural count loss at the canonical buffered
scale is bounded by one explicit source-delta power. -/
theorem canonicalBuffered_doubledFiberCountLoss_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    {CKT : ENNReal} {etaKT absorbEta : Real}
    (hCKTone : 1 <= CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hdeltaFiber : delta <=
      ordinaryFiberNatCapSmallDeltaThreshold absorbEta) :
    (katzTaoDoubledFiberNatCap (S.tau W.m)
      (canonicalBufferedRadius W) CKT : ENNReal) <=
      (delta : ENNReal) ^
        (-ordinaryFiberPowerEnvelope P.epsilon etaKT absorbEta) := by
  simpa only [canonicalBufferedRadius] using
    (canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_powerEnvelope
      hD.delta_pos (S.delta_le_tau W.m) (S.tau_le_theta W.m)
      (S.theta_le_one W.m) P.epsilon_pos.le habsorbEta
      hdeltaFiber hCKTone hCKT)

#print axioms canonicalBuffered_doubledFiberCountLoss_le_power

end
end Family8NormalizedLongCoreDoubledFiberCountLossPowerV1
