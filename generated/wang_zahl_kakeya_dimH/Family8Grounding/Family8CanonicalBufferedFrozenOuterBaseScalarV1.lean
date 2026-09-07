import Family8Grounding.Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedFrozenOuterBaseScalarV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8CanonicalLowerBufferedScaleV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4

noncomputable section

/-!
# Canonical identified-witness frozen outer base scalar

The two scale inequalities consumed by the pure V4 envelope are automatic:
`W.long` gives `tau <= delta^epsilon`, and the literal canonical buffered
radius gives `rho <= tau^(1-epsilon)`.  No scale or base-budget callback is
retained.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBuffered_fixedConflict_baseScalar_le
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    {CKT : ENNReal} {etaF etaKT absorbEta : Real}
    (hetaF : 0 ≤ etaF)
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 ≤ CKT)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      frozenOuterThirdKatzTaoBaseSmallDeltaThreshold absorbEta)
    (hscaleGain : 0 ≤
      (1 - P.epsilon) * etaF -
        (10 * P.eta W.stage / (P.epsilon * beta)))
    (hbudget : 2 * etaKT + absorbEta ≤
      P.epsilon *
        ((1 - P.epsilon) * etaF -
          (10 * P.eta W.stage / (P.epsilon * beta)))) :
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) *
        ((128 * CKT) * volume (unitBallBody : Set Space)) ≤
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ (-etaF)) *
        (((Sseq.tau W.m ^
          (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) /
            128) := by
  have htau : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hlong := W.long
  change (Sseq.tau W.m : ENNReal) ≤
      (delta : ENNReal) ^ P.epsilon * (Sseq.theta W.m : ENNReal) at hlong
  have hlongNN : Sseq.tau W.m ≤
      delta ^ P.epsilon * Sseq.theta W.m := by
    rw [← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne' P.epsilon,
      ← ENNReal.coe_mul] at hlong
    exact ENNReal.coe_le_coe.mp hlong
  have htauDelta : Sseq.tau W.m ≤ delta ^ P.epsilon := by
    calc
      Sseq.tau W.m ≤ delta ^ P.epsilon * Sseq.theta W.m := hlongNN
      _ ≤ delta ^ P.epsilon * 1 :=
        mul_le_mul_of_nonneg_left (Sseq.theta_le_one W.m) (by positivity)
      _ = delta ^ P.epsilon := mul_one _
  have hrhoTau : canonicalBufferedRadius W ≤
      (Sseq.tau W.m) ^ (1 - P.epsilon) := by
    simpa only [canonicalBufferedRadius] using
      (canonicalLowerBufferedScale_le_tau_rpow_one_sub
        (Sseq.theta_le_one W.m) P.epsilon_pos.le)
  have hdeltaOne : delta ≤ 1 :=
    hD.delta_le_half.trans (by norm_num)
  exact fixedConflict_baseScalar_le_of_longBufferedScale
    hD.delta_pos hdeltaOne htau
      (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
      htauDelta hrhoTau hetaF hscaleGain
      hCKTfinite hCKTone hCKT habsorbEta hsmall hbudget

#print axioms canonicalBuffered_fixedConflict_baseScalar_le

end Witness
end
end Family8CanonicalBufferedFrozenOuterBaseScalarV1
