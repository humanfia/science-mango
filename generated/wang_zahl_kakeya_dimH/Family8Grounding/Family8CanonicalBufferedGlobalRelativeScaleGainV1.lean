import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalRelativeScaleGainV1

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8CanonicalLowerBufferedScaleV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness

noncomputable section

/-!
# Power gain in the global fine-to-buffered scale ratio

The long-interval inequality is used before any multiplicity estimate.  At
the canonical lower buffered endpoint it gives the sharp relation
`delta / b <= delta^(epsilon^2)`.  This is the scale gain consumed by both
fixed-Katz--Tao scalar envelopes in the first outer factor.
-/

theorem tau_div_canonicalLowerBufferedScale_le_rpow_sq
    {delta tau theta : NNReal} {epsilon : Real}
    (hdelta : 0 < delta) (hdeltaTau : delta <= tau)
    (htauTheta : tau <= theta) (hepsilon : 0 <= epsilon)
    (hlong : (tau : ENNReal) <=
      (delta : ENNReal) ^ epsilon * (theta : ENNReal)) :
    tau / canonicalLowerBufferedScale tau theta epsilon <=
      delta ^ (epsilon ^ 2) := by
  have htau : 0 < tau := hdelta.trans_le hdeltaTau
  have htheta : 0 < theta := htau.trans_le htauTheta
  have hlongNN : tau <= delta ^ epsilon * theta := by
    rw [<- ENNReal.coe_le_coe]
    simpa only [ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hlong
  have hratio : tau / theta <= delta ^ epsilon := by
    apply (div_le_iff₀ htheta).2
    simpa only [mul_comm] using hlongNN
  have hratioPow : (tau / theta) ^ epsilon <=
      (delta ^ epsilon) ^ epsilon :=
    NNReal.rpow_le_rpow hratio hepsilon
  have hratioIdentity :
      tau / canonicalLowerBufferedScale tau theta epsilon =
        (tau / theta) ^ epsilon := by
    rw [canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
    have hratioPos : 0 < (theta / tau) ^ epsilon :=
      NNReal.rpow_pos (div_pos htheta htau)
    apply (div_eq_iff (mul_ne_zero htau.ne' hratioPos.ne')).2
    have hratioMul : (tau / theta) * (theta / tau) = 1 := by
      field_simp
    calc
      tau = tau * 1 := by simp
      _ = tau * (((tau / theta) * (theta / tau)) ^ epsilon) := by
        rw [hratioMul, NNReal.one_rpow]
      _ = tau * ((tau / theta) ^ epsilon *
          (theta / tau) ^ epsilon) := by rw [NNReal.mul_rpow]
      _ = (tau / theta) ^ epsilon *
          (tau * (theta / tau) ^ epsilon) := by ring
  rw [hratioIdentity]
  calc
    (tau / theta) ^ epsilon <= (delta ^ epsilon) ^ epsilon :=
      hratioPow
    _ = delta ^ (epsilon ^ 2) := by
      rw [show epsilon ^ 2 = epsilon * epsilon by ring,
        NNReal.rpow_mul]

namespace Witness

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : Submission.Kakeya.Uniformity.UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

theorem delta_div_canonicalBufferedRadius_le_rpow_sq
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    delta / canonicalBufferedRadius W <= delta ^ (epsilon ^ 2) := by
  calc
    delta / canonicalBufferedRadius W <=
        S.tau W.m / canonicalBufferedRadius W := by
      exact div_le_div_of_nonneg_right (S.delta_le_tau W.m) (by positivity)
    _ <= delta ^ (epsilon ^ 2) :=
      tau_div_canonicalLowerBufferedScale_le_rpow_sq
        hdelta (S.delta_le_tau W.m) (S.tau_le_theta W.m)
          hepsilon W.long

theorem coe_delta_div_canonicalBufferedRadius_le_rpow_sq
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    (delta : ENNReal) / (canonicalBufferedRadius W : ENNReal) <=
      (delta : ENNReal) ^ (epsilon ^ 2) := by
  rw [<- ENNReal.coe_div
      (canonicalBufferedRadius_pos W hdelta hepsilon).ne',
    <- ENNReal.coe_rpow_of_ne_zero hdelta.ne', ENNReal.coe_le_coe]
  exact delta_div_canonicalBufferedRadius_le_rpow_sq W hdelta hepsilon

end Witness

#print axioms tau_div_canonicalLowerBufferedScale_le_rpow_sq
#print axioms Witness.delta_div_canonicalBufferedRadius_le_rpow_sq
#print axioms Witness.coe_delta_div_canonicalBufferedRadius_le_rpow_sq

end
end Family8CanonicalBufferedGlobalRelativeScaleGainV1
