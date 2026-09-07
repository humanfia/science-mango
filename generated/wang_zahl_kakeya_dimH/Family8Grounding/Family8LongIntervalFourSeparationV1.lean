import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import Mathlib.Tactic

/-!
# Extracting the geometric four-separation from a long interval

The common-fine buffered producer needs `4 * tau <= theta`.  The stopping
predicate `IsLong` supplies this exactly when the global small-scale factor
obeys `4 * delta^epsilon <= 1`.  The final theorem records that `IsLong`
alone is insufficient, even for the canonical one-step sequence at
`delta = 1/2`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8LongIntervalFourSeparationV1

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2

noncomputable section

variable {delta : NNReal} {depth : Nat}

/-- A long terminal interval is four-separated once the displayed global
small-scale threshold is available. -/
theorem four_mul_tau_le_theta_of_isLong
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (m : Fin depth) (hlong : S.IsLong epsilon m)
    (hsmall : 4 * (delta : ENNReal) ^ epsilon <= 1) :
    4 * S.tau m <= S.theta m := by
  change (S.tau m : ENNReal) <=
    (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal) at hlong
  have hcalc :
      4 * (S.tau m : ENNReal) <= (S.theta m : ENNReal) := by
    calc
      4 * (S.tau m : ENNReal) <=
          4 * ((delta : ENNReal) ^ epsilon * (S.theta m : ENNReal)) :=
        mul_le_mul' le_rfl hlong
      _ = (4 * (delta : ENNReal) ^ epsilon) *
          (S.theta m : ENNReal) := by ring
      _ <= 1 * (S.theta m : ENNReal) :=
        mul_le_mul' hsmall le_rfl
      _ = (S.theta m : ENNReal) := one_mul _
  apply ENNReal.coe_le_coe.mp
  simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat] using hcalc

/-- The canonical `1 -> 1/2` endpoint sequence. -/
def halfEndpointScaleSequence :
    FiniteScaleSequence ((2 : NNReal)⁻¹) 1 :=
  endpointScaleSequence ((2 : NNReal)⁻¹) (by norm_num)

/-- At exponent one, the unique `1 -> 1/2` interval is long. -/
theorem halfEndpointScaleSequence_isLong :
    halfEndpointScaleSequence.IsLong 1 (0 : Fin 1) := by
  unfold FiniteScaleSequence.IsLong halfEndpointScaleSequence
  simp

/-- Nevertheless that interval is not four-separated.  Thus `IsLong` by
itself cannot discharge the geometric producer's scale hypothesis. -/
theorem isLong_does_not_force_four_mul_tau_le_theta :
    ¬ (4 * halfEndpointScaleSequence.tau (0 : Fin 1) <=
      halfEndpointScaleSequence.theta (0 : Fin 1)) := by
  unfold halfEndpointScaleSequence
  simp
  norm_num [NNReal.coe_mul, NNReal.coe_inv]

#print axioms four_mul_tau_le_theta_of_isLong
#print axioms halfEndpointScaleSequence_isLong
#print axioms isLong_does_not_force_four_mul_tau_le_theta

end
end Family8LongIntervalFourSeparationV1
