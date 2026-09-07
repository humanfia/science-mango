import Family8Grounding.Family8PlankRetainedOwnerFixedComparisonCountEnvelopeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8PlankRetainedOwnerBetaCountReserveV1

open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerFullBallPowerAbsorptionV1
open Family8PlankRetainedOwnerFixedComparisonCountEnvelopeV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Count-exponent allocation for `beta` in the paper range

For `0 < beta ≤ 1`, half of the positive target exponent
`1 - beta / 2` pays the retained-owner logarithmic coefficient.  The other
half remains available to the analytic estimate, and the two powers recombine
exactly into the count power in the Family 6 Frostman factor.
-/

def retainedOwnerCountReserve (beta : Real) : Real :=
  (1 - beta / 2) / 2

theorem retainedOwnerCountReserve_pos
    {beta : Real} (hbeta : beta ∈ Ioc 0 1) :
    0 < retainedOwnerCountReserve beta := by
  unfold retainedOwnerCountReserve
  linarith [hbeta.2]

theorem retainedOwnerCountReserve_add_self (beta : Real) :
    retainedOwnerCountReserve beta + retainedOwnerCountReserve beta =
      1 - beta / 2 := by
  unfold retainedOwnerCountReserve
  ring

theorem natCard_rpow_countReserve_mul_self
    (n : Nat) {beta : Real} (hn : 1 ≤ n) :
    (n : ENNReal) ^ retainedOwnerCountReserve beta *
        (n : ENNReal) ^ retainedOwnerCountReserve beta =
      (n : ENNReal) ^ (1 - beta / 2) := by
  have hn0 : (n : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (zero_lt_one.trans_le hn))
  rw [← ENNReal.rpow_add _ _ hn0 ENNReal.coe_ne_top]
  rw [retainedOwnerCountReserve_add_self]

theorem fixedComparison_retainedLogCoefficient_mul_reserve_le_countPower
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hcomparison : D.comparisonConstant = 576)
    {beta : Real} (hbeta : beta ∈ Ioc 0 1) :
    retainedOwnerFullBallCoefficient D
        ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) *
        (Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta ≤
      fixedComparisonLogPowerConstant (retainedOwnerCountReserve beta) *
        (Fintype.card iota : ENNReal) ^ (1 - beta / 2) := by
  have hn := originalIndexCard_one_le_of_retainedMass D C q hmass
  have hcoefficient := fixedComparison_retainedLogCoefficient_le_card_rpow
    D C q hmass hcomparison (retainedOwnerCountReserve_pos hbeta)
  calc
    _ ≤ (fixedComparisonLogPowerConstant (retainedOwnerCountReserve beta) *
          (Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta) *
        (Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta := by
      gcongr
    _ = fixedComparisonLogPowerConstant (retainedOwnerCountReserve beta) *
        ((Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta *
          (Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta) := by
      ring
    _ = fixedComparisonLogPowerConstant (retainedOwnerCountReserve beta) *
        (Fintype.card iota : ENNReal) ^ (1 - beta / 2) := by
      rw [natCard_rpow_countReserve_mul_self (Fintype.card iota) hn]

#print axioms retainedOwnerCountReserve_pos
#print axioms retainedOwnerCountReserve_add_self
#print axioms natCard_rpow_countReserve_mul_self
#print axioms fixedComparison_retainedLogCoefficient_mul_reserve_le_countPower

end
end Family8PlankRetainedOwnerBetaCountReserveV1
