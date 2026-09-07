import Family8Grounding.Family8PlankRetainedOwnerBetaCountReserveV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8PlankRetainedOwnerBetaUniformPowerEnvelopeV2

open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerFullBallPowerAbsorptionV1
open Family8PlankRetainedOwnerFixedComparisonCountEnvelopeV1
open Family8PlankRetainedOwnerBetaCountReserveV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- A datum-independent small-scale threshold which absorbs the fixed comparison
constant and the logarithmic retained-owner loss after the canonical
`comparisonConstant = 576` specialization. -/
def retainedOwnerBetaUniformThreshold (beta absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (fixedComparisonLogPowerConstant (retainedOwnerCountReserve beta))
    absorbExponent

theorem retainedOwnerBetaUniformThreshold_pos (beta absorbExponent : Real) :
    0 < retainedOwnerBetaUniformThreshold beta absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem retainedOwnerBetaFixedConstant_ne_top (beta : Real) :
    fixedComparisonLogPowerConstant (retainedOwnerCountReserve beta) ≠ ∞ := by
  unfold fixedComparisonLogPowerConstant
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top <;> norm_num
  · exact ENNReal.ofReal_ne_top

theorem retainedOwnerBetaFixedConstant_le_a_negativePower
    {a : NNReal} {beta absorbExponent : Real}
    (ha : 0 < a) (habsorb : 0 < absorbExponent)
    (hsmall : a ≤ retainedOwnerBetaUniformThreshold beta absorbExponent) :
    fixedComparisonLogPowerConstant (retainedOwnerCountReserve beta) ≤
      (a : ENNReal) ^ (-absorbExponent) := by
  exact finiteConstant_le_delta_negativePower
    (retainedOwnerBetaFixedConstant_ne_top beta) habsorb ha hsmall

/-- For `0 < beta <= 1`, the complete fixed-comparison retained-owner
coefficient and one half of the available count power are bounded uniformly by
one small-scale power and the full target count exponent.  The threshold is
chosen before the plank datum. -/
theorem fixedComparison_retainedLog_mul_reserve_le_uniformPower
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hcomparison : D.comparisonConstant = 576)
    {beta absorbExponent : Real} (hbeta : beta ∈ Ioc 0 1)
    (ha : 0 < a) (habsorb : 0 < absorbExponent)
    (hsmall : a ≤ retainedOwnerBetaUniformThreshold beta absorbExponent) :
    retainedOwnerFullBallCoefficient D
        ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) *
        (Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta ≤
      (a : ENNReal) ^ (-absorbExponent) *
        (Fintype.card iota : ENNReal) ^ (1 - beta / 2) := by
  have hcount :=
    fixedComparison_retainedLogCoefficient_mul_reserve_le_countPower
      D C q hmass hcomparison hbeta
  have hconstant := retainedOwnerBetaFixedConstant_le_a_negativePower
    ha habsorb hsmall
  exact hcount.trans (by gcongr)

#print axioms retainedOwnerBetaUniformThreshold_pos
#print axioms retainedOwnerBetaFixedConstant_ne_top
#print axioms retainedOwnerBetaFixedConstant_le_a_negativePower
#print axioms fixedComparison_retainedLog_mul_reserve_le_uniformPower

end
end Family8PlankRetainedOwnerBetaUniformPowerEnvelopeV2
