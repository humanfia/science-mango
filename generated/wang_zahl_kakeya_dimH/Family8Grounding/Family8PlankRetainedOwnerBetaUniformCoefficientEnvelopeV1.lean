import Family8Grounding.Family8PlankRetainedOwnerBetaUniformPowerEnvelopeV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8PlankRetainedOwnerBetaUniformCoefficientEnvelopeV1

open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerFullBallPowerAbsorptionV1
open Family8PlankRetainedOwnerFixedComparisonCountEnvelopeV1
open Family8PlankRetainedOwnerBetaCountReserveV1
open Family8PlankRetainedOwnerBetaUniformPowerEnvelopeV2

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- Direct-consumer form of the canonical retained-owner envelope.  Positive
retained mass makes the original index type nonempty, so the reserved count
power is at least one.  It can therefore be removed from the left-hand side
of the stronger reserve theorem. -/
theorem fixedComparison_retainedLogCoefficient_le_uniformPower
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hcomparison : D.comparisonConstant = 576)
    {beta absorbExponent : Real} (hbeta : beta ∈ Ioc 0 1)
    (ha : 0 < a) (habsorb : 0 < absorbExponent)
    (hsmall : a ≤ retainedOwnerBetaUniformThreshold beta absorbExponent) :
    retainedOwnerFullBallCoefficient D
        ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) ≤
      (a : ENNReal) ^ (-absorbExponent) *
        (Fintype.card iota : ENNReal) ^ (1 - beta / 2) := by
  have hcardNat := originalIndexCard_one_le_of_retainedMass D C q hmass
  have hcard : (1 : ENNReal) ≤ (Fintype.card iota : ENNReal) := by
    exact_mod_cast hcardNat
  have hreserveNonneg : 0 ≤ retainedOwnerCountReserve beta :=
    (retainedOwnerCountReserve_pos hbeta).le
  have honeReserve : (1 : ENNReal) ≤
      (Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta := by
    simpa using ENNReal.rpow_le_rpow hcard hreserveNonneg
  calc
    retainedOwnerFullBallCoefficient D
        ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) =
      retainedOwnerFullBallCoefficient D
          ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) * 1 := by
        rw [mul_one]
    _ ≤ retainedOwnerFullBallCoefficient D
          ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) *
        (Fintype.card iota : ENNReal) ^ retainedOwnerCountReserve beta := by
      gcongr
    _ ≤ (a : ENNReal) ^ (-absorbExponent) *
        (Fintype.card iota : ENNReal) ^ (1 - beta / 2) :=
      fixedComparison_retainedLog_mul_reserve_le_uniformPower
        D C q hmass hcomparison hbeta ha habsorb hsmall

#print axioms fixedComparison_retainedLogCoefficient_le_uniformPower

end
end Family8PlankRetainedOwnerBetaUniformCoefficientEnvelopeV1
