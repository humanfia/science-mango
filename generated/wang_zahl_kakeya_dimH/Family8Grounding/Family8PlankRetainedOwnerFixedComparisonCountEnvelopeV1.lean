import Family8Grounding.Family8PlankRetainedOwnerLogCardPowerEnvelopeV1
import Family8Grounding.Family8PlankRetainedOwnerFullBallPowerAbsorptionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8PlankRetainedOwnerFixedComparisonCountEnvelopeV1

open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerLogCardPowerEnvelopeV1
open Family8PlankRetainedOwnerFullBallPowerAbsorptionV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Uniform count envelope at the canonical plank comparison constant

The max-owner common-scale construction uses the literal comparison constant
`576`.  At that value the full-ball coefficient and the logarithmic retained
owner loss are bounded by a fixed `kappa`-dependent constant times
`(card iota)^kappa`.  Positive retained mass supplies the required nonempty
source-card condition on the same selected object.
-/

def fixedComparisonLogPowerConstant (kappa : Real) : ENNReal :=
  54000 * (576 : ENNReal) ^ 3 *
    ENNReal.ofReal (retainedOwnerLogPowerConstant kappa)

theorem originalIndexCard_one_le_of_retainedMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    1 ≤ Fintype.card iota := by
  have hset := retainedOwnerSourceIndices_nonempty_of_mass_ne_zero
    D C q hmass
  exact Fintype.card_pos_iff.mpr ⟨hset.choose⟩

theorem fixedComparison_retainedLogCoefficient_le_card_rpow
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hcomparison : D.comparisonConstant = 576)
    {kappa : Real} (hkappa : 0 < kappa) :
    retainedOwnerFullBallCoefficient D
        ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) ≤
      fixedComparisonLogPowerConstant kappa *
        (Fintype.card iota : ENNReal) ^ kappa := by
  have hn := originalIndexCard_one_le_of_retainedMass D C q hmass
  have hlog := natLog_add_one_ennreal_le_card_rpow
    (Fintype.card iota) hn hkappa
  rw [retainedOwnerFullBallCoefficient, hcomparison]
  calc
    54000 * (576 : ENNReal) ^ 3 *
        ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) ≤
      54000 * (576 : ENNReal) ^ 3 *
        (ENNReal.ofReal (retainedOwnerLogPowerConstant kappa) *
          (Fintype.card iota : ENNReal) ^ kappa) := by gcongr
    _ = fixedComparisonLogPowerConstant kappa *
        (Fintype.card iota : ENNReal) ^ kappa := by
      unfold fixedComparisonLogPowerConstant
      ring

#print axioms fixedComparisonLogPowerConstant
#print axioms originalIndexCard_one_le_of_retainedMass
#print axioms fixedComparison_retainedLogCoefficient_le_card_rpow

end
end Family8PlankRetainedOwnerFixedComparisonCountEnvelopeV1
