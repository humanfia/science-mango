import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1
import Family8Grounding.Family8UniformTubeCardRetentionFrostmanV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Mathlib.Tactic

/-!
# Exact-card Frostman restriction for an arbitrary weighted critical ball

An actual-mass maximizer need not retain a fixed fraction of the source
cardinality.  The literal critical ball is nevertheless nonempty, so the
exact quotient `|family| / |criticalBall|` cancels without loss.  Keeping this
quotient explicit is the honest interface to the middle-count factor.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8WeightedCanonicalCriticalBallExactCardFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8UniformTubeCardRetentionFrostmanV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1

noncomputable section

universe u

/-- The literal source-to-critical-ball cardinality quotient. -/
def weightedCanonicalCriticalBallCardLoss
    {iota : Type u} [DecidableEq iota]
    (W : WeightedCanonicalNormBallData iota) : ENNReal :=
  (W.family.card : ENNReal) / (W.criticalBall.card : ENNReal)

/-- Nonemptiness of the canonical critical ball makes the exact quotient
cancel against its denominator. -/
theorem family_card_eq_cardLoss_mul_criticalBall_card
    {iota : Type u} [DecidableEq iota]
    (W : WeightedCanonicalNormBallData iota) :
    (W.family.card : ENNReal) =
      weightedCanonicalCriticalBallCardLoss W *
        (W.criticalBall.card : ENNReal) := by
  have hcardPos : 0 < W.criticalBall.card := W.criticalBall_nonempty.card_pos
  have hcard0 : (W.criticalBall.card : ENNReal) ≠ 0 := by
    exact_mod_cast hcardPos.ne'
  have hcardTop : (W.criticalBall.card : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  unfold weightedCanonicalCriticalBallCardLoss
  exact (ENNReal.div_mul_cancel hcard0 hcardTop).symm

theorem family_card_le_cardLoss_mul_criticalBall_card
    {iota : Type u} [DecidableEq iota]
    (W : WeightedCanonicalNormBallData iota) :
    (W.family.card : ENNReal) ≤
      weightedCanonicalCriticalBallCardLoss W *
        (W.criticalBall.card : ENNReal) := by
  exact (family_card_eq_cardLoss_mul_criticalBall_card W).le

/-- Restrict an explicit source Frostman certificate to the literal
weighted critical ball with precisely its source/ball cardinal quotient. -/
theorem weightedCanonicalCriticalBall_isFrostmanIn_exactCardLoss
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (W : WeightedCanonicalNormBallData iota)
    (K : ConvexBody Space) {C : ENNReal}
    (hF : IsFrostmanOn C fine.bodyFamily W.family K)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsFrostmanIn
      (C * (16 * weightedCanonicalCriticalBallCardLoss W))
      (activeSubtypeFamily fine.bodyFamily W.criticalBall) K := by
  exact isFrostmanIn_activeSubtype_of_card_retention
    fine W.family W.criticalBall K W.criticalBall_subset_family hF
      hdeltaHalf (family_card_le_cardLoss_mul_criticalBall_card W)

#print axioms weightedCanonicalCriticalBallCardLoss
#print axioms family_card_eq_cardLoss_mul_criticalBall_card
#print axioms family_card_le_cardLoss_mul_criticalBall_card
#print axioms weightedCanonicalCriticalBall_isFrostmanIn_exactCardLoss

end
end Family8WeightedCanonicalCriticalBallExactCardFrostmanV1
