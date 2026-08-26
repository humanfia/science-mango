import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1

open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1

noncomputable section

/-!
# A separated pair of canonical non-concentrated balls

This is the direct consumer shared by the rich-pair selection layer and the
unreduced PYZ Proposition 4.1 application.  Once two centres at distance
`10r` have been produced, their radius-`r` subfamilies are cross-separated at
scale `8r`, and canonical maximality bounds both cardinalities.

The theorem does not assert that such a pair exists and does not identify the
balls with the paper's later coarse families.
-/

/-- A centre pair at distance `10r` simultaneously gives the required cross
separation and the two canonical non-concentration bounds. -/
theorem canonicalMetricBallPair_crossSeparated_and_card_bounds
    {alpha : Type*} (D : CanonicalNormNonconcentrationData alpha)
    (hsymm : forall x y, D.distance x y = D.distance y x)
    (htriangle : forall x center y,
      D.distance x y <= D.distance x center + D.distance center y)
    {ballRadius : Real}
    (hradiusLower : D.delta <= ballRadius)
    (hradiusUpper : ballRadius <= D.ceiling)
    (whiteCenter blackCenter : alpha)
    (hwhiteCenter : whiteCenter ∈ D.family)
    (hblackCenter : blackCenter ∈ D.family)
    (hcenters : 10 * ballRadius <=
      D.distance whiteCenter blackCenter) :
    FiniteFamiliesCrossSeparated D.distance (8 * ballRadius)
        (finiteFamilyMetricBall D.family D.distance ballRadius whiteCenter)
        (finiteFamilyMetricBall D.family D.distance ballRadius blackCenter) ∧
      ((finiteFamilyMetricBall D.family D.distance ballRadius
          whiteCenter).card : Real) <=
        (ballRadius / D.criticalScale) ^ D.exponent *
          ((D.criticalBall.card : Nat) : Real) ∧
      ((finiteFamilyMetricBall D.family D.distance ballRadius
          blackCenter).card : Real) <=
        (ballRadius / D.criticalScale) ^ D.exponent *
          ((D.criticalBall.card : Nat) : Real) := by
  constructor
  · apply finiteFamilyMetricBalls_crossSeparated D.family D.distance
      hsymm htriangle
    nlinarith [hcenters]
  constructor
  · simpa only [finiteBallCount, finiteFamilyMetricBall] using
      (D.card_le_ratio_rpow hradiusLower hradiusUpper whiteCenter hwhiteCenter)
  · simpa only [finiteBallCount, finiteFamilyMetricBall] using
      (D.card_le_ratio_rpow hradiusLower hradiusUpper blackCenter hblackCenter)

#print axioms canonicalMetricBallPair_crossSeparated_and_card_bounds

end

end FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
