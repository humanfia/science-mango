import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

noncomputable section

/-!
# Selecting two rich separated canonical balls

This module specializes the finite rich-pair selector to centre separation
`10 * ballRadius <= D.distance left right`.  A positive global cross-incidence
lower bound then selects two centres in `D.family`; the existing canonical
ball-pair consumer converts their centre separation into `8 * ballRadius`
cross-separation and proves both canonical non-concentration bounds.

The item types, incidence predicates, and `goodPair` predicate remain abstract.
In particular, no coarse rectangle family or PYZ Proposition 4.1 geometric
producer is asserted here.
-/

/-- The concrete centre-separation predicate used by the canonical ball-pair
consumer. -/
def canonicalTenRadiusSeparated {alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha)
    (ballRadius : Real) (left right : alpha) : Prop :=
  10 * ballRadius <= D.distance left right

/-- The global abstract cross-incidence count, restricted to centre pairs at
distance at least `10 * ballRadius` and satisfying `goodPair`. -/
noncomputable def canonicalRichSeparatedCrossIncidenceTotal
    {leftItem rightItem alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha)
    (ballRadius : Real) (goodPair : alpha -> alpha -> Prop)
    (leftItems : Finset leftItem) (rightItems : Finset rightItem)
    (leftIncident : leftItem -> alpha -> Prop)
    (rightIncident : rightItem -> alpha -> Prop) : Nat :=
  richSeparatedCrossIncidenceTotal D.family
    (canonicalTenRadiusSeparated D ballRadius) goodPair
    leftItems rightItems leftIncident rightIncident

/-- A positive global cross-incidence lower bound selects two centres in the
canonical family.  The conclusion retains the actual centre separation and
`goodPair`, the exact finite-average incidence lower bound, cross-separation of
the two radius-`ballRadius` balls, and both canonical cardinality bounds. -/
theorem exists_canonical_richSeparated_ballPair
    {leftItem rightItem alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha)
    (hsymm : forall x y, D.distance x y = D.distance y x)
    (htriangle : forall x center y,
      D.distance x y <= D.distance x center + D.distance center y)
    {ballRadius : Real}
    (hradiusLower : D.delta <= ballRadius)
    (hradiusUpper : ballRadius <= D.ceiling)
    (goodPair : alpha -> alpha -> Prop)
    (leftItems : Finset leftItem) (rightItems : Finset rightItem)
    (leftIncident : leftItem -> alpha -> Prop)
    (rightIncident : rightItem -> alpha -> Prop)
    {lowerBound : Nat} (hlowerBound : 0 < lowerBound)
    (htotal : lowerBound <=
      canonicalRichSeparatedCrossIncidenceTotal D ballRadius goodPair
        leftItems rightItems leftIncident rightIncident) :
    exists whiteCenter, whiteCenter ∈ D.family ∧
      exists blackCenter, blackCenter ∈ D.family ∧
        canonicalTenRadiusSeparated D ballRadius whiteCenter blackCenter ∧
        goodPair whiteCenter blackCenter ∧
        lowerBound <=
          (richSeparatedCenterPairs D.family
              (canonicalTenRadiusSeparated D ballRadius) goodPair).card *
            centerCrossIncidenceCount leftItems rightItems
              leftIncident rightIncident whiteCenter blackCenter ∧
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
  have hselected := exists_richSeparated_pair_of_pos_crossIncidence_lower
    D.family (canonicalTenRadiusSeparated D ballRadius) goodPair
      leftItems rightItems leftIncident rightIncident hlowerBound htotal
  rcases hselected with
    ⟨whiteCenter, hwhiteCenter, blackCenter, hblackCenter,
      hcenters, hgoodPair, hcrossIncidence⟩
  have hballData := canonicalMetricBallPair_crossSeparated_and_card_bounds
    D hsymm htriangle hradiusLower hradiusUpper
      whiteCenter blackCenter hwhiteCenter hblackCenter hcenters
  exact ⟨whiteCenter, hwhiteCenter, blackCenter, hblackCenter,
    hcenters, hgoodPair, hcrossIncidence,
    hballData.1, hballData.2.1, hballData.2.2⟩

#print axioms canonicalTenRadiusSeparated
#print axioms canonicalRichSeparatedCrossIncidenceTotal
#print axioms exists_canonical_richSeparated_ballPair

end

end FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
