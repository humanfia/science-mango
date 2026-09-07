import Family6Grounding.Family6AffinePlankAnalyticHypothesesFixedGeometryV1

/-!
# One-shot fixed-geometry convex-plank Frostman bound

`ConvexPlankFrostmanMultiplicityHypothesisFixedGeometry` packages every
positive loss and every pair of fixed geometry caps.  A downstream
application only needs one such choice.  The proposition below is exactly
that chosen tail: it fixes the exponent, loss, member-comparison cap, and
ambient-comparison cap before the analytic parameters are selected.

This file is only an interface refactor.  It does not assert or prove the
Family 7 convex-plank estimate.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family6AffinePlankFrostmanBoundAtFixedGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6AffinePlankAnalyticHypothesesFixedGeometryV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

universe u

/-- The single-loss, single-geometry-cap tail of the fixed-geometry
convex-plank Frostman multiplicity statement. -/
structure ConvexPlankFrostmanBoundAtFixedGeometry
    (UniverseMarker : Type u) (beta epsilon : Real)
    (memberComparisonCap ambientComparisonCap : NNReal) : Prop where
  bound :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (iota : Type u) [Fintype iota] [DecidableEq iota]
        (a b : NNReal) (D : ShadedConvexPlankFamily iota a b)
        (CF : ENNReal) (M : NNReal),
        D.comparisonConstant ≤ memberComparisonCap →
        D.ambientComparisonConstant ≤ ambientComparisonCap →
        0 < a → a ≤ b → b ≤ b0 →
        IsFrostmanIn CF D.family D.ambient →
        (a : ENNReal) ^ eta ≤ D.shading.shadingDensity →
        FrostmanThickenedPlankControl D M →
        D.shading.averageMultiplicity ≤
          convexPlankFrostmanFactor D epsilon beta CF M

/-- Extract the chosen loss and geometry caps from the full fixed-geometry
hypothesis.  This is an adapter, not an analytic producer. -/
theorem boundAt_of_fixedGeometry
    {UniverseMarker : Type u} {beta epsilon : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesisFixedGeometry
      UniverseMarker beta)
    (hepsilon : 0 < epsilon)
    (memberComparisonCap ambientComparisonCap : NNReal) :
    ConvexPlankFrostmanBoundAtFixedGeometry UniverseMarker beta epsilon
      memberComparisonCap ambientComparisonCap := by
  exact ⟨H.bound epsilon hepsilon memberComparisonCap ambientComparisonCap⟩

/-- The full fixed-geometry hypothesis is precisely the family of all its
positive-loss, chosen-cap tails. -/
theorem fixedGeometry_iff_forall_boundAt
    {UniverseMarker : Type u} {beta : Real} :
    ConvexPlankFrostmanMultiplicityHypothesisFixedGeometry
        UniverseMarker beta ↔
      ∀ epsilon : Real, 0 < epsilon →
        ∀ memberComparisonCap ambientComparisonCap : NNReal,
          ConvexPlankFrostmanBoundAtFixedGeometry UniverseMarker beta epsilon
            memberComparisonCap ambientComparisonCap := by
  constructor
  · intro H epsilon hepsilon memberComparisonCap ambientComparisonCap
    exact boundAt_of_fixedGeometry H hepsilon memberComparisonCap
      ambientComparisonCap
  · intro H
    refine ⟨?_⟩
    intro epsilon hepsilon memberComparisonCap ambientComparisonCap
    exact (H epsilon hepsilon memberComparisonCap ambientComparisonCap).bound

#print axioms boundAt_of_fixedGeometry
#print axioms fixedGeometry_iff_forall_boundAt

end
end Family6AffinePlankFrostmanBoundAtFixedGeometryV1
