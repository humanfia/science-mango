import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1

/-!
# Fixed-geometry formulation of the convex-plank Frostman hypothesis

The comparison constants are fixed before the terminal scale is chosen.
This is the quantifier order needed for a uniform small-scale analytic
statement: `eta` and `b0` may depend on the fixed geometric losses, but not
on the datum or on its plank scales.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family6AffinePlankAnalyticHypothesesFixedGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

universe u

/-- Convex-plank Frostman multiplicity with the geometric comparison losses
fixed before the uniform terminal scale. -/
structure ConvexPlankFrostmanMultiplicityHypothesisFixedGeometry
    (UniverseMarker : Type u) (beta : Real) : Prop where
  bound :
    ∀ epsilon : Real, 0 < epsilon →
      ∀ memberComparisonCap ambientComparisonCap : NNReal,
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

/-- The previous stronger formulation implies the fixed-geometry one.
This direction is only a compatibility adapter; it is not an analytic
producer. -/
theorem fixedGeometry_of_stable
    {UniverseMarker : Type u} {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis UniverseMarker beta) :
    ConvexPlankFrostmanMultiplicityHypothesisFixedGeometry
      UniverseMarker beta := by
  refine ⟨?_⟩
  intro epsilon hepsilon memberComparisonCap ambientComparisonCap
  obtain ⟨eta, b0, heta, hb0, hbound⟩ := H.bound epsilon hepsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro iota _instFintype _instDecidableEq a b D CF M
    _hmember _hambient ha hab hbb0 hFrostman hdensity hthick
  exact hbound iota a b D CF M ha hab hbb0 hFrostman hdensity hthick

/-- A convenient specialization when the datum carries the two chosen
comparison constants definitionally. -/
theorem ConvexPlankFrostmanMultiplicityHypothesisFixedGeometry.bound_selfCaps
    {UniverseMarker : Type u} {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesisFixedGeometry
      UniverseMarker beta)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (memberComparisonConstant ambientComparisonConstant : NNReal) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (iota : Type u) [Fintype iota] [DecidableEq iota]
        (a b : NNReal) (D : ShadedConvexPlankFamily iota a b)
        (CF : ENNReal) (M : NNReal),
        D.comparisonConstant = memberComparisonConstant →
        D.ambientComparisonConstant = ambientComparisonConstant →
        0 < a → a ≤ b → b ≤ b0 →
        IsFrostmanIn CF D.family D.ambient →
        (a : ENNReal) ^ eta ≤ D.shading.shadingDensity →
        FrostmanThickenedPlankControl D M →
        D.shading.averageMultiplicity ≤
          convexPlankFrostmanFactor D epsilon beta CF M := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    H.bound epsilon hepsilon memberComparisonConstant
      ambientComparisonConstant
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro iota _instFintype _instDecidableEq a b D CF M
    hmember hambient ha hab hbb0 hFrostman hdensity hthick
  exact hbound iota a b D CF M hmember.le hambient.le ha hab hbb0
    hFrostman hdensity hthick
