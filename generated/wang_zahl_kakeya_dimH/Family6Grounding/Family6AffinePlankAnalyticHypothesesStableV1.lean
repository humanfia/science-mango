import Family6Grounding.Family6PlankKatzTaoFrostmanActualAdaptersV1

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family6AffinePlankAnalyticHypothesesStableV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring

noncomputable section

universe u

/-- A shaded finite family of actual convex bodies, uniformly certified as
`a x b x 1` planks and contained in one unit-scale ambient convex body. -/
structure ShadedConvexPlankFamily
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (a b : NNReal) where
  family : ConvexFamily iota
  shading : Shading family
  comparisonConstant : NNReal
  all_isPlank : forall i, IsPlank comparisonConstant a b (family i)
  ambient : ConvexBody Space
  ambientComparisonConstant : NNReal
  ambient_is_unit_scale :
    IsPlank ambientComparisonConstant 1 1 ambient
  contained_in_ambient : forall i,
    (family i : Set Space) ⊆ (ambient : Set Space)

noncomputable def containedIndices
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {a b : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (K : Set Space) : Finset iota := by
  classical
  exact Finset.univ.filter fun i ↦ (D.family i : Set Space) ⊆ K

/-- The literal closed `theta*b` thickening in the full plank-Frostman
hypothesis. -/
noncomputable def thickenedPlankIndices
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {a b : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (theta : NNReal) (i : iota) : Finset iota :=
  containedIndices D
    (Metric.cthickening ((theta * b : NNReal) : Real)
      (D.family i : Set Space))

/-- The full `M`-dependent thickened-plank control. -/
def FrostmanThickenedPlankControl
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {a b : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (M : NNReal) : Prop :=
  1 ≤ M ∧
    forall theta : NNReal, a / b ≤ theta → theta ≤ 1 →
      forall i : iota,
        ((thickenedPlankIndices D theta i).card : ENNReal) ≤
          (M : ENNReal) * (theta : ENNReal)

/-- The typed tangent/slab incidence set used by the full Katz--Tao plank
hypothesis.  Its semantics is explicit data, not an isotropic-tube proxy. -/
structure PlankSlabIncidence
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    {a b : NNReal} (D : ShadedConvexPlankFamily iota a b) where
  members : NNReal → ConvexBody Space → Finset iota
  members_contained : forall theta S,
    members theta S ⊆ containedIndices D (S : Set Space)

/-- Full `gamma`-dependent slab-incidence control. -/
def KatzTaoSlabIncidenceControl
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {a b : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (I : PlankSlabIncidence iota D)
    (slabComparisonConstant : NNReal) (eta gamma : Real) : Prop :=
  0 ≤ gamma ∧ gamma ≤ 1 ∧
    forall theta : NNReal, a / b ≤ theta → theta ≤ 1 →
      forall S : ConvexBody Space,
        IsSlab slabComparisonConstant theta S →
          ((I.members theta S).card : ENNReal) ≤
            (a : ENNReal) ^ (-eta) *
              (theta : ENNReal) ^ gamma *
                (Fintype.card iota : ENNReal)

/-- Exact full Frostman plank factor, retaining the thickening count `M`,
the aspect ratio, and the actual index count. -/
def convexPlankFrostmanFactor
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {a b : NNReal} (_D : ShadedConvexPlankFamily iota a b)
    (epsilon beta : Real) (CF : ENNReal) (M : NNReal) : ENNReal :=
  (a : ENNReal) ^ (-epsilon) *
    CF ^ (1 - beta / 2) *
    (M : ENNReal) ^ (beta / 2) *
    ((a : ENNReal) / (b : ENNReal)) *
    (b : ENNReal) ^ (-2 * beta) *
    (((b : ENNReal) ^ (2 : Nat)) *
      (Fintype.card iota : ENNReal)) ^ (1 - beta / 2)

/-- Exact full Katz--Tao plank factor, retaining `gamma` and the typed
incidence-controlled aspect-ratio power. -/
def convexPlankKatzTaoFactor
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {a b : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (epsilon beta gamma : Real) : ENNReal :=
  (a : ENNReal) ^ (-epsilon) *
    maximalConcentration D.family ^ (1 - beta) *
    ((a : ENNReal) / (b : ENNReal)) ^ (gamma * beta) *
    (Fintype.card iota : ENNReal) ^ beta

/-- Full convex-plank Frostman analytic hypothesis. -/
structure ConvexPlankFrostmanMultiplicityHypothesis
    (UniverseMarker : Type u) (beta : Real) : Prop where
  bound :
    forall epsilon : Real, 0 < epsilon →
      exists eta : Real, exists b0 : NNReal,
        0 < eta ∧ 0 < b0 ∧
        forall (iota : Type u) [Fintype iota] [DecidableEq iota]
          (a b : NNReal) (D : ShadedConvexPlankFamily iota a b)
          (CF : ENNReal) (M : NNReal),
          0 < a → a ≤ b → b ≤ b0 →
          IsFrostmanIn CF D.family D.ambient →
          (a : ENNReal) ^ eta ≤ D.shading.shadingDensity →
          FrostmanThickenedPlankControl D M →
          D.shading.averageMultiplicity ≤
            convexPlankFrostmanFactor D epsilon beta CF M

/-- Full convex-plank Katz--Tao analytic hypothesis. -/
structure ConvexPlankKatzTaoMultiplicityHypothesis
    (UniverseMarker : Type u) (beta : Real) : Prop where
  bound :
    forall epsilon : Real, 0 < epsilon →
      exists eta : Real, exists b0 : NNReal,
        0 < eta ∧ 0 < b0 ∧
        forall (iota : Type u) [Fintype iota] [DecidableEq iota]
          (a b : NNReal) (D : ShadedConvexPlankFamily iota a b)
          (gamma : Real) (I : PlankSlabIncidence iota D)
          (slabComparisonConstant : NNReal),
          0 < a → a ≤ b → b ≤ b0 →
          (a : ENNReal) ^ eta ≤ D.shading.shadingDensity →
          KatzTaoSlabIncidenceControl D I slabComparisonConstant eta gamma →
          D.shading.averageMultiplicity ≤
            convexPlankKatzTaoFactor D epsilon beta gamma

end
end Family6AffinePlankAnalyticHypothesesStableV1
