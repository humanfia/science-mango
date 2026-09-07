import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Mathlib.Tactic

/-!
# Parent aggregation is lossless for an injective parent map

If no two active fine indices share a parent, every active parent fibre has
cardinality at most one.  The two existing parent-aggregation mass bounds
then become inverse inequalities, so both shading mass and actual average
multiplicity are preserved exactly.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentInjectiveAggregatedAverageIdentityV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- An injective active parent map makes every literal active parent fibre
have cardinality at most one. -/
theorem activeIndexFactorization_fiber_card_le_one_of_parent_injective
    (S : StickyScaleCover fine rho)
    (hinjective : Set.InjOn S.parent (S.activeFine : Set iota))
    (k : {k // k ∈ S.activeCoarse}) :
    ((activeIndexFactorization S).fiber k).card <= 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiData :=
    (IndexFactorization.mem_fiber (activeIndexFactorization S) i k).mp hi
  have hjData :=
    (IndexFactorization.mem_fiber (activeIndexFactorization S) j k).mp hj
  apply Subtype.ext
  apply hinjective i.2 j.2
  have hiParent : S.parent i.1 = k.1 := congrArg Subtype.val hiData.2
  have hjParent : S.parent j.1 = k.1 := congrArg Subtype.val hjData.2
  exact hiParent.trans hjParent.symm

/-- Injective parent aggregation preserves the multiplicity-counted shading
mass exactly. -/
theorem parentAggregatedShading_shadingMass_eq_activeFineShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hinjective : Set.InjOn S.parent (S.activeFine : Set iota)) :
    (parentAggregatedShading S Y).shadingMass =
      (activeFineShading S Y).shadingMass := by
  apply le_antisymm
  · exact parentAggregatedShading_shadingMass_le S Y
  · simpa using
      (activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
        S Y 1
        (activeIndexFactorization_fiber_card_le_one_of_parent_injective
          S hinjective))

/-- The shaded union is always preserved by parent aggregation, so the mass
identity also gives exact average-multiplicity identity. -/
theorem parentAggregatedShading_averageMultiplicity_eq_activeFineShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hinjective : Set.InjOn S.parent (S.activeFine : Set iota)) :
    (parentAggregatedShading S Y).averageMultiplicity =
      (activeFineShading S Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [parentAggregatedShading_shadingMass_eq_activeFineShading
      S Y hinjective,
    parentAggregatedShading_shadedUnion]

#print axioms
  activeIndexFactorization_fiber_card_le_one_of_parent_injective
#print axioms parentAggregatedShading_shadingMass_eq_activeFineShading
#print axioms parentAggregatedShading_averageMultiplicity_eq_activeFineShading

end
end Family8ParentInjectiveAggregatedAverageIdentityV2
