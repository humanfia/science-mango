import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberSubtypeAverageBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Exact subtype/full-index Sticky fibre average bridge

The contracted-John proxy uses the literal fibre subtype, while a frozen
assembly's final fibre is represented on the full fine index type with empty
carriers off that fibre.  These are the same mass, union, and average; this
module records the exact reindexing once.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem stickyFiberSourceShading_shadingMass_eq_restrictTo
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) :
    (stickyFiberSourceShading S Y k).shadingMass =
      (IndexedShadingRefinement.restrictTo Y
        (S.fiber k)).shading.shadingMass := by
  classical
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  simp only [stickyFiberSourceShading_carrier]
  symm
  exact Finset.sum_subtype _ (fun _i => Iff.rfl) _

theorem stickyFiberSourceShading_shadedUnion_eq_restrictTo
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) :
    (stickyFiberSourceShading S Y k).shadedUnion =
      (IndexedShadingRefinement.restrictTo Y
        (S.fiber k)).shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i.1, by
      simpa [IndexedShadingRefinement.restrictTo_carrier,
        i.2] using hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    by_cases hi : i ∈ S.fiber k
    · exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, by
        simpa [IndexedShadingRefinement.restrictTo_carrier,
          hi] using hxi⟩
    · simp [IndexedShadingRefinement.restrictTo_carrier, hi] at hxi

theorem stickyFiberSourceShading_averageMultiplicity_eq_restrictTo
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) :
    (stickyFiberSourceShading S Y k).averageMultiplicity =
      (IndexedShadingRefinement.restrictTo Y
        (S.fiber k)).shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [stickyFiberSourceShading_shadingMass_eq_restrictTo,
    stickyFiberSourceShading_shadedUnion_eq_restrictTo]

/-- The exact final-fibre factor of the canonical Sticky frozen assembly is
the same average as the subtype source consumed by the proxy endpoint. -/
theorem stickyFiberSourceShading_averageMultiplicity_eq_finalFiberShading
    (S : StickyScaleCover fine rho) (hscale : delta <= rho)
    (Y : Shading fine.bodyFamily) (r : Real)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass ≠
        0)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
        Y r)
    (k : Fin S.coarseCard) :
    (stickyFiberSourceShading S A.refinement.shading k).averageMultiplicity =
      (finalFiberShading A k).averageMultiplicity := by
  rw [stickyFiberSourceShading_averageMultiplicity_eq_restrictTo]
  rfl

#print axioms stickyFiberSourceShading_shadingMass_eq_restrictTo
#print axioms stickyFiberSourceShading_shadedUnion_eq_restrictTo
#print axioms stickyFiberSourceShading_averageMultiplicity_eq_restrictTo
#print axioms
  stickyFiberSourceShading_averageMultiplicity_eq_finalFiberShading

end

end Family8StickyFiberSubtypeAverageBridgeV1
