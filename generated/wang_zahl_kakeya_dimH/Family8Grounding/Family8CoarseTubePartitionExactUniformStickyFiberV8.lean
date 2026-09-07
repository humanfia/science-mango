import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import Mathlib.Tactic

/-!
# Exact-uniform source fine levels as literal Sticky fibres

The source fine-level shading selected by an exact assembly is already
supported on one fibre of its coarse tube partition.  Restricting it to that
fibre consequently preserves its mass, shaded union, and actual average
multiplicity.  V5--V7 are failed elaboration drafts and are not imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoarseTubePartitionExactUniformStickyFiberV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberSubtypeAverageBridgeV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-- Restricting an exact assembly's actual source fine-level shading to its
own partition fibre preserves multiplicity-counted mass. -/
theorem restrictTo_sourceFineLevelShading_shadingMass_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (IndexedShadingRefinement.restrictTo
      (sourceFineLevelShading A k) (P.fiber k)).shading.shadingMass =
        (sourceFineLevelShading A k).shadingMass := by
  classical
  unfold Shading.shadingMass
  apply Finset.sum_congr rfl
  intro i _hi
  rw [IndexedShadingRefinement.restrictTo_carrier]
  by_cases hif : i ∈ P.fiber k
  · rw [if_pos hif]
  · rw [if_neg hif]
    have hempty : (sourceFineLevelShading A k).carrier i = ∅ := by
      exact fiberLevelShading_carrier_eq_empty_of_not_mem
        P.asConvexFactorization Y k A.fineLevel i hif
    rw [hempty]

/-- The same restriction preserves the actual shaded union. -/
theorem restrictTo_sourceFineLevelShading_shadedUnion_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (IndexedShadingRefinement.restrictTo
      (sourceFineLevelShading A k) (P.fiber k)).shading.shadedUnion =
        (sourceFineLevelShading A k).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [IndexedShadingRefinement.restrictTo_carrier] at hxi
    by_cases hif : i ∈ P.fiber k
    · rw [if_pos hif] at hxi
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    · rw [if_neg hif] at hxi
      exact hxi.elim
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hif : i ∈ P.fiber k := by
      by_contra hnot
      have hempty : (sourceFineLevelShading A k).carrier i = ∅ := by
        exact fiberLevelShading_carrier_eq_empty_of_not_mem
          P.asConvexFactorization Y k A.fineLevel i hnot
      rw [hempty] at hxi
      exact hxi
    exact Set.mem_iUnion.mpr ⟨i, by
      rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hif]
      exact hxi⟩

/-- Hence the source fine-level actual average is unchanged by the literal
fibre restriction. -/
theorem restrictTo_sourceFineLevelShading_averageMultiplicity_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (IndexedShadingRefinement.restrictTo
      (sourceFineLevelShading A k) (P.fiber k)).shading.averageMultiplicity =
        (sourceFineLevelShading A k).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [restrictTo_sourceFineLevelShading_shadingMass_eq P Y A k,
    restrictTo_sourceFineLevelShading_shadedUnion_eq P Y A k]

/-- The source fine-level average on the exact partition is exactly the
average consumed by the corresponding literal Sticky fibre subtype. -/
theorem stickyFiber_exactPartition_sourceFineLevel_averageMultiplicity_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (stickyFiberSourceShading (exactPartitionStickyCover P)
      (sourceFineLevelShading A k) k).averageMultiplicity =
        (sourceFineLevelShading A k).averageMultiplicity := by
  rw [stickyFiberSourceShading_averageMultiplicity_eq_restrictTo]
  change
    (IndexedShadingRefinement.restrictTo
      (sourceFineLevelShading A k) (P.fiber k)).shading.averageMultiplicity = _
  exact restrictTo_sourceFineLevelShading_averageMultiplicity_eq P Y A k

/-- The same exact identification for multiplicity-counted mass. -/
theorem stickyFiber_exactPartition_sourceFineLevel_shadingMass_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (stickyFiberSourceShading (exactPartitionStickyCover P)
      (sourceFineLevelShading A k) k).shadingMass =
        (sourceFineLevelShading A k).shadingMass := by
  rw [stickyFiberSourceShading_shadingMass_eq_restrictTo]
  change
    (IndexedShadingRefinement.restrictTo
      (sourceFineLevelShading A k) (P.fiber k)).shading.shadingMass = _
  exact restrictTo_sourceFineLevelShading_shadingMass_eq P Y A k

/-- The same exact identification for the underlying shaded union. -/
theorem stickyFiber_exactPartition_sourceFineLevel_shadedUnion_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (stickyFiberSourceShading (exactPartitionStickyCover P)
      (sourceFineLevelShading A k) k).shadedUnion =
        (sourceFineLevelShading A k).shadedUnion := by
  rw [stickyFiberSourceShading_shadedUnion_eq_restrictTo]
  change
    (IndexedShadingRefinement.restrictTo
      (sourceFineLevelShading A k) (P.fiber k)).shading.shadedUnion = _
  exact restrictTo_sourceFineLevelShading_shadedUnion_eq P Y A k

#print axioms restrictTo_sourceFineLevelShading_shadingMass_eq
#print axioms restrictTo_sourceFineLevelShading_shadedUnion_eq
#print axioms restrictTo_sourceFineLevelShading_averageMultiplicity_eq
#print axioms
  stickyFiber_exactPartition_sourceFineLevel_averageMultiplicity_eq
#print axioms stickyFiber_exactPartition_sourceFineLevel_shadingMass_eq
#print axioms stickyFiber_exactPartition_sourceFineLevel_shadedUnion_eq

end
end Family8CoarseTubePartitionExactUniformStickyFiberV8
