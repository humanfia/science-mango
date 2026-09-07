import Family8Grounding.Family8FrozenAssemblyMassPopularFiberV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra

/-!
# A mass-popular frozen fibre with literal subtype density, V2

V1 omitted the namespace containing the selected-coarse subtype definitions.
This clean successor makes that dependency explicit.  It preserves the same
mass-popular fibre, density loss, positivity witness, and actual-average
product.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FrozenAssemblyMassPopularFiberDensityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Family8FrozenAssemblyMassPopularFiberV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- Restricting a final fibre shading to its literal factorization fibre
changes neither its mass nor its object. -/
theorem selectedFinalFiberShading_shadingMass
    (A : Assembly P Y r) (k : kappa) :
    (selectedCoarseShading (finalFiberShading A k)
      (P.index.fiber k)).shadingMass =
        (finalFiberShading A k).shadingMass := by
  rw [selectedCoarseShading_mass]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hifiber
  rw [finalFiberShading, fiberShading_carrier, if_neg hifiber,
    measure_empty]

/-- The existing mass-popular final fibre also retains the source active
density after paying exactly `A.loss * P.index.coarse.card`.  Positivity and
the actual-average product concern this identical `k`. -/
theorem exists_massPopular_finalFiber_density_sameProduct
    (A : Assembly P Y r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass ≠ 0) :
    ∃ k ∈ P.index.coarse,
      (sourceActiveFineShading P Y).shadingDensity /
          ((A.loss : ENNReal) * (P.index.coarse.card : ENNReal)) ≤
        (selectedCoarseShading (finalFiberShading A k)
          (P.index.fiber k)).shadingDensity ∧
      0 < volume (finalFiberShading A k).shadedUnion ∧
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) := by
  obtain ⟨k, hk, hmass, hpositive, hproduct⟩ :=
    exists_massPopular_finalFiber_sameProduct A hsource
  let source := sourceActiveFineShading P Y
  let target := selectedCoarseShading (finalFiberShading A k)
    (P.index.fiber k)
  let loss : ENNReal :=
    (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  have hfamily :
      familyVolume (selectedCoarseFamily F (P.index.fiber k)) ≤
        familyVolume (sourceActiveFineFamily P) := by
    unfold sourceActiveFineFamily
    rw [selectedCoarseFamily_volume, selectedCoarseFamily_volume]
    exact Finset.sum_le_sum_of_subset (P.index.fiber_subset_fine k)
  have hmass' : source.shadingMass ≤ loss * target.shadingMass := by
    simpa only [source, target, loss,
      selectedFinalFiberShading_shadingMass] using hmass
  have hdensity : source.shadingDensity ≤
      loss * target.shadingDensity := by
    by_cases hzero : familyVolume (sourceActiveFineFamily P) = 0
    · have hsourceMass : source.shadingMass = 0 :=
        nonpos_iff_eq_zero.mp
          (source.shadingMass_le_familyVolume.trans_eq hzero)
      simp [Shading.shadingDensity, source, hzero, hsourceMass]
    · rw [← ENNReal.mul_le_mul_iff_right hzero
        (familyVolume_ne_top (sourceActiveFineFamily P))]
      calc
        familyVolume (sourceActiveFineFamily P) *
            source.shadingDensity = source.shadingMass := by
          rw [mul_comm, shadingDensity_mul_familyVolume]
        _ ≤ loss * target.shadingMass := hmass'
        _ = loss *
            (target.shadingDensity *
              familyVolume
                (selectedCoarseFamily F (P.index.fiber k))) := by
          rw [shadingDensity_mul_familyVolume]
        _ ≤ loss *
            (target.shadingDensity *
              familyVolume (sourceActiveFineFamily P)) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hfamily)
        _ = familyVolume (sourceActiveFineFamily P) *
            (loss * target.shadingDensity) := by ac_rfl
  refine ⟨k, hk, ?_, hpositive, hproduct⟩
  simpa only [source, target, loss] using
    (ENNReal.div_le_of_le_mul' hdensity)

#print axioms selectedFinalFiberShading_shadingMass
#print axioms exists_massPopular_finalFiber_density_sameProduct

end
end Family8FrozenAssemblyMassPopularFiberDensityV2
