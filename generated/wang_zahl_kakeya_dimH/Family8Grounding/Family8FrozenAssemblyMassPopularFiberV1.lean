import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrozenAssemblyMassPopularFiberV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly

noncomputable section

/-!
# A mass-popular actual fibre in a frozen comparable assembly

The retained final refinement decomposes exactly into its actual parent
fibres.  Selecting a maximum therefore gives one parent that retains the
source active mass up to `A.loss * activeCoarse.card`.  Positivity makes this
same fibre eligible for the existing four-times actual-average product.
-/

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

theorem refinement_shadingMass_eq_sum_finalFiberShading
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    A.refinement.shading.shadingMass =
      ∑ k ∈ P.index.coarse, (finalFiberShading A k).shadingMass := by
  rw [refinement_shadingMass_eq_sum_fiberShadingMass
    P A.refinement A.indices_subset_fine]
  apply Finset.sum_congr rfl
  intro k _hk
  exact fiberShadingMass_eq_fiberShading_mass
    P A.refinement.shading k

/-- One genuinely surviving final fibre is mass-popular and is the same
second factor in the actual-average product. -/
theorem exists_massPopular_finalFiber_sameProduct
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass ≠ 0) :
    ∃ k ∈ P.index.coarse,
      (sourceActiveFineShading P Y).shadingMass ≤
          (A.loss : ENNReal) * (P.index.coarse.card : ENNReal) *
            (finalFiberShading A k).shadingMass ∧
      0 < volume (finalFiberShading A k).shadedUnion ∧
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) := by
  classical
  obtain ⟨k₀, hk₀, _hk₀Volume, _hrefinementVolume,
      houterVolume⟩ := exists_positive_finalFiber A hsource
  have hcoarse : P.index.coarse.Nonempty := ⟨k₀, hk₀⟩
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image P.index.coarse
    (fun k => (finalFiberShading A k).shadingMass) hcoarse
  have hmass : (sourceActiveFineShading P Y).shadingMass ≤
      (A.loss : ENNReal) * (P.index.coarse.card : ENNReal) *
        (finalFiberShading A k).shadingMass := by
    calc
      (sourceActiveFineShading P Y).shadingMass ≤
          (A.loss : ENNReal) *
            (actualRefinementShading A).shadingMass :=
        sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
      _ = (A.loss : ENNReal) * A.refinement.shading.shadingMass := by
        rw [actualRefinementShading_shadingMass]
      _ = (A.loss : ENNReal) *
          (∑ k' ∈ P.index.coarse,
            (finalFiberShading A k').shadingMass) := by
        rw [refinement_shadingMass_eq_sum_finalFiberShading]
      _ ≤ (A.loss : ENNReal) *
          ((P.index.coarse.card : Nat) •
            (finalFiberShading A k).shadingMass) := by
        apply mul_le_mul' le_rfl
        exact Finset.sum_le_card_nsmul P.index.coarse
          (fun k' => (finalFiberShading A k').shadingMass)
          (finalFiberShading A k).shadingMass
          (fun k' hk' => hmax k' hk')
      _ = (A.loss : ENNReal) * (P.index.coarse.card : ENNReal) *
          (finalFiberShading A k).shadingMass := by
        simp only [nsmul_eq_mul, mul_assoc]
  have hkMass : (finalFiberShading A k).shadingMass ≠ 0 := by
    intro hkZero
    apply hsource
    have hsourceEq :
        (sourceActiveFineShading P Y).shadingMass =
          (IndexedShadingRefinement.restrictTo Y
            P.index.fine).shading.shadingMass :=
      sourceActiveFineShading_shadingMass P Y
    rw [← hsourceEq]
    apply le_antisymm
    · simpa only [hkZero, mul_zero] using hmass
    · exact bot_le
  have hkVolume : volume (finalFiberShading A k).shadedUnion ≠ 0 :=
    Family8ExactAssemblyActualAverageBridgeV1.volume_shadedUnion_ne_zero_of_shadingMass_ne_zero
      (finalFiberShading A k) hkMass
  have hproduct := refinement_averageMultiplicity_le_four_mul_actualAverages
    A k hk hkVolume (ne_of_gt houterVolume)
  refine ⟨k, hk, hmass, bot_lt_iff_ne_bot.mpr hkVolume, ?_⟩
  rw [actualRefinementShading_averageMultiplicity]
  exact hproduct

#print axioms refinement_shadingMass_eq_sum_finalFiberShading
#print axioms exists_massPopular_finalFiber_sameProduct

end
end Family8FrozenAssemblyMassPopularFiberV1
