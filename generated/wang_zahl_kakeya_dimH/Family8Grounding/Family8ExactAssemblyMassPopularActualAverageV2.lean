import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

/-!
# A quantitatively mass-popular fibre in an exact assembly, V2

The ordinary actual-average bridge selects an arbitrary surviving coarse
fibre.  For the middle factorization step one needs the same fibre to retain
a quantitative portion of the source active mass.  This module obtains that
fibre honestly from the finite coarse partition.

The final refinement is contained, index by index, in the source shading at
the assembly's common fine multiplicity level.  Hence its mass is bounded by
the sum of those source fine-level masses.  The retained-mass inequality and
one finite maximum then select a coarse fibre with the explicit loss
`loss * coarse.card`.  Positivity of that selected mass also makes its actual
average multiplicity equal to the assembly's `fineLevel`, so the usual
outer/fine actual-average product uses this very same fibre.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ExactAssemblyMassPopularActualAverageV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : Nat}

/-- The final refinement mass is bounded by the sum of the honest source
fine-level masses over the active coarse partition. -/
theorem refinement_shadingMass_le_sum_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    A.refinement.shading.shadingMass ≤
      ∑ k ∈ P.index.coarse, (sourceFineLevelShading A k).shadingMass := by
  rw [refinement_shadingMass_eq_sum_fiberShadingMass
    P A.refinement A.indices_subset_fine]
  apply Finset.sum_le_sum
  intro k hk
  unfold fiberShadingMass
  rw [sourceFineLevelShading, fiberLevelShading_mass_eq_sum_fiber]
  apply Finset.sum_le_sum
  intro i hi
  apply measure_mono
  have hp : P.index.parent i = k := (P.index.mem_fiber i k).1 hi |>.2
  simpa only [sourceFineLevelShading, hp] using
    refinement_carrier_subset_sourceFineLevelShading A i

/-- A nonzero active source has at least one active coarse parent.  This is
derived from the retained refinement rather than assumed as a separate
nonemptiness input. -/
theorem coarse_nonempty_of_source_shadingMass_ne_zero
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    P.index.coarse.Nonempty := by
  by_contra hcoarse
  rw [Finset.not_nonempty_iff_eq_empty] at hcoarse
  apply hsource
  apply le_antisymm
  · calc
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
          (loss : ENNReal) * A.refinement.shading.shadingMass := by
        simpa only [WithinFactor, nsmul_eq_mul] using A.retained
      _ ≤ (loss : ENNReal) *
          (∑ k ∈ P.index.coarse,
            (sourceFineLevelShading A k).shadingMass) :=
        mul_le_mul' le_rfl
          (refinement_shadingMass_le_sum_sourceFineLevelShading A)
      _ = 0 := by simp only [hcoarse, Finset.sum_empty, mul_zero]
  · exact bot_le

/-- Finite coarse averaging selects one source fine-level shading retaining
the source active mass up to the exact assembly loss and the number of active
coarse parents. -/
theorem exists_massPopular_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
        (loss : ENNReal) * (P.index.coarse.card : ENNReal) *
          (sourceFineLevelShading A k).shadingMass := by
  have hcoarse := coarse_nonempty_of_source_shadingMass_ne_zero A hsource
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image P.index.coarse
    (fun k => (sourceFineLevelShading A k).shadingMass) hcoarse
  refine ⟨k, hk, ?_⟩
  calc
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
        (loss : ENNReal) * A.refinement.shading.shadingMass := by
      simpa only [WithinFactor, nsmul_eq_mul] using A.retained
    _ ≤ (loss : ENNReal) *
        (∑ k' ∈ P.index.coarse,
          (sourceFineLevelShading A k').shadingMass) :=
      mul_le_mul' le_rfl
        (refinement_shadingMass_le_sum_sourceFineLevelShading A)
    _ ≤ (loss : ENNReal) *
        ((P.index.coarse.card : Nat) •
          (sourceFineLevelShading A k).shadingMass) := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_card_nsmul P.index.coarse
        (fun k' => (sourceFineLevelShading A k').shadingMass)
        (sourceFineLevelShading A k).shadingMass
        (fun k' hk' => hmax k' hk')
    _ = (loss : ENNReal) * (P.index.coarse.card : ENNReal) *
        (sourceFineLevelShading A k).shadingMass := by
      simp only [nsmul_eq_mul, mul_assoc]

/-- The mass-popular parent is simultaneously a genuine positive carrier and
the fine actual-average factor used in the exact product bound. -/
theorem exists_massPopular_sourceFineLevelShading_actualAverage
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
          (loss : ENNReal) * (P.index.coarse.card : ENNReal) *
            (sourceFineLevelShading A k).shadingMass ∧
      0 < volume (sourceFineLevelShading A k).shadedUnion ∧
      A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A k).averageMultiplicity := by
  obtain ⟨k, hk, hmass⟩ := exists_massPopular_sourceFineLevelShading A hsource
  have hkMass : (sourceFineLevelShading A k).shadingMass ≠ 0 := by
    intro hkZero
    apply hsource
    apply le_antisymm
    · simpa only [hkZero, mul_zero] using hmass
    · exact bot_le
  have hkVolume : volume (sourceFineLevelShading A k).shadedUnion ≠ 0 :=
    volume_shadedUnion_ne_zero_of_shadingMass_ne_zero
      (sourceFineLevelShading A k) hkMass
  have hkAverage := sourceFineLevelShading_averageMultiplicity_eq_fineLevel
    A k hkVolume
  refine ⟨k, hk, hmass, bot_lt_iff_ne_bot.mpr hkVolume, ?_⟩
  calc
    A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (A.fineLevel : ENNReal) :=
      refinement_averageMultiplicity_le_inducedAverage_mul_fineLevel A hsource
    _ = (P.inducedShading A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A k).averageMultiplicity := by
      rw [hkAverage]

#print axioms refinement_shadingMass_le_sum_sourceFineLevelShading
#print axioms coarse_nonempty_of_source_shadingMass_ne_zero
#print axioms exists_massPopular_sourceFineLevelShading
#print axioms exists_massPopular_sourceFineLevelShading_actualAverage

end ExactAssembly

end

end Family8ExactAssemblyMassPopularActualAverageV2
