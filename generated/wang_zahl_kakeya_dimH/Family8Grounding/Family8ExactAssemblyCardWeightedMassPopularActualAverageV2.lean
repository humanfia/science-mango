import Family8Grounding.Family8ExactAssemblyMassPopularActualAverageV2
import Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
import Submission.Kakeya.Uniformity.PenalizedScaleChoice
import Mathlib.Tactic

/-!
# Card-weighted mass-popular fibres in an exact assembly, V2

Maximizing source fine-level mass divided by the actual fibre cardinality and
using the exact fibre partition gives

`sourceMass * selectedFiber.card <= loss * fine.card * selectedFiberMass`.

This is the count-sensitive replacement for ordinary coarse-cardinality
pigeonholing.  The selected object is still the genuine fine actual-average
factor of the same exact assembly.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ExactAssemblyCardWeightedMassPopularActualAverageV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8ExactAssemblyMassPopularActualAverageV2.ExactAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : Nat}

/-- A positive-cardinality fibre selected by its mass/cardinality score.
The total weight is the exact active fine cardinality. -/
theorem exists_cardWeighted_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0)
    (hfiber : ∀ k ∈ P.index.coarse, (P.index.fiber k).Nonempty) :
    ∃ k ∈ P.index.coarse,
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass *
          (P.index.fiber k).card ≤
        (loss : ENNReal) * (P.index.fine.card : ENNReal) *
          (sourceFineLevelShading A k).shadingMass := by
  let mass : kappa → ENNReal :=
    fun k => (sourceFineLevelShading A k).shadingMass
  let weight : kappa → ENNReal :=
    fun k => (P.index.fiber k).card
  have hcoarse := coarse_nonempty_of_source_shadingMass_ne_zero A hsource
  obtain ⟨C⟩ := exists_penalizedScaleChoice
    P.index.coarse mass weight hcoarse
  have hweight0 : ∀ k ∈ P.index.coarse, weight k ≠ 0 := by
    intro k hk
    dsimp only [weight]
    exact_mod_cast (Finset.card_ne_zero.mpr (hfiber k hk))
  have hweightTop : ∀ k ∈ P.index.coarse, weight k ≠ ∞ := by
    intro k _hk
    dsimp only [weight]
    exact ENNReal.coe_ne_top
  have hcross : ∀ k ∈ P.index.coarse,
      mass k * weight C.index ≤ mass C.index * weight k := by
    intro k hk
    exact C.cross_stable hweight0 hweightTop hk
  have hsumCross :
      (∑ k ∈ P.index.coarse, mass k) * weight C.index ≤
        mass C.index * (∑ k ∈ P.index.coarse, weight k) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hcross k hk
  have hweightSum :
      (∑ k ∈ P.index.coarse, weight k) =
        (P.index.fine.card : ENNReal) := by
    dsimp only [weight]
    exact_mod_cast P.index.card_eq_sum_card_fiber.symm
  refine ⟨C.index, C.index_mem, ?_⟩
  calc
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass *
          (P.index.fiber C.index).card ≤
        ((loss : ENNReal) * A.refinement.shading.shadingMass) *
          weight C.index := by
      apply mul_le_mul'
      · simpa only [WithinFactor, nsmul_eq_mul] using A.retained
      · rfl
    _ ≤ ((loss : ENNReal) *
          (∑ k ∈ P.index.coarse, mass k)) * weight C.index := by
      exact mul_le_mul' (mul_le_mul' le_rfl
        (refinement_shadingMass_le_sum_sourceFineLevelShading A)) le_rfl
    _ = (loss : ENNReal) *
          ((∑ k ∈ P.index.coarse, mass k) * weight C.index) := by
      ac_rfl
    _ ≤ (loss : ENNReal) *
          (mass C.index * (∑ k ∈ P.index.coarse, weight k)) :=
      mul_le_mul' le_rfl hsumCross
    _ = (loss : ENNReal) * (P.index.fine.card : ENNReal) *
          (sourceFineLevelShading A C.index).shadingMass := by
      rw [hweightSum]
      dsimp only [mass]
      ac_rfl

/-- The card-weighted selected fibre is a positive actual carrier and is the
fine actual-average factor for the very same exact assembly. -/
theorem exists_cardWeighted_sourceFineLevelShading_actualAverage
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0)
    (hfiber : ∀ k ∈ P.index.coarse, (P.index.fiber k).Nonempty) :
    ∃ k ∈ P.index.coarse,
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass *
            (P.index.fiber k).card ≤
          (loss : ENNReal) * (P.index.fine.card : ENNReal) *
            (sourceFineLevelShading A k).shadingMass ∧
      0 < volume (sourceFineLevelShading A k).shadedUnion ∧
      A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A k).averageMultiplicity := by
  obtain ⟨k, hk, hmass⟩ :=
    exists_cardWeighted_sourceFineLevelShading A hsource hfiber
  have hkCard0 : ((P.index.fiber k).card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (hfiber k hk))
  have hkMass : (sourceFineLevelShading A k).shadingMass ≠ 0 := by
    intro hkZero
    have hleft :
        (IndexedShadingRefinement.restrictTo
          Y P.index.fine).shading.shadingMass *
            (P.index.fiber k).card ≠ 0 := mul_ne_zero hsource hkCard0
    apply hleft
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

end ExactAssembly

#print axioms ExactAssembly.exists_cardWeighted_sourceFineLevelShading
#print axioms ExactAssembly.exists_cardWeighted_sourceFineLevelShading_actualAverage

end

end Family8ExactAssemblyCardWeightedMassPopularActualAverageV2
