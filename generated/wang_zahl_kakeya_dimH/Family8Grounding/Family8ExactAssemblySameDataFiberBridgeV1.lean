import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Mathlib.Tactic

/-!
# Same-data fibre bounds for an exact multiplicity assembly

For an arbitrary `ExactAssembly`, the final fibre shading is a genuine
refinement of the source fine-level shading over the same parent.  This gives
pointwise carrier, mass, union, multiplicity, and average comparisons without
adding any field to the assembly.

The available structure deliberately does not record fibre saturation after
the outer restriction.  Consequently the unconditional direction is
`final fibre average <= source fine-level average`; equality for the final
fibre needs the additional fact that the outer restriction keeps all fine
occurrences through every retained point.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ExactAssemblySameDataFiberBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
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

/-- The actual final shading restricted to one actual factorization fibre. -/
def finalFiberShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) : Shading F :=
  fiberShading P A.refinement.shading k

@[simp] theorem finalFiberShading_carrier
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) (i : iota) :
    (finalFiberShading A k).carrier i =
      if i ∈ P.index.fiber k then A.refinement.shading.carrier i else ∅ := by
  rfl

/-- On the same parent, every final fibre carrier is contained in the actual
source fine-level carrier selected by `A.fineLevel`. -/
theorem finalFiberShading_carrier_subset_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) (i : iota) :
    (finalFiberShading A k).carrier i ⊆
      (sourceFineLevelShading A k).carrier i := by
  intro x hx
  rw [finalFiberShading_carrier] at hx
  by_cases hi : i ∈ P.index.fiber k
  · rw [if_pos hi] at hx
    have hp : P.index.parent i = k :=
      (P.index.mem_fiber i k).1 hi |>.2
    simpa only [hp] using
      (refinement_carrier_subset_sourceFineLevelShading A i hx)
  · rw [if_neg hi] at hx
    exact hx.elim

/-- Same-parent final fibre mass is bounded by its source fine-level mass. -/
theorem finalFiberShading_shadingMass_le_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) :
    (finalFiberShading A k).shadingMass ≤
      (sourceFineLevelShading A k).shadingMass := by
  unfold Shading.shadingMass
  exact Finset.sum_le_sum fun i _hi =>
    measure_mono
      (finalFiberShading_carrier_subset_sourceFineLevelShading A k i)

/-- The actual final fibre union is contained in the corresponding source
fine-level union. -/
theorem finalFiberShading_shadedUnion_subset_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) :
    (finalFiberShading A k).shadedUnion ⊆
      (sourceFineLevelShading A k).shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr
    ⟨i, finalFiberShading_carrier_subset_sourceFineLevelShading A k i hxi⟩

/-- Final multiplicity inside every active fibre is bounded by the selected
source fine level. -/
theorem finalFiberShading_pointMultiplicity_le_fineLevel
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) (hk : k ∈ P.index.coarse) (x : Space) :
    (finalFiberShading A k).pointMultiplicity x ≤ A.fineLevel := by
  rw [finalFiberShading, fiberShading_pointMultiplicity]
  exact A.fiberMultiplicity_refinement_le_fineLevel k hk x

/-- The final same-parent fibre average is unconditionally at most
`fineLevel`; no positivity or division hypothesis is needed. -/
theorem finalFiberShading_averageMultiplicity_le_fineLevel
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) (hk : k ∈ P.index.coarse) :
    (finalFiberShading A k).averageMultiplicity ≤
      (A.fineLevel : ENNReal) := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  simpa only [nsmul_eq_mul] using
    (_root_.Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
        (finalFiberShading A k) A.fineLevel
        (finalFiberShading_pointMultiplicity_le_fineLevel A k hk))

/-- The volume of a finite shaded union is at most its multiplicity-counted
shading mass. -/
theorem volume_shadedUnion_le_shadingMass
    {alpha : Type*} [Fintype alpha]
    {G : ConvexFamily alpha} (Z : Shading G) :
    volume Z.shadedUnion ≤ Z.shadingMass := by
  unfold Shading.shadedUnion Shading.shadingMass
  exact measure_iUnion_fintype_le volume fun i => Z.carrier i

/-- Every positive-volume finite shading has actual average multiplicity at
least one. -/
theorem one_le_averageMultiplicity_of_volume_shadedUnion_ne_zero
    {alpha : Type*} [Fintype alpha]
    {G : ConvexFamily alpha} (Z : Shading G)
    (hvolume : volume Z.shadedUnion ≠ 0) :
    1 ≤ Z.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  calc
    1 = volume Z.shadedUnion / volume Z.shadedUnion :=
      (ENNReal.div_self hvolume (volume_shadedUnion_ne_top Z)).symm
    _ ≤ Z.shadingMass / volume Z.shadedUnion :=
      ENNReal.div_le_div_right (volume_shadedUnion_le_shadingMass Z) _

/-- A nonzero final fibre automatically gives a positive source fine-level
fibre, realizes `fineLevel` as the latter's actual average, and compares the
two same-parent averages in the honest direction. -/
theorem finalFiberShading_averageMultiplicity_le_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) (hk : k ∈ P.index.coarse)
    (hfinal : (finalFiberShading A k).shadingMass ≠ 0) :
    (finalFiberShading A k).averageMultiplicity ≤
      (sourceFineLevelShading A k).averageMultiplicity ∧
    (sourceFineLevelShading A k).averageMultiplicity =
      (A.fineLevel : ENNReal) := by
  have hsourceMass : (sourceFineLevelShading A k).shadingMass ≠ 0 := by
    intro hzero
    apply hfinal
    apply le_antisymm
    · simpa only [hzero] using
        (finalFiberShading_shadingMass_le_sourceFineLevelShading A k)
    · exact bot_le
  have hsourceVolume :=
    volume_shadedUnion_ne_zero_of_shadingMass_ne_zero
      (sourceFineLevelShading A k) hsourceMass
  have hsourceAverage :=
    sourceFineLevelShading_averageMultiplicity_eq_fineLevel
      A k hsourceVolume
  exact ⟨(finalFiberShading_averageMultiplicity_le_fineLevel A k hk).trans_eq
      hsourceAverage.symm,
    hsourceAverage⟩

/-- Positive source active mass produces one actual surviving final fibre
with positive union volume.  The same parent has source fine-level average
exactly `fineLevel`, while its final-fibre average is bounded above by it. -/
theorem exists_surviving_finalFiberShading_sameData_comparison
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      0 < volume (finalFiberShading A k).shadedUnion ∧
      (finalFiberShading A k).averageMultiplicity ≤
        (sourceFineLevelShading A k).averageMultiplicity ∧
      (sourceFineLevelShading A k).averageMultiplicity =
        (A.fineLevel : ENNReal) := by
  have href0 := refinement_shadingMass_ne_zero A hsource
  have hexists : ∃ i : iota,
      volume (A.refinement.shading.carrier i) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply href0
    unfold Shading.shadingMass
    simp only [h, Finset.sum_const_zero]
  obtain ⟨i, hiVolume⟩ := hexists
  have hiIndices : i ∈ A.refinement.indices := by
    by_contra hni
    have hempty := A.refinement.carrier_eq_empty_of_not_mem i hni
    rw [hempty, measure_empty] at hiVolume
    exact hiVolume rfl
  have hif : i ∈ P.index.fine := A.indices_subset_fine hiIndices
  let k : kappa := P.index.parent i
  have hk : k ∈ P.index.coarse := P.index.parent_mem i hif
  have hiFiber : i ∈ P.index.fiber k :=
    (P.index.mem_fiber i k).2 ⟨hif, rfl⟩
  have hsubset : A.refinement.shading.carrier i ⊆
      (finalFiberShading A k).shadedUnion := by
    intro x hx
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [finalFiberShading_carrier, if_pos hiFiber]
    exact hx
  have hvolume0 : volume (finalFiberShading A k).shadedUnion ≠ 0 := by
    intro hzero
    apply hiVolume
    have hle : volume (A.refinement.shading.carrier i) ≤
        volume (finalFiberShading A k).shadedUnion := measure_mono hsubset
    apply le_antisymm
    · simpa only [hzero] using hle
    · exact bot_le
  have hfinalMass : (finalFiberShading A k).shadingMass ≠ 0 := by
    intro hzero
    have hle := volume_shadedUnion_le_shadingMass (finalFiberShading A k)
    exact hvolume0 (le_antisymm (by simpa only [hzero] using hle) bot_le)
  obtain ⟨haverage, hsourceAverage⟩ :=
    finalFiberShading_averageMultiplicity_le_sourceFineLevelShading
      A k hk hfinalMass
  exact ⟨k, hk, bot_lt_iff_ne_bot.mpr hvolume0,
    haverage, hsourceAverage⟩

/-- A fully same-data actual-average product follows with the explicit extra
loss `fineLevel`.  Removing this loss requires fibre saturation of the final
outer restriction, which is not a field of an arbitrary `ExactAssembly`. -/
theorem refinement_averageMultiplicity_le_fineLevel_mul_sameDataAverages
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      0 < volume (finalFiberShading A k).shadedUnion ∧
      A.refinement.shading.averageMultiplicity ≤
        (A.fineLevel : ENNReal) *
          ((P.inducedShading A.refinement.shading).averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  obtain ⟨k, hk, hvolume, _hfinalLe, _hsourceAverage⟩ :=
    exists_surviving_finalFiberShading_sameData_comparison A hsource
  have hfinalOne : 1 ≤ (finalFiberShading A k).averageMultiplicity :=
    one_le_averageMultiplicity_of_volume_shadedUnion_ne_zero
      (finalFiberShading A k) (ne_of_gt hvolume)
  have hnatural :
      A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (A.fineLevel : ENNReal) :=
    refinement_averageMultiplicity_le_inducedAverage_mul_fineLevel A hsource
  refine ⟨k, hk, hvolume, hnatural.trans ?_⟩
  calc
    (P.inducedShading A.refinement.shading).averageMultiplicity *
          (A.fineLevel : ENNReal) =
        (A.fineLevel : ENNReal) *
          (P.inducedShading A.refinement.shading).averageMultiplicity :=
      mul_comm _ _
    _ ≤ ((A.fineLevel : ENNReal) *
          (P.inducedShading A.refinement.shading).averageMultiplicity) *
          (finalFiberShading A k).averageMultiplicity :=
      by
        have hprefix :
            ((A.fineLevel : ENNReal) *
              (P.inducedShading A.refinement.shading).averageMultiplicity) ≤
            ((A.fineLevel : ENNReal) *
              (P.inducedShading A.refinement.shading).averageMultiplicity) :=
          le_rfl
        simpa only [mul_one] using
          (mul_le_mul' hprefix hfinalOne)
    _ = (A.fineLevel : ENNReal) *
          ((P.inducedShading A.refinement.shading).averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by ac_rfl

#print axioms finalFiberShading_carrier_subset_sourceFineLevelShading
#print axioms finalFiberShading_shadingMass_le_sourceFineLevelShading
#print axioms finalFiberShading_averageMultiplicity_le_fineLevel
#print axioms finalFiberShading_averageMultiplicity_le_sourceFineLevelShading
#print axioms exists_surviving_finalFiberShading_sameData_comparison
#print axioms
  refinement_averageMultiplicity_le_fineLevel_mul_sameDataAverages

end ExactAssembly

end

end Family8ExactAssemblySameDataFiberBridgeV1
