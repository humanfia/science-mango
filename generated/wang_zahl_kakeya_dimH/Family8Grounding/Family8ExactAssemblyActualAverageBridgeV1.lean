import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
import Mathlib.Tactic

/-!
# Actual average multiplicities in an exact factoring assembly

The natural levels stored by `FactoringMultiplicityAssembly.ExactAssembly`
can be related to genuine shadings, provided the source active shading mass is
nonzero.  The outer level is exactly the average multiplicity of the induced
coarse shading of the final refinement.  The fine level is exactly the
average multiplicity of an actual source-fibre level shading on at least one
surviving parent.

The latter distinction is essential: `fineLevel` records the source fibre
statistic selected before `coarseLevelBucket` and the final outer restriction.
It is not asserted to equal the average multiplicity of the final refinement
inside that fibre.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ExactAssemblyActualAverageBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Nonzero total shaded mass forces the actual shaded union to have nonzero
volume. -/
theorem volume_shadedUnion_ne_zero_of_shadingMass_ne_zero
    {alpha : Type*} [Fintype alpha]
    {G : ConvexFamily alpha} (Z : Shading G)
    (hmass : Z.shadingMass ≠ 0) :
    volume Z.shadedUnion ≠ 0 := by
  intro hunion
  apply hmass
  unfold Shading.shadingMass
  apply Finset.sum_eq_zero
  intro i _hi
  have hle : volume (Z.carrier i) ≤ volume Z.shadedUnion :=
    measure_mono (Set.subset_iUnion (fun j => Z.carrier j) i)
  apply le_antisymm
  · simpa only [hunion] using hle
  · exact bot_le

/-- A finite convex-family shading has finite shaded-union volume. -/
theorem volume_shadedUnion_ne_top
    {alpha : Type*} [Fintype alpha]
    {G : ConvexFamily alpha} (Z : Shading G) :
    volume Z.shadedUnion ≠ ∞ := by
  exact ((measure_mono Z.shadedUnion_subset_familyUnion).trans_lt
    (familyUnion_isCompact G).measure_lt_top).ne

/-- If the point multiplicity is the natural number `n` everywhere on a
positive-volume shaded union, its actual average multiplicity is exactly
`n`. -/
theorem averageMultiplicity_eq_nat_of_constant_on_shadedUnion
    {alpha : Type*} [Fintype alpha]
    {G : ConvexFamily alpha} (Z : Shading G) (n : Nat)
    (hvolume : volume Z.shadedUnion ≠ 0)
    (hconstant : ∀ x ∈ Z.shadedUnion, Z.pointMultiplicity x = n) :
    Z.averageMultiplicity = (n : ENNReal) := by
  have hmass :
      Z.shadingMass = (n : ENNReal) * volume Z.shadedUnion := by
    rw [← Z.lintegral_pointMultiplicity]
    calc
      (∫⁻ x, (Z.pointMultiplicity x : ENNReal) ∂volume) =
          ∫⁻ x, Z.shadedUnion.indicator
            (fun _ => (n : ENNReal)) x ∂volume := by
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ Z.shadedUnion
        · simp only [Set.indicator_of_mem hx]
          exact_mod_cast hconstant x hx
        · have hzero : Z.pointMultiplicity x = 0 := by
            apply Nat.eq_zero_of_not_pos
            intro hpos
            exact hx ((Z.pointMultiplicity_pos_iff_mem_shadedUnion x).1 hpos)
          simp [hx, hzero]
      _ = (n : ENNReal) * volume Z.shadedUnion := by
        rw [lintegral_indicator Z.shadedUnion_measurableSet]
        simp
  unfold Shading.averageMultiplicity
  rw [hmass]
  exact ENNReal.mul_div_cancel_right hvolume (volume_shadedUnion_ne_top Z)

namespace ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : Nat}

/-- Positive source active mass survives every exact assembly refinement. -/
theorem refinement_shadingMass_ne_zero
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    A.refinement.shading.shadingMass ≠ 0 := by
  intro href
  have hle :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
        0 := by
    simpa only [WithinFactor, href, nsmul_zero] using A.retained
  exact hsource (bot_unique hle)

theorem refinement_shadingMass_pos
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    0 < A.refinement.shading.shadingMass := by
  exact bot_lt_iff_ne_bot.mpr (refinement_shadingMass_ne_zero A hsource)

/-- Consequently the final refinement has a positive-volume shaded union. -/
theorem refinement_volume_shadedUnion_pos
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    0 < volume A.refinement.shading.shadedUnion := by
  exact bot_lt_iff_ne_bot.mpr
    (volume_shadedUnion_ne_zero_of_shadingMass_ne_zero A.refinement.shading
      (refinement_shadingMass_ne_zero A hsource))

/-- Restricting the final refinement once more to the factorization's active
fine indices does not change its shaded union: all carriers outside those
indices are already empty. -/
theorem restrictTo_fine_shadedUnion_eq
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (IndexedShadingRefinement.restrictTo A.refinement.shading
      P.index.fine).shading.shadedUnion =
        A.refinement.shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [IndexedShadingRefinement.restrictTo_carrier] at hxi
    by_cases hif : i ∈ P.index.fine
    · rw [if_pos hif] at hxi
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    · rw [if_neg hif] at hxi
      exact hxi.elim
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hif : i ∈ P.index.fine := by
      by_contra hif
      have hni : i ∉ A.refinement.indices := fun hi =>
        hif (A.indices_subset_fine hi)
      rw [A.refinement.carrier_eq_empty_of_not_mem i hni] at hxi
      exact hxi
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hif]
    exact hxi

/-- The actual induced-coarse shading has exactly the same shaded union as
the final fine refinement. -/
theorem inducedShading_shadedUnion_eq_refinement
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (P.inducedShading A.refinement.shading).shadedUnion =
      A.refinement.shading.shadedUnion := by
  calc
    (P.inducedShading A.refinement.shading).shadedUnion =
        (IndexedShadingRefinement.restrictTo A.refinement.shading
          P.index.fine).shading.shadedUnion :=
      P.inducedShading_shadedUnion_eq A.refinement.shading
    _ = A.refinement.shading.shadedUnion :=
      restrictTo_fine_shadedUnion_eq A

/-- On its actual union, the induced coarse shading has point multiplicity
exactly the automatically selected outer level. -/
theorem inducedShading_pointMultiplicity_eq_outerLevel_on
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    {x : Space}
    (hx : x ∈ (P.inducedShading A.refinement.shading).shadedUnion) :
    (P.inducedShading A.refinement.shading).pointMultiplicity x =
      A.outerLevel := by
  have hxref : x ∈ A.refinement.shading.shadedUnion := by
    rw [← inducedShading_shadedUnion_eq_refinement A]
    exact hx
  calc
    (P.inducedShading A.refinement.shading).pointMultiplicity x =
        P.outerMultiplicity A.refinement.shading x :=
      P.pointMultiplicity_inducedShading_eq_outer A.refinement.shading x
    _ = A.outerLevel := A.outerStatistic_constant x hxref

/-- The selected outer level is the genuine average multiplicity of the
induced coarse shading, not merely a pointwise natural bound. -/
theorem inducedShading_averageMultiplicity_eq_outerLevel
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    (P.inducedShading A.refinement.shading).averageMultiplicity =
      (A.outerLevel : ENNReal) := by
  apply averageMultiplicity_eq_nat_of_constant_on_shadedUnion
  · rw [inducedShading_shadedUnion_eq_refinement A]
    exact ne_of_gt (refinement_volume_shadedUnion_pos A hsource)
  · intro x hx
    exact inducedShading_pointMultiplicity_eq_outerLevel_on A hx

/-- The honest fine object associated to `A.fineLevel` over one parent is the
source fibre restricted to that actual multiplicity level.  It is not the
final refinement fibre. -/
def sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) : Shading F :=
  fiberLevelShading P Y k A.fineLevel

/-- Every final carrier is contained in the corresponding actual source
fine-level shading.  This is the precise direction surviving the
`assembledRefinement`, `coarseLevelBucket`, and outer restriction steps. -/
theorem refinement_carrier_subset_sourceFineLevelShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (i : iota) :
    A.refinement.shading.carrier i ⊆
      (sourceFineLevelShading A (P.index.parent i)).carrier i := by
  intro x hx
  have hiIndices : i ∈ A.refinement.indices := by
    by_contra hni
    rw [A.refinement.carrier_eq_empty_of_not_mem i hni] at hx
    exact hx
  have hif : i ∈ P.index.fine := A.indices_subset_fine hiIndices
  have hiFiber : i ∈ P.index.fiber (P.index.parent i) :=
    (P.index.mem_fiber i (P.index.parent i)).2 ⟨hif, rfl⟩
  rw [sourceFineLevelShading, fiberLevelShading_carrier, if_pos hiFiber]
  exact ⟨A.refinement.carrier_subset i hx,
    A.fineStatistic_constant i x hx⟩

/-- On its actual carrier, the source fine-level shading has point
multiplicity exactly `fineLevel`. -/
theorem sourceFineLevelShading_pointMultiplicity_eq_fineLevel_on
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa) {x : Space}
    (hx : x ∈ (sourceFineLevelShading A k).shadedUnion) :
    (sourceFineLevelShading A k).pointMultiplicity x = A.fineLevel := by
  have hstat : P.fiberMultiplicity Y k x = A.fineLevel := by
    simpa only [sourceFineLevelShading, fiberLevelShading] using
      (statistic_eq_on_restrictStatisticLevel
        (fiberShading P Y k) (P.fiberMultiplicity Y k)
        (measurableSet_fiberMultiplicity_eq P Y k) A.fineLevel hx)
  have hxSlice :
      x ∈ statisticSlice (fiberShading P Y k)
        (P.fiberMultiplicity Y k) A.fineLevel := by
    simpa only [sourceFineLevelShading, fiberLevelShading,
      restrictStatisticLevel_shadedUnion] using hx
  calc
    (sourceFineLevelShading A k).pointMultiplicity x =
        (fiberShading P Y k).pointMultiplicity x := by
      rw [sourceFineLevelShading, fiberLevelShading,
        pointMultiplicity_restrictStatisticLevel, if_pos hxSlice]
    _ = P.fiberMultiplicity Y k x :=
      fiberShading_pointMultiplicity P Y k x
    _ = A.fineLevel := hstat

/-- Any positive-volume source fine-level shading realizes `fineLevel` as an
actual average multiplicity. -/
theorem sourceFineLevelShading_averageMultiplicity_eq_fineLevel
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (k : kappa)
    (hvolume : volume (sourceFineLevelShading A k).shadedUnion ≠ 0) :
    (sourceFineLevelShading A k).averageMultiplicity =
      (A.fineLevel : ENNReal) := by
  exact averageMultiplicity_eq_nat_of_constant_on_shadedUnion
    (sourceFineLevelShading A k) A.fineLevel hvolume
      (fun x hx => sourceFineLevelShading_pointMultiplicity_eq_fineLevel_on
        A k hx)

/-- Positive retained mass supplies at least one genuine surviving parent
whose source fine-level shading has positive union volume and average exactly
`fineLevel`. -/
theorem exists_sourceFineLevelShading_averageMultiplicity_eq_fineLevel
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      0 < volume (sourceFineLevelShading A k).shadedUnion ∧
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
  have hsubset : A.refinement.shading.carrier i ⊆
      (sourceFineLevelShading A k).shadedUnion := by
    intro x hx
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact refinement_carrier_subset_sourceFineLevelShading A i hx
  have hvolume0 : volume (sourceFineLevelShading A k).shadedUnion ≠ 0 := by
    intro hzero
    apply hiVolume
    have hle : volume (A.refinement.shading.carrier i) ≤
        volume (sourceFineLevelShading A k).shadedUnion :=
      measure_mono hsubset
    apply le_antisymm
    · simpa only [hzero] using hle
    · exact bot_le
  exact ⟨k, hk, bot_lt_iff_ne_bot.mpr hvolume0,
    sourceFineLevelShading_averageMultiplicity_eq_fineLevel A k hvolume0⟩

/-- The natural product bound with its outer factor replaced by the genuine
induced-coarse average multiplicity. -/
theorem refinement_averageMultiplicity_le_inducedAverage_mul_fineLevel
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    A.refinement.shading.averageMultiplicity ≤
      (P.inducedShading A.refinement.shading).averageMultiplicity *
        (A.fineLevel : ENNReal) := by
  have houter := inducedShading_averageMultiplicity_eq_outerLevel A hsource
  calc
    A.refinement.shading.averageMultiplicity ≤
        (A.outerLevel * A.fineLevel : Nat) :=
      A.averageMultiplicity_le_product
    _ = (A.outerLevel : ENNReal) * (A.fineLevel : ENNReal) := by
      norm_cast
    _ = (P.inducedShading A.refinement.shading).averageMultiplicity *
          (A.fineLevel : ENNReal) := by rw [houter]

/-- Strongest honest actual-average form available from `ExactAssembly`:
the refinement average is bounded by the product of the actual induced-coarse
average and the actual average of one positive surviving source-fibre level
shading. -/
theorem refinement_averageMultiplicity_le_product_actualAverages
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      0 < volume (sourceFineLevelShading A k).shadedUnion ∧
      A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A k).averageMultiplicity := by
  obtain ⟨k, hk, hvolume, hfineAverage⟩ :=
    exists_sourceFineLevelShading_averageMultiplicity_eq_fineLevel A hsource
  refine ⟨k, hk, hvolume, ?_⟩
  calc
    A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (A.fineLevel : ENNReal) :=
      refinement_averageMultiplicity_le_inducedAverage_mul_fineLevel A hsource
    _ = (P.inducedShading A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A k).averageMultiplicity := by
      rw [hfineAverage]

#print axioms refinement_shadingMass_ne_zero
#print axioms refinement_shadingMass_pos
#print axioms refinement_volume_shadedUnion_pos
#print axioms inducedShading_shadedUnion_eq_refinement
#print axioms inducedShading_averageMultiplicity_eq_outerLevel
#print axioms refinement_carrier_subset_sourceFineLevelShading
#print axioms sourceFineLevelShading_averageMultiplicity_eq_fineLevel
#print axioms
  exists_sourceFineLevelShading_averageMultiplicity_eq_fineLevel
#print axioms
  refinement_averageMultiplicity_le_inducedAverage_mul_fineLevel
#print axioms refinement_averageMultiplicity_le_product_actualAverages

end ExactAssembly

end

end Family8ExactAssemblyActualAverageBridgeV1
