import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnDensityBudgetSelectorV2
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnLongPackingMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open FamilyStickyRandomTestDependentChernoffV1
open FamilyStickyRandomFiniteChernoffV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-! The density ratio itself chooses the number of independent copies.  The
maximum with one is essential: below unit density ratio, the unconditional
one-copy exact-mean estimate is stronger than the conservative `9504`
packing estimate.  Hence the exported selector has no numerical-budget or
positive-mean callback.  A genuine lower bound for the literal normalized
maximal concentration is still needed only to show that this integer is
large, and that final scalar seam is stated explicitly below. -/

/-- Cost of one copy in the conservative long-axis packing estimate. -/
def fixedJohnDensityUnitCost
    (delta : NNReal) (iota : Type) [Fintype iota] : Real :=
  9504 * (Fintype.card iota : Real) *
    (((delta / 8 : NNReal) : Real) ^ 2)

/-- Literal maximal-concentration-to-packing-cost ratio. -/
def fixedJohnDensityRatio
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Real :=
  (fixedJohnPackingMaximalConcentration D hD).toReal /
    fixedJohnDensityUnitCost delta iota

/-- Automatic branch-free repetition count, always at least one. -/
def fixedJohnAutomaticDensityRepetitions
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Nat :=
  max 1 (Nat.floor (fixedJohnDensityRatio D hD))

theorem one_le_fixedJohnAutomaticDensityRepetitions
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    1 ≤ fixedJohnAutomaticDensityRepetitions D hD := by
  exact Nat.le_max_left _ _

theorem fixedJohnDensityUnitCost_pos
    {delta : NNReal} {iota : Type}
    [Fintype iota]
    (hdelta : 0 < delta) (hcard : Fintype.card iota ≠ 0) :
    0 < fixedJohnDensityUnitCost delta iota := by
  unfold fixedJohnDensityUnitCost
  have hcardPos : 0 < (Fintype.card iota : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero hcard
  have hrhoPos : 0 < (((delta / 8 : NNReal) : Real)) := by
    exact_mod_cast div_pos hdelta (by norm_num : (0 : NNReal) < 8)
  positivity

/-- The raw floor satisfies the conservative scalar density budget whenever
the source family is nonempty. -/
theorem fixedJohnDensityFloor_budget
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota ≠ 0) :
    9504 * (Nat.floor (fixedJohnDensityRatio D hD) : Real) *
          (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) ≤
        (fixedJohnPackingMaximalConcentration D hD).toReal := by
  let cost := fixedJohnDensityUnitCost delta iota
  let mass := (fixedJohnPackingMaximalConcentration D hD).toReal
  have hcost : 0 < cost := by
    simpa only [cost] using
      fixedJohnDensityUnitCost_pos hD.delta_pos hcard
  have hratioNonneg : 0 ≤ mass / cost :=
    div_nonneg ENNReal.toReal_nonneg hcost.le
  have hfloor : (Nat.floor (mass / cost) : Real) ≤ mass / cost :=
    Nat.floor_le hratioNonneg
  have hmul : (Nat.floor (mass / cost) : Real) * cost ≤ mass :=
    (le_div_iff₀ hcost).mp hfloor
  calc
    9504 * (Nat.floor (fixedJohnDensityRatio D hD) : Real) *
          (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) =
        (Nat.floor (mass / cost) : Real) * cost := by
      simp only [fixedJohnDensityRatio, fixedJohnDensityUnitCost, mass, cost]
      ring
    _ ≤ mass := hmul
    _ = (fixedJohnPackingMaximalConcentration D hD).toReal := rfl

/-- The automatic integer loses less than one from the literal real ratio. -/
theorem fixedJohnDensityRatio_sub_one_lt_repetitions
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    fixedJohnDensityRatio D hD - 1 <
      (fixedJohnAutomaticDensityRepetitions D hD : Real) := by
  have hfloor := Nat.sub_one_lt_floor (fixedJohnDensityRatio D hD)
  have hcast :
      (Nat.floor (fixedJohnDensityRatio D hD) : Real) ≤
        (fixedJohnAutomaticDensityRepetitions D hD : Real) := by
    exact_mod_cast Nat.le_max_right 1
      (Nat.floor (fixedJohnDensityRatio D hD))
  exact hfloor.trans_le hcast

/-- A lower bound for normalized maximal concentration converts directly
into a lower bound for the automatic integer.  This is the remaining honest
nondegenerate-density seam. -/
theorem repetitions_lower_of_densityRatio
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (J0 : Nat)
    (hlower : (J0 : Real) + 1 ≤ fixedJohnDensityRatio D hD) :
    J0 ≤ fixedJohnAutomaticDensityRepetitions D hD := by
  have hfloor : J0 ≤ Nat.floor (fixedJohnDensityRatio D hD) := by
    apply Nat.le_floor
    linarith
  exact hfloor.trans (Nat.le_max_right _ _)

/-- For the automatic count, every exact finite mean satisfies the scale
condition required by the finite Chernoff selector.  The floor-zero branch
uses the unconditional one-copy bound; the positive branch uses the honest
long-axis packing estimate. -/
theorem automaticDensityRepetitions_mul_finiteMean_le_cap
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    (fixedJohnAutomaticDensityRepetitions D hD : Real) *
        fixedJohnFiniteMean (fixedJohnPackingGridVector D hD) D hD K ≤
      fixedJohnTranslationPaperCap
        (fixedJohnPackingGridVector D hD) D hD K := by
  by_cases hfloor : Nat.floor (fixedJohnDensityRatio D hD) = 0
  · have hrep : fixedJohnAutomaticDensityRepetitions D hD = 1 := by
      norm_num [fixedJohnAutomaticDensityRepetitions, hfloor]
    rw [hrep]
    norm_num
    exact fixedJohnFiniteMean_le_paperCap
      (fixedJohnPackingGridVector D hD) D hD K
  · have hcard : Fintype.card iota ≠ 0 := by
      intro hcard
      apply hfloor
      simp only [fixedJohnDensityRatio, fixedJohnDensityUnitCost, hcard,
        Nat.cast_zero, mul_zero, zero_mul, div_zero, Nat.floor_zero]
    have hone : 1 ≤ Nat.floor (fixedJohnDensityRatio D hD) :=
      Nat.one_le_iff_ne_zero.mpr hfloor
    have hrep : fixedJohnAutomaticDensityRepetitions D hD =
        Nat.floor (fixedJohnDensityRatio D hD) := by
      exact Nat.max_eq_right hone
    rw [hrep]
    calc
      (Nat.floor (fixedJohnDensityRatio D hD) : Real) *
          fixedJohnFiniteMean (fixedJohnPackingGridVector D hD) D hD K ≤
        (Nat.floor (fixedJohnDensityRatio D hD) : Real) *
          fixedJohnLongPackingMean D hD K :=
        mul_le_mul_of_nonneg_left
          (fixedJohnPackingFiniteMean_le_longPackingMean D hD K)
          (Nat.cast_nonneg _)
      _ ≤ fixedJohnTranslationPaperCap
          (fixedJohnPackingGridVector D hD) D hD K :=
        fixedJohnLongPackingMean_scale_le_paperCap_of_densityBudget
          D hD (Nat.floor (fixedJohnDensityRatio D hD))
            (fixedJohnDensityFloor_budget D hD hcard) K

/-- Fully automatic bounded finite packing selector.  No positive-mean or
numerical density-budget premise remains. -/
theorem exists_boundedPackingTuple_automaticDensityRepetitions
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    ∃ omega : Fin (fixedJohnAutomaticDensityRepetitions D hD) →
        FixedJohnPackingTranslation D hD,
      (∀ K : FixedJohnTest D hD,
        (∑ j, (normalizedTranslationBodyLoadNat
          (fixedJohnPackingGridVector D hD) D
          (fixedJohnCatalogueBody hD) K (omega j) : Real)) ≤
          fixedJohnTailParameter D hD *
            fixedJohnTranslationPaperCap
              (fixedJohnPackingGridVector D hD) D hD K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D)
          a).card ≤
            fixedJohnLoadThreshold
              (fixedJohnPackingGridVector D hD) D hD) := by
  let gridVector := fixedJohnPackingGridVector D hD
  let repetitions := fixedJohnAutomaticDensityRepetitions D hD
  let mean : FixedJohnTest D hD → Real :=
    fixedJohnFiniteMean gridVector D hD
  let cap : FixedJohnTest D hD → Real :=
    fixedJohnTranslationPaperCap gridVector D hD
  let A := fixedJohnTailParameter D hD
  obtain ⟨omega, htail⟩ :=
    exists_product_choice_load_le_A_mul_cap
      (Finset.univ : Finset (FixedJohnTest D hD)) repetitions
      (fun K g ↦ (normalizedTranslationBodyLoadNat gridVector D
        (fixedJohnCatalogueBody hD) K g : Real)) cap mean A
      (fun K _hK ↦ fixedJohnPaperCap_nonneg gridVector D hD K)
      (fun K _hK ↦ fixedJohnFiniteMean_nonneg gridVector D hD K)
      (fun _K _hK _g ↦ Nat.cast_nonneg _)
      (fun K _hK g ↦ fixedJohnLoad_le_paperCap gridVector D hD K g)
      (fun K _hK ↦ by
        exact (sum_fixedJohnLoad_eq_card_mul_finiteMean
          gridVector D hD K).le)
      (fun K _hK ↦ by
        simpa only [repetitions, mean, cap, gridVector] using
          automaticDensityRepetitions_mul_finiteMean_le_cap D hD K)
      (fixedJohnTailRoom D hD)
  have hunit : ∀ a :
      NormalizedRigidCandidate (FixedJohnPackingTranslation D hD) iota,
      (normalizedRigidCandidateTube
        (translationCandidateMotion gridVector) D a).carrier ⊆
          Metric.closedBall (0 : Space) 1 :=
    normalizedRigidCandidateTube_subset_unitBall_of_gridVector_norm_le_one
      gridVector D hD (fun g ↦ by
        simpa only [gridVector] using
          fixedJohnPackingGridVector_norm_le_one D hD g)
  obtain ⟨cover, hcoverActive, hcoverCard, hcover⟩ :=
    exists_fixedJohn_normalizedConflict_bodyMultiCover
      (translationCandidateMotion gridVector) D hD hunit omega
  refine ⟨omega, ?_, ?_⟩
  · intro K
    simpa only [Finset.mem_univ, repetitions, mean, cap, A, gridVector,
      productLoad] using htail K (Finset.mem_univ K)
  · have hconf :=
      normalizedConflictIndices_card_le_of_bodyMultiCover
        (coverMultiplicity := 1)
        (loadThreshold := fixedJohnLoadThreshold gridVector D hD)
        gridVector D (fixedJohnCatalogueBody hD) Finset.univ omega cover
        hcoverActive hcoverCard hcover (fun K _hK ↦ by
          have hreal :=
            (htail K (Finset.mem_univ K)).trans
              (fixedJohn_threshold_le_loadThreshold gridVector D hD K)
          have hcast :
              ((∑ j, normalizedTranslationBodyLoadNat gridVector D
                (fixedJohnCatalogueBody hD) K (omega j) : Nat) : Real) ≤
                (fixedJohnLoadThreshold gridVector D hD : Real) := by
            simpa only [Nat.cast_sum, repetitions, mean, cap, A,
              productLoad] using hreal
          exact_mod_cast hcast)
    simpa only [one_mul, repetitions, gridVector] using hconf

#print axioms one_le_fixedJohnAutomaticDensityRepetitions
#print axioms fixedJohnDensityUnitCost_pos
#print axioms fixedJohnDensityFloor_budget
#print axioms fixedJohnDensityRatio_sub_one_lt_repetitions
#print axioms repetitions_lower_of_densityRatio
#print axioms automaticDensityRepetitions_mul_finiteMean_le_cap
#print axioms exists_boundedPackingTuple_automaticDensityRepetitions

end
end Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
