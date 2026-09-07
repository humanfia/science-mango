import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV3
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1
open Family8PolynomialJohnFrameBoxTestNetV1
open FamilyStickyRandomTestDependentChernoffV1
open FamilyStickyRandomFiniteChernoffV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Fixed-John selection from the literal finite-law mean

This module removes the incompatible simultaneous-product-lattice premise.
For an actual finite translation law supported in the unit ball, the mean is
the literal uniform average of the containment load.  Its sum identity is
formal, while the already proved single-load estimate bounds it by the paper
cap.  We therefore choose the largest common integer repetition budget given
by the finite infimum of `cap / mean`, a logarithmic union-bound parameter,
and a single ceiling threshold.

The resulting repetition count is proved to be at least one.  No claim of a
large paper-strength repetition count is made here: that requires the later
geometric small-mean estimate for a genuine bounded finite motion law.
-/

abbrev FixedJohnTest
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :=
  Fin (Fintype.card
    (CatalogueIndex (delta / 8) (admissibleNormalizedRadiusPos hD)))

/-- The exact mean of one fixed-John containment load under the supplied
uniform finite translation law. -/
def fixedJohnFiniteMean
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : Real :=
  (∑ g : translation,
      (normalizedTranslationBodyLoadNat gridVector D
        (fixedJohnCatalogueBody hD) K g : Real)) /
    (Fintype.card translation : Real)

theorem fixedJohnFiniteMean_nonneg
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    0 ≤ fixedJohnFiniteMean gridVector D hD K := by
  unfold fixedJohnFiniteMean
  positivity

theorem sum_fixedJohnLoad_eq_card_mul_finiteMean
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    (∑ g : translation,
      (normalizedTranslationBodyLoadNat gridVector D
        (fixedJohnCatalogueBody hD) K g : Real)) =
      (Fintype.card translation : Real) *
        fixedJohnFiniteMean gridVector D hD K := by
  unfold fixedJohnFiniteMean
  have hcard : (Fintype.card translation : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The canonical paper cap bounds every literal fixed-John load. -/
theorem fixedJohnLoad_le_paperCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) (g : translation) :
    (normalizedTranslationBodyLoadNat gridVector D
        (fixedJohnCatalogueBody hD) K g : Real) ≤
      fixedJohnTranslationPaperCap gridVector D hD K := by
  rw [← normalizedTranslationBodyGrid_singleLoad
    gridVector D (fixedJohnCatalogueBody hD) Finset.univ K g]
  exact
    FamilyStickyActualPaperSingleLoadAutomaticV1.ActualTubeTranslationGrid.singleLoad_real_le_paperSingleLoadCap
      (normalizedTranslationBodyGrid gridVector D
        (fixedJohnCatalogueBody hD) Finset.univ) K g
      ((div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8)).trans hD.delta_le_half)
      (div_pos hD.delta_pos (by norm_num))

theorem fixedJohnPaperCap_nonneg
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    0 ≤ fixedJohnTranslationPaperCap gridVector D hD K := by
  unfold fixedJohnTranslationPaperCap normalizedTranslationBodyPaperCap
  exact ENNReal.toReal_nonneg

/-- Averaging the pointwise load cap gives `mean ≤ cap`. -/
theorem fixedJohnFiniteMean_le_paperCap
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnFiniteMean gridVector D hD K ≤
      fixedJohnTranslationPaperCap gridVector D hD K := by
  have hcardPos : 0 < (Fintype.card translation : Real) := by
    exact_mod_cast Fintype.card_pos
  unfold fixedJohnFiniteMean
  apply (div_le_iff₀ hcardPos).2
  calc
    (∑ g : translation,
      (normalizedTranslationBodyLoadNat gridVector D
        (fixedJohnCatalogueBody hD) K g : Real)) ≤
        ∑ _g : translation,
          fixedJohnTranslationPaperCap gridVector D hD K := by
      exact Finset.sum_le_sum fun g _hg ↦
        fixedJohnLoad_le_paperCap gridVector D hD K g
    _ = fixedJohnTranslationPaperCap gridVector D hD K *
        (Fintype.card translation : Real) := by simp [mul_comm]

def fixedJohnPositiveMeanTests
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    Finset (FixedJohnTest D hD) :=
  Finset.univ.filter fun K ↦ 0 < fixedJohnFiniteMean gridVector D hD K

/-- Largest common integer repetition count certified solely by the exact
finite means and the paper single-load caps. -/
def fixedJohnRepetitions
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Nat :=
  if h : (fixedJohnPositiveMeanTests gridVector D hD).Nonempty then
    Nat.floor ((fixedJohnPositiveMeanTests gridVector D hD).inf' h fun K ↦
      fixedJohnTranslationPaperCap gridVector D hD K /
        fixedJohnFiniteMean gridVector D hD K)
  else 1

theorem fixedJohnRepetitions_mul_mean_le_cap
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    ∀ K : FixedJohnTest D hD,
      (fixedJohnRepetitions gridVector D hD : Real) *
          fixedJohnFiniteMean gridVector D hD K ≤
        fixedJohnTranslationPaperCap gridVector D hD K := by
  intro K
  have hcap := fixedJohnPaperCap_nonneg gridVector D hD K
  by_cases hmeanPos : 0 < fixedJohnFiniteMean gridVector D hD K
  · have hKpos : K ∈ fixedJohnPositiveMeanTests gridVector D hD :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ K, hmeanPos⟩
    have hpositive :
        (fixedJohnPositiveMeanTests gridVector D hD).Nonempty := ⟨K, hKpos⟩
    let budget : Real :=
      (fixedJohnPositiveMeanTests gridVector D hD).inf' hpositive fun L ↦
        fixedJohnTranslationPaperCap gridVector D hD L /
          fixedJohnFiniteMean gridVector D hD L
    have hbudgetNonneg : 0 ≤ budget := by
      apply Finset.le_inf' hpositive
      intro L hL
      have hLpos : 0 < fixedJohnFiniteMean gridVector D hD L :=
        (Finset.mem_filter.mp hL).2
      exact div_nonneg
        (fixedJohnPaperCap_nonneg gridVector D hD L) hLpos.le
    have hfloor : (Nat.floor budget : Real) ≤ budget :=
      Nat.floor_le hbudgetNonneg
    have hbudgetK : budget ≤
        fixedJohnTranslationPaperCap gridVector D hD K /
          fixedJohnFiniteMean gridVector D hD K :=
      Finset.inf'_le (fun L ↦
        fixedJohnTranslationPaperCap gridVector D hD L /
          fixedJohnFiniteMean gridVector D hD L) hKpos
    have hJ : (fixedJohnRepetitions gridVector D hD : Real) =
        Nat.floor budget := by
      simp only [fixedJohnRepetitions, dif_pos hpositive, budget]
    rw [hJ]
    exact (le_div_iff₀ hmeanPos).mp (hfloor.trans hbudgetK)
  · have hmeanZero : fixedJohnFiniteMean gridVector D hD K = 0 :=
      le_antisymm (le_of_not_gt hmeanPos)
        (fixedJohnFiniteMean_nonneg gridVector D hD K)
    simp [hmeanZero, hcap]

/-- The exact mean bound guarantees that the canonical selector retains at
least one copy. -/
theorem one_le_fixedJohnRepetitions
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    1 ≤ fixedJohnRepetitions gridVector D hD := by
  by_cases hpositive :
      (fixedJohnPositiveMeanTests gridVector D hD).Nonempty
  · rw [fixedJohnRepetitions, dif_pos hpositive]
    apply Nat.le_floor
    apply Finset.le_inf' hpositive
    intro K hK
    have hKpos : 0 < fixedJohnFiniteMean gridVector D hD K :=
      (Finset.mem_filter.mp hK).2
    exact (le_div_iff₀ hKpos).2
      (by simpa using fixedJohnFiniteMean_le_paperCap gridVector D hD K)
  · simp [fixedJohnRepetitions, hpositive]

/-- Logarithmic tail with one full unit of slack. -/
def fixedJohnTailParameter
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Real :=
  max 1 (Real.log ((Fintype.card (FixedJohnTest D hD) : Real) *
    Real.exp (Real.exp 1 - 1) + 1))

theorem one_le_fixedJohnTailParameter
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    1 ≤ fixedJohnTailParameter D hD := le_max_left _ _

theorem fixedJohnTailRoom
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    ((Finset.univ : Finset (FixedJohnTest D hD)).card : Real) *
        Real.exp (Real.exp 1 - 1) <
      Real.exp (fixedJohnTailParameter D hD) := by
  let x : Real :=
    ((Finset.univ : Finset (FixedJohnTest D hD)).card : Real) *
      Real.exp (Real.exp 1 - 1)
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hx1 : 0 < x + 1 := by linarith
  have hxlt : x < Real.exp (Real.log (x + 1)) := by
    rw [Real.exp_log hx1]
    linarith
  have hmono : Real.exp (Real.log (x + 1)) ≤
      Real.exp (max 1 (Real.log (x + 1))) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  simpa only [fixedJohnTailParameter, x, Finset.card_univ] using
    hxlt.trans_le hmono

/-- One integer threshold which dominates every test-dependent Chernoff
threshold. -/
def fixedJohnLoadThreshold
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Nat :=
  Nat.ceil (fixedJohnTailParameter D hD *
    ∑ K : FixedJohnTest D hD,
      fixedJohnTranslationPaperCap gridVector D hD K)

theorem fixedJohn_threshold_le_loadThreshold
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnTailParameter D hD *
        fixedJohnTranslationPaperCap gridVector D hD K ≤
      (fixedJohnLoadThreshold gridVector D hD : Real) := by
  have hcapSum : fixedJohnTranslationPaperCap gridVector D hD K ≤
      ∑ L : FixedJohnTest D hD,
        fixedJohnTranslationPaperCap gridVector D hD L := by
    exact Finset.single_le_sum
      (fun L _hL ↦ fixedJohnPaperCap_nonneg gridVector D hD L)
      (Finset.mem_univ K)
  calc
    fixedJohnTailParameter D hD *
        fixedJohnTranslationPaperCap gridVector D hD K ≤
      fixedJohnTailParameter D hD *
        ∑ L : FixedJohnTest D hD,
          fixedJohnTranslationPaperCap gridVector D hD L :=
      mul_le_mul_of_nonneg_left hcapSum
        (le_trans (by norm_num) (one_le_fixedJohnTailParameter D hD))
    _ ≤ (Nat.ceil (fixedJohnTailParameter D hD *
        ∑ L : FixedJohnTest D hD,
          fixedJohnTranslationPaperCap gridVector D hD L) : Real) :=
      Nat.le_ceil _
    _ = (fixedJohnLoadThreshold gridVector D hD : Real) := rfl

/-- Direct finite-law selector.  It has no lattice realization, mean,
support callback, tail-room callback, or threshold callback. -/
theorem exists_translationTuple_normalizedConflictIndices_card_le_exactMean
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (hgrid : ∀ g, ‖gridVector g‖ ≤ 1) :
    ∃ omega : Fin (fixedJohnRepetitions gridVector D hD) → translation,
      (∀ K : FixedJohnTest D hD,
        (∑ j, (normalizedTranslationBodyLoadNat gridVector D
          (fixedJohnCatalogueBody hD) K (omega j) : Real)) ≤
          fixedJohnTailParameter D hD *
            fixedJohnTranslationPaperCap gridVector D hD K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion (gridVector (omega j))) D)
          a).card ≤ fixedJohnLoadThreshold gridVector D hD) := by
  let repetitions := fixedJohnRepetitions gridVector D hD
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
      (fun K _hK ↦ fixedJohnRepetitions_mul_mean_le_cap
        gridVector D hD K)
      (fixedJohnTailRoom D hD)
  have hunit : ∀ a : NormalizedRigidCandidate translation iota,
      (normalizedRigidCandidateTube
        (translationCandidateMotion gridVector) D a).carrier ⊆
          Metric.closedBall (0 : Space) 1 :=
    normalizedRigidCandidateTube_subset_unitBall_of_gridVector_norm_le_one
      gridVector D hD hgrid
  obtain ⟨cover, hcoverActive, hcoverCard, hcover⟩ :=
    exists_fixedJohn_normalizedConflict_bodyMultiCover
      (translationCandidateMotion gridVector) D hD hunit omega
  refine ⟨omega, ?_, ?_⟩
  · intro K
    simpa only [Finset.mem_univ, repetitions, mean, cap, A, productLoad] using
      htail K (Finset.mem_univ K)
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
            simpa only [Nat.cast_sum, repetitions, mean, cap, A, productLoad] using hreal
          exact_mod_cast hcast)
    simpa only [one_mul, repetitions] using hconf

#print axioms fixedJohnFiniteMean_nonneg
#print axioms sum_fixedJohnLoad_eq_card_mul_finiteMean
#print axioms fixedJohnLoad_le_paperCap
#print axioms fixedJohnFiniteMean_le_paperCap
#print axioms fixedJohnRepetitions_mul_mean_le_cap
#print axioms one_le_fixedJohnRepetitions
#print axioms fixedJohnTailRoom
#print axioms fixedJohn_threshold_le_loadThreshold
#print axioms
  exists_translationTuple_normalizedConflictIndices_card_le_exactMean

end
end Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
