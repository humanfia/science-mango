import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossSourceExponentV4
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FixedJohnMaxThresholdGreedyLossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
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
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPolynomialV3
open Family8FiniteRandomRigidMotionPaperFixedJohnSourceKTBudgetV5
open Family8FiniteRandomRigidMotionPaperFixedJohnTailPowerV2
open FamilyStickyRandomTestDependentChernoffV1
open FamilyStickyRandomFiniteChernoffV3

noncomputable section

/-!
# Maximum-threshold fixed-John greedy loss

The old automatic threshold is the logarithmic tail parameter times the sum
of all test-dependent paper caps.  The selector only requires a common upper
bound for each individual cap.  Folding with `max`, starting at zero, gives
such a bound without paying the degree-fifteen catalogue cardinality.
-/

def fixedJohnMaxPaperCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Real :=
  (Finset.univ : Finset (FixedJohnTest D hD)).fold max 0 fun K ↦
    fixedJohnTranslationPaperCap gridVector D hD K

theorem fixedJohnPaperCap_le_maxPaperCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnTranslationPaperCap gridVector D hD K ≤
      fixedJohnMaxPaperCap gridVector D hD := by
  unfold fixedJohnMaxPaperCap
  rw [Finset.le_fold_max]
  exact Or.inr ⟨K, Finset.mem_univ K, le_rfl⟩

theorem fixedJohnMaxPaperCap_nonneg
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    0 ≤ fixedJohnMaxPaperCap gridVector D hD := by
  unfold fixedJohnMaxPaperCap
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

def fixedJohnMaxLoadThreshold
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Nat :=
  Nat.ceil (fixedJohnTailParameter D hD *
    fixedJohnMaxPaperCap gridVector D hD)

theorem fixedJohn_threshold_le_maxLoadThreshold
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnTailParameter D hD *
        fixedJohnTranslationPaperCap gridVector D hD K ≤
      (fixedJohnMaxLoadThreshold gridVector D hD : Real) := by
  calc
    fixedJohnTailParameter D hD *
          fixedJohnTranslationPaperCap gridVector D hD K ≤
        fixedJohnTailParameter D hD *
          fixedJohnMaxPaperCap gridVector D hD := by
      gcongr
      exact zero_le_one.trans (one_le_fixedJohnTailParameter D hD)
      exact fixedJohnPaperCap_le_maxPaperCap gridVector D hD K
    _ ≤ (Nat.ceil (fixedJohnTailParameter D hD *
          fixedJohnMaxPaperCap gridVector D hD) : Real) :=
      Nat.le_ceil _
    _ = (fixedJohnMaxLoadThreshold gridVector D hD : Real) := rfl

/-- The exact-mean selector remains valid with the maximum threshold. -/
theorem exists_translationTuple_normalizedConflictIndices_card_le_maxThreshold
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
          a).card ≤ fixedJohnMaxLoadThreshold gridVector D hD) := by
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
        (loadThreshold := fixedJohnMaxLoadThreshold gridVector D hD)
        gridVector D (fixedJohnCatalogueBody hD) Finset.univ omega cover
        hcoverActive hcoverCard hcover (fun K _hK ↦ by
          have hreal :=
            (htail K (Finset.mem_univ K)).trans
              (fixedJohn_threshold_le_maxLoadThreshold gridVector D hD K)
          have hcast :
              ((∑ j, normalizedTranslationBodyLoadNat gridVector D
                (fixedJohnCatalogueBody hD) K (omega j) : Nat) : Real) ≤
                (fixedJohnMaxLoadThreshold gridVector D hD : Real) := by
            simpa only [Nat.cast_sum, repetitions, mean, cap, A, productLoad]
              using hreal
          exact_mod_cast hcast)
    simpa only [one_mul, repetitions] using hconf

def fixedJohnMaxAutomaticGreedyLoss
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Nat :=
  fixedJohnMaxLoadThreshold (fixedJohnPackingGridVector D hD) D hD + 1

theorem fixedJohnMaxAutomaticGreedyLoss_cast_le_envelope
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnTailParameter D hD *
          fixedJohnMaxPaperCap (fixedJohnPackingGridVector D hD) D hD +
        2 := by
  let x : Real := fixedJohnTailParameter D hD *
    fixedJohnMaxPaperCap (fixedJohnPackingGridVector D hD) D hD
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg
      (zero_le_one.trans (one_le_fixedJohnTailParameter D hD))
      (fixedJohnMaxPaperCap_nonneg _ D hD)
  have hceil : (fixedJohnMaxLoadThreshold
      (fixedJohnPackingGridVector D hD) D hD : Real) < x + 1 := by
    simpa only [fixedJohnMaxLoadThreshold, x] using
      Nat.ceil_lt_add_one hx
  unfold fixedJohnMaxAutomaticGreedyLoss
  push_cast
  dsimp only [x] at hceil ⊢
  linarith

#print axioms fixedJohnPaperCap_le_maxPaperCap
#print axioms fixedJohnMaxPaperCap_nonneg
#print axioms fixedJohn_threshold_le_maxLoadThreshold
#print axioms
  exists_translationTuple_normalizedConflictIndices_card_le_maxThreshold
#print axioms fixedJohnMaxAutomaticGreedyLoss_cast_le_envelope

end
end Family8FixedJohnMaxThresholdGreedyLossV1
