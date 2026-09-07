import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnDensityBudgetSelectorV2

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

/-! Branch-free selector using the desired integer repetition count itself.
The explicit density budget controls the exact mean in every case, including
when every exact mean is zero; no positive-mean premise is exposed. -/

theorem exists_boundedPackingTuple_of_densityBudget
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (J : Nat)
    (hbudget :
      9504 * (J : Real) * (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) <=
        (fixedJohnPackingMaximalConcentration D hD).toReal) :
    ∃ omega : Fin J → FixedJohnPackingTranslation D hD,
      (∀ K : FixedJohnTest D hD,
        (∑ j, (normalizedTranslationBodyLoadNat
          (fixedJohnPackingGridVector D hD) D
          (fixedJohnCatalogueBody hD) K (omega j) : Real)) <=
          fixedJohnTailParameter D hD *
            fixedJohnTranslationPaperCap
              (fixedJohnPackingGridVector D hD) D hD K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D)
          a).card <=
            fixedJohnLoadThreshold
              (fixedJohnPackingGridVector D hD) D hD) := by
  let gridVector := fixedJohnPackingGridVector D hD
  let mean : FixedJohnTest D hD → Real :=
    fixedJohnFiniteMean gridVector D hD
  let cap : FixedJohnTest D hD → Real :=
    fixedJohnTranslationPaperCap gridVector D hD
  let A := fixedJohnTailParameter D hD
  have hscale (K : FixedJohnTest D hD) :
      (J : Real) * mean K <= cap K := by
    calc
      (J : Real) * mean K <=
          (J : Real) * fixedJohnLongPackingMean D hD K :=
        mul_le_mul_of_nonneg_left
          (by simpa only [mean, gridVector] using
            fixedJohnPackingFiniteMean_le_longPackingMean D hD K)
          (Nat.cast_nonneg J)
      _ <= cap K := by
        simpa only [cap, gridVector] using
          fixedJohnLongPackingMean_scale_le_paperCap_of_densityBudget
            D hD J hbudget K
  obtain ⟨omega, htail⟩ :=
    exists_product_choice_load_le_A_mul_cap
      (Finset.univ : Finset (FixedJohnTest D hD)) J
      (fun K g ↦ (normalizedTranslationBodyLoadNat gridVector D
        (fixedJohnCatalogueBody hD) K g : Real)) cap mean A
      (fun K _hK ↦ fixedJohnPaperCap_nonneg gridVector D hD K)
      (fun K _hK ↦ fixedJohnFiniteMean_nonneg gridVector D hD K)
      (fun _K _hK _g ↦ Nat.cast_nonneg _)
      (fun K _hK g ↦ fixedJohnLoad_le_paperCap gridVector D hD K g)
      (fun K _hK ↦ by
        exact (sum_fixedJohnLoad_eq_card_mul_finiteMean
          gridVector D hD K).le)
      (fun K _hK ↦ hscale K)
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
    simpa only [Finset.mem_univ, gridVector, mean, cap, A,
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
                (fixedJohnCatalogueBody hD) K (omega j) : Nat) : Real) <=
                (fixedJohnLoadThreshold gridVector D hD : Real) := by
            simpa only [Nat.cast_sum, mean, cap, A, productLoad] using hreal
          exact_mod_cast hcast)
    simpa only [one_mul, gridVector] using hconf

#print axioms exists_boundedPackingTuple_of_densityBudget

end
end Family8FiniteRandomRigidMotionPaperFixedJohnDensityBudgetSelectorV2
