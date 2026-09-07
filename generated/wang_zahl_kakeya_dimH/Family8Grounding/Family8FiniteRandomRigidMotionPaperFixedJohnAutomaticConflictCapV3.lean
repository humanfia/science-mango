import Family8Grounding.Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1
open Family8PolynomialJohnFrameBoxTestNetV1
open FamilyStickyLatticeMultiBoxPointCountV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Fixed-John conflict cap with automatic motion support

The public premise is now the genuine finite-law condition
`forall g, norm (gridVector g) <= 1`.  Source admissibility and the formal B2
normalization automatically produce the B1 support required by the fixed
John catalogue; no support callback remains.
-/

theorem exists_translationTuple_normalizedConflictIndices_card_le_fixedJohn
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (hgrid : ∀ g, ‖gridVector g‖ ≤ 1)
    (L : MultiBoxLattice
      (Fin (Fintype.card
        (CatalogueIndex (delta / 8) (admissibleNormalizedRadiusPos hD)))))
    (R :
      FamilyStickyActualLatticePointBalanceV1.ActualTubeTranslationGrid.IsMultiBoxLatticeRealization
        (normalizedTranslationBodyGrid gridVector D
          (fixedJohnCatalogueBody hD) Finset.univ) L)
    (repetitions loadThreshold : Nat)
    (mean : Fin (Fintype.card
      (CatalogueIndex (delta / 8) (admissibleNormalizedRadiusPos hD))) →
        Real)
    (A : Real)
    (hmean : ∀ K, 0 ≤ mean K)
    (hlocal : ∀ K,
      (Fintype.card iota : Real) ≤
        (Fintype.card (L.Block K) : Real) * mean K)
    (hscale : ∀ K,
      (repetitions : Real) * mean K ≤
        fixedJohnTranslationPaperCap gridVector D hD K)
    (htailRoom :
      ((Finset.univ : Finset (Fin (Fintype.card
          (CatalogueIndex (delta / 8)
            (admissibleNormalizedRadiusPos hD))))).card : Real) *
          Real.exp (Real.exp 1 - 1) < Real.exp A)
    (hthreshold : ∀ K,
      A * fixedJohnTranslationPaperCap gridVector D hD K ≤
        (loadThreshold : Real)) :
    ∃ omega : Fin repetitions → translation,
      (∀ K,
        (∑ j, (normalizedTranslationBodyLoadNat gridVector D
          (fixedJohnCatalogueBody hD) K (omega j) : Real)) ≤
          A * fixedJohnTranslationPaperCap gridVector D hD K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion (gridVector (omega j))) D)
          a).card ≤ loadThreshold) := by
  exact
    Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2.exists_translationTuple_normalizedConflictIndices_card_le_fixedJohn
      gridVector D hD
      (normalizedRigidCandidateTube_subset_unitBall_of_gridVector_norm_le_one
        gridVector D hD hgrid)
      L R repetitions loadThreshold mean A hmean hlocal hscale htailRoom
      hthreshold

#print axioms
  exists_translationTuple_normalizedConflictIndices_card_le_fixedJohn

end
end Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV3
