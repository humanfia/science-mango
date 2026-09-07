import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
import Family8Grounding.Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8PolynomialJohnFrameBoxTestNetV1
open FamilyStickyLatticeMultiBoxPointCountV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Fixed-John automatic conflict cap

This connector feeds the motion-independent polynomial John catalogue into
the honest BodyGrid/Chernoff selector.  The test type and product lattice
depend only on the normalized radius.  Remaining premises are literal B1
support and explicit lattice/mean/tail budgets.
-/

theorem admissibleNormalizedRadiusPos
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota} (hD : D.IsAdmissible) :
    0 < delta / 8 :=
  div_pos hD.delta_pos (by norm_num)

def fixedJohnCatalogueBody
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota} (hD : D.IsAdmissible) :
    Fin (Fintype.card
      (CatalogueIndex (delta / 8) (admissibleNormalizedRadiusPos hD))) →
      ConvexBody Space :=
  normalizedJohnCatalogueBody (delta / 8)
    (admissibleNormalizedRadiusPos hD)

def fixedJohnTranslationPaperCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : Fin (Fintype.card
      (CatalogueIndex (delta / 8) (admissibleNormalizedRadiusPos hD)))) :
      Real :=
  normalizedTranslationBodyPaperCap gridVector D
    (fixedJohnCatalogueBody hD) Finset.univ K

/-- Fixed-catalogue conflict cap with multiplicity one. -/
theorem exists_translationTuple_normalizedConflictIndices_card_le_fixedJohn
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (hunit : ∀ a : NormalizedRigidCandidate translation iota,
      (normalizedRigidCandidateTube
        (translationCandidateMotion gridVector) D a).carrier ⊆
          Metric.closedBall (0 : Space) 1)
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
  have h :=
    exists_translationTuple_normalizedConflictIndices_card_le_of_bodyLatticeMultiCover
      gridVector D hD (fixedJohnCatalogueBody hD) Finset.univ L R
      repetitions 1 loadThreshold mean A
      (fun K _hK ↦ hmean K)
      (fun K _hK ↦ hlocal K)
      (fun K _hK ↦ hscale K)
      htailRoom
      (fun K _hK ↦ hthreshold K)
      (fun omega ↦ by
        simpa only [fixedJohnCatalogueBody,
          admissibleNormalizedRadiusPos, translationCandidateMotion] using
          exists_fixedJohn_normalizedConflict_bodyMultiCover
            (translationCandidateMotion gridVector) D hD hunit omega)
  simpa only [Finset.mem_univ, true_implies, one_mul,
    fixedJohnTranslationPaperCap] using h

#print axioms admissibleNormalizedRadiusPos
#print axioms fixedJohnCatalogueBody
#print axioms fixedJohnTranslationPaperCap
#print axioms
  exists_translationTuple_normalizedConflictIndices_card_le_fixedJohn

end
end Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
