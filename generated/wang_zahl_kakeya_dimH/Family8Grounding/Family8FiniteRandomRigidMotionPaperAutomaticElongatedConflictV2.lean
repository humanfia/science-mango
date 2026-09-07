import Family8Grounding.Family8FiniteRandomRigidMotionPaperTubeOverlapUpperV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictAngleAlgebraV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictToElongatedViaAngleV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperTubeOverlapUpperV1
open Family8FiniteRandomRigidMotionPaperConflictAngleAlgebraV1
open Family8FiniteRandomRigidMotionPaperConflictToElongatedViaAngleV1
open Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open FamilyStickyLatticeMultiBoxPointCountV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Automatic elongated conflict tests

The exact three-slab overlap estimate closes the angular premise of the
side-six elongated containment theorem.  For normalized rigid candidates,
the fixed candidate catalogue therefore supplies the singleton multi-cover
automatically.  The final theorem feeds that cover into the honest finite
translation BodyGrid producer; only the actual lattice realization and its
explicit mean/tail/threshold budgets remain as hypotheses.
-/

/-- A genuine volume conflict automatically lies in the anchor tube's
side-six elongated test body. -/
theorem carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
    {rho : NNReal} (T U : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hrhoPos : 0 < rho) (hrho : rho ≤ (1 / 100 : NNReal))
    (hconflict : ¬ EssentiallyDistinct T U) :
    U.carrier ⊆
      (Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1.paperElongatedBody
        T frame : Set Space) := by
  have hrhoHalf : rho ≤ (2 : NNReal)⁻¹ := by
    exact hrho.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) ≤ 100 by norm_num)))
  have hsin32 :
      Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) ≤
        32 * (rho : Real) :=
    sin_angle_le_thirtyTwo_mul_of_conflict_overlap_upper
      T U hrhoPos hrhoHalf hconflict
        (sin_angle_mul_volume_inter_toReal_le_eight_rho_cubed T U)
  apply
    carrier_subset_paperElongatedBody_of_not_essentiallyDistinct_of_sin_le
      T U frame hframe hrhoPos hrho hconflict
  exact hsin32.trans (by
    have hrhoNonneg : 0 ≤ (rho : Real) := NNReal.zero_le_coe
    nlinarith)

/-- At a normalized radius at most `1/100`, the local geometric callback in
the candidate-grid module is a theorem rather than an input. -/
theorem normalizedConflictContainedInElongatedCandidate
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hsmall : delta / 8 ≤ (1 / 100 : NNReal)) :
    NormalizedConflictContainedInElongatedCandidate motion D := by
  intro a b hab
  let T := normalizedRigidCandidateTube motion D a
  let U := normalizedRigidCandidateTube motion D b
  have hrhoPos : 0 < delta / 8 := div_pos hdeltaPos (by norm_num)
  have hconflict : ¬ EssentiallyDistinct T U := by
    intro hTU
    exact hab ((essentiallyDistinct_comm T U).mp hTU)
  exact carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
    T U (normalizedRigidCandidateAlignedFrame motion D a)
    (normalizedRigidCandidateAlignedFrame_two motion D a)
    hrhoPos hsmall hconflict

/-- The singleton candidate catalogue automatically supplies the complete
body multi-cover with multiplicity one. -/
theorem exists_canonical_normalizedConflict_bodyMultiCover_automatic
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hsmall : delta / 8 ≤ (1 / 100 : NNReal))
    (omega : Fin repetitions → motionChoice) :
    ∃ cover : Fin repetitions × iota →
        Finset (Fin (Fintype.card
          (NormalizedRigidCandidate motionChoice iota))),
      (∀ a, cover a ⊆ Finset.univ) ∧
      (∀ a, (cover a).card ≤ 1) ∧
      (∀ a b,
        normalizedConflict
            (indexedRigidCopyDatum (fun j ↦ motion (omega j)) D) b a →
          ∃ K, K ∈ cover a ∧
            (eighthNormalizedTube
              (rigidTube (motion (omega b.1))
                (D.family.tubes b.2))).carrier ⊆
              (normalizedRigidCandidateElongatedBody motion D K :
                Set Space)) := by
  exact exists_canonical_normalizedConflict_bodyMultiCover
    motion D
    (normalizedConflictContainedInElongatedCandidate
      motion D hdeltaPos hsmall)
    omega

/-- Translation candidates use their literal translation rigid motions. -/
def translationCandidateMotion
    {translation : Type} (gridVector : translation → Space) :
    translation → RigidMotion := fun g ↦ translationRigidMotion (gridVector g)

/-- Fixed elongated test body for every translation/source candidate. -/
def translationCandidateElongatedBody
    {translation iota : Type}
    [Fintype translation] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) :
    Fin (Fintype.card (NormalizedRigidCandidate translation iota)) →
      ConvexBody Space :=
  normalizedRigidCandidateElongatedBody
    (translationCandidateMotion gridVector) D

/-- BodyGrid's automatic cap specialized to the fixed elongated catalogue. -/
def translationCandidateElongatedPaperCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota)
    (K : Fin (Fintype.card
      (NormalizedRigidCandidate translation iota))) : Real :=
  normalizedTranslationBodyPaperCap gridVector D
    (translationCandidateElongatedBody gridVector D) Finset.univ K

/-- Fully automatic conflict-cap producer for the fixed elongated catalogue.
The remaining hypotheses are precisely the pre-selection lattice, mean,
Chernoff room and numeric threshold budgets. -/
theorem exists_translationTuple_normalizedConflictIndices_card_le_automatic
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (hsmall : delta / 8 ≤ (1 / 100 : NNReal))
    (L : MultiBoxLattice
      (Fin (Fintype.card (NormalizedRigidCandidate translation iota))))
    (R :
      FamilyStickyActualLatticePointBalanceV1.ActualTubeTranslationGrid.IsMultiBoxLatticeRealization
        (normalizedTranslationBodyGrid gridVector D
          (translationCandidateElongatedBody gridVector D) Finset.univ) L)
    (repetitions loadThreshold : Nat)
    (mean : Fin (Fintype.card
      (NormalizedRigidCandidate translation iota)) → Real)
    (A : Real)
    (hmean : ∀ K, 0 ≤ mean K)
    (hlocal : ∀ K,
      (Fintype.card iota : Real) ≤
        (Fintype.card (L.Block K) : Real) * mean K)
    (hscale : ∀ K,
      (repetitions : Real) * mean K ≤
        translationCandidateElongatedPaperCap gridVector D K)
    (htailRoom :
      ((Finset.univ : Finset (Fin (Fintype.card
          (NormalizedRigidCandidate translation iota)))).card : Real) *
          Real.exp (Real.exp 1 - 1) < Real.exp A)
    (hthreshold : ∀ K,
      A * translationCandidateElongatedPaperCap gridVector D K ≤
        (loadThreshold : Real)) :
    ∃ omega : Fin repetitions → translation,
      (∀ K,
        (∑ j, (normalizedTranslationBodyLoadNat gridVector D
          (translationCandidateElongatedBody gridVector D) K
          (omega j) : Real)) ≤
          A * translationCandidateElongatedPaperCap gridVector D K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion (gridVector (omega j))) D)
          a).card ≤ loadThreshold) := by
  have h :=
    exists_translationTuple_normalizedConflictIndices_card_le_of_bodyLatticeMultiCover
      gridVector D hD
      (translationCandidateElongatedBody gridVector D)
      Finset.univ L R repetitions 1 loadThreshold mean A
      (fun K _hK ↦ hmean K)
      (fun K _hK ↦ hlocal K)
      (fun K _hK ↦ hscale K)
      htailRoom
      (fun K _hK ↦ hthreshold K)
      (fun omega ↦
        exists_canonical_normalizedConflict_bodyMultiCover_automatic
          (translationCandidateMotion gridVector) D hD.delta_pos hsmall omega)
  simpa only [Finset.mem_univ, true_implies, one_mul,
    translationCandidateElongatedPaperCap,
    translationCandidateMotion] using h

#print axioms carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
#print axioms normalizedConflictContainedInElongatedCandidate
#print axioms exists_canonical_normalizedConflict_bodyMultiCover_automatic
#print axioms exists_translationTuple_normalizedConflictIndices_card_le_automatic

end
end Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
