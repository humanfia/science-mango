import Family8Grounding.Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperCommonPointElongatedBudgetV3

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3

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
open Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1
open Family8FiniteRandomRigidMotionPaperTransverseCoordinateAngleV1
open Family8FiniteRandomRigidMotionPaperCommonPointElongatedBudgetV3
open Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
open FamilyStickyLatticeMultiBoxPointCountV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Automatic elongated conflict tests on every admissible normalized scale

An admissible source radius is at most `1/2`; eighth-normalization therefore
has radius at most `1/16`.  The sharpened common-point budget uses the actual
`32 rho` angle estimate on that full range.  Consequently the former explicit
`delta / 8 <= 1/100` premise disappears from the automatic conflict producer.
-/

/-- A genuine volume conflict lies in the anchor tube's side-six elongated
body throughout the full normalized admissible radius range. -/
theorem carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
    {rho : NNReal} (T U : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hrhoPos : 0 < rho) (hrho : rho ≤ (1 / 16 : NNReal))
    (hconflict : ¬ EssentiallyDistinct T U) :
    U.carrier ⊆
      (Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1.paperElongatedBody
        T frame : Set Space) := by
  have hrhoHalf : rho ≤ (2 : NNReal)⁻¹ := by
    exact hrho.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) ≤ 16 by norm_num)))
  obtain ⟨x, hxT, hxU⟩ :=
    inter_carrier_nonempty_of_not_essentiallyDistinct
      T U hrhoPos hrhoHalf hconflict
  have hsin32 :
      Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) ≤
        32 * (rho : Real) :=
    sin_angle_le_thirtyTwo_mul_of_conflict_overlap_upper
      T U hrhoPos hrhoHalf hconflict
        (sin_angle_mul_volume_inter_toReal_le_eight_rho_cubed T U)
  apply carrier_subset_paperElongatedBody_of_commonPoint_thirtyTwo
    T U x frame hframe hrho hxT hxU
  intro k hk
  exact (abs_inner_frame_le_sin_angle_of_ne_two
    frame T.axis.direction U.axis.direction hframe
      T.axis.norm_direction U.axis.norm_direction k hk).trans hsin32

/-- The admissibility bound automatically supplies the normalized scale
needed by the fixed elongated candidate catalogue. -/
theorem normalizedConflictContainedInElongatedCandidate
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible) :
    NormalizedConflictContainedInElongatedCandidate motion D := by
  intro a b hab
  let T := normalizedRigidCandidateTube motion D a
  let U := normalizedRigidCandidateTube motion D b
  have hrhoPos : 0 < delta / 8 := div_pos hD.delta_pos (by norm_num)
  have hrho : delta / 8 ≤ (1 / 16 : NNReal) := by
    rw [← NNReal.coe_le_coe]
    have hreal' : (delta : Real) ≤ (((2 : NNReal)⁻¹ : NNReal) : Real) :=
      NNReal.coe_le_coe.mpr hD.delta_le_half
    have hreal : (delta : Real) ≤ (1 / 2 : Real) := by
      simpa using hreal'
    push_cast
    linarith
  have hconflict : ¬ EssentiallyDistinct T U := by
    intro hTU
    exact hab ((essentiallyDistinct_comm T U).mp hTU)
  exact carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
    T U (normalizedRigidCandidateAlignedFrame motion D a)
    (normalizedRigidCandidateAlignedFrame_two motion D a)
    hrhoPos hrho hconflict

/-- The singleton candidate catalogue supplies the complete body multi-cover
without any additional small-scale premise. -/
theorem exists_canonical_normalizedConflict_bodyMultiCover_automatic
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
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
    (normalizedConflictContainedInElongatedCandidate motion D hD)
    omega

/-- Fully automatic conflict-cap producer for every admissible normalized
datum.  Only the honest lattice realization and explicit mean, Chernoff-room,
and threshold budgets remain. -/
theorem exists_translationTuple_normalizedConflictIndices_card_le_automatic
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
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
          (translationCandidateMotion gridVector) D hD omega)
  simpa only [Finset.mem_univ, true_implies, one_mul,
    translationCandidateElongatedPaperCap,
    translationCandidateMotion] using h

#print axioms carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
#print axioms normalizedConflictContainedInElongatedCandidate
#print axioms exists_canonical_normalizedConflict_bodyMultiCover_automatic
#print axioms exists_translationTuple_normalizedConflictIndices_card_le_automatic

end
end Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3
