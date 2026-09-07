import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
open Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1

noncomputable section

/-!
# Scale-only elongated conflict projection

This module keeps the conflict projection independent of admissibility and
of the particular finite rigid-motion law.  It converts uniform arbitrary-body
loads into conflict-neighbourhood cardinality bounds, and supplies the
singleton elongated candidate cover from only the two normalized scale
hypotheses used by the geometry.
-/

/-- Product occurrences contained in one arbitrary convex test after the
common eighth normalization and an arbitrary rigid motion. -/
def normalizedRigidBodyIndices
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testBody : testIndex → ConvexBody Space)
    (omega : Fin repetitions → motionChoice)
    (K : testIndex) : Finset (Fin repetitions × iota) := by
  classical
  exact Finset.univ.filter fun b ↦
    (eighthNormalizedTube
      (rigidTube (motion (omega b.1)) (D.family.tubes b.2))).carrier ⊆
        (testBody K : Set Space)

/-- Exact splitting of an arbitrary rigid-motion body containment count by
the repetition coordinate. -/
theorem normalizedRigidBodyIndices_card_eq_sum_load
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testBody : testIndex → ConvexBody Space)
    (omega : Fin repetitions → motionChoice)
    (K : testIndex) :
    (normalizedRigidBodyIndices motion D testBody omega K).card =
      ∑ j, normalizedRigidBodyLoadNat motion D testBody K (omega j) := by
  classical
  unfold normalizedRigidBodyIndices normalizedRigidBodyLoadNat
  rw [Finset.card_eq_sum_ones]
  rw [← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A bounded multi-cover by arbitrary convex bodies projects uniform
rigid-motion body loads to the corresponding conflict-cardinality bound. -/
theorem normalizedConflictIndices_card_le_of_bodyMultiCover
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    [DecidableEq testIndex]
    {delta : NNReal} {repetitions : Nat}
    {coverMultiplicity loadThreshold : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testBody : testIndex → ConvexBody Space)
    (activeTests : Finset testIndex)
    (omega : Fin repetitions → motionChoice)
    (cover : Fin repetitions × iota → Finset testIndex)
    (hcoverActive : ∀ a, cover a ⊆ activeTests)
    (hcoverCard : ∀ a, (cover a).card ≤ coverMultiplicity)
    (hcover : ∀ a b,
      normalizedConflict
          (indexedRigidCopyDatum (fun j ↦ motion (omega j)) D) b a →
        ∃ K, K ∈ cover a ∧
          (eighthNormalizedTube
            (rigidTube (motion (omega b.1))
              (D.family.tubes b.2))).carrier ⊆
            (testBody K : Set Space))
    (hload : ∀ K, K ∈ activeTests →
      (∑ j, normalizedRigidBodyLoadNat
        motion D testBody K (omega j)) ≤ loadThreshold) :
    ∀ a,
      (normalizedConflictIndices
        (indexedRigidCopyDatum (fun j ↦ motion (omega j)) D) a).card ≤
          coverMultiplicity * loadThreshold := by
  classical
  intro a
  have hsubset :
      normalizedConflictIndices
          (indexedRigidCopyDatum (fun j ↦ motion (omega j)) D) a ⊆
        (cover a).biUnion fun K ↦
          normalizedRigidBodyIndices motion D testBody omega K := by
    intro b hb
    rw [normalizedConflictIndices, Finset.mem_filter] at hb
    obtain ⟨K, hK, hcontain⟩ := hcover a b hb.2
    apply Finset.mem_biUnion.mpr
    refine ⟨K, hK, ?_⟩
    rw [normalizedRigidBodyIndices, Finset.mem_filter]
    exact ⟨Finset.mem_univ b, hcontain⟩
  calc
    (normalizedConflictIndices
        (indexedRigidCopyDatum (fun j ↦ motion (omega j)) D) a).card ≤
        ((cover a).biUnion fun K ↦
          normalizedRigidBodyIndices motion D testBody omega K).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ K ∈ cover a,
        (normalizedRigidBodyIndices motion D testBody omega K).card :=
      Finset.card_biUnion_le
    _ = ∑ K ∈ cover a,
        ∑ j, normalizedRigidBodyLoadNat
          motion D testBody K (omega j) := by
      apply Finset.sum_congr rfl
      intro K _hK
      exact normalizedRigidBodyIndices_card_eq_sum_load
        motion D testBody omega K
    _ ≤ ∑ _K ∈ cover a, loadThreshold := by
      apply Finset.sum_le_sum
      intro K hK
      exact hload K (hcoverActive a hK)
    _ = (cover a).card * loadThreshold := by simp
    _ ≤ coverMultiplicity * loadThreshold :=
      Nat.mul_le_mul_right loadThreshold (hcoverCard a)

/-- Positivity and the paper half-scale bound alone imply the local
elongated-candidate containment needed by the canonical cover. -/
theorem normalizedConflictContainedInElongatedCandidate
    {motionChoice iota : Type}
    [Fintype motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    NormalizedConflictContainedInElongatedCandidate motion D := by
  intro a b hab
  let T := normalizedRigidCandidateTube motion D a
  let U := normalizedRigidCandidateTube motion D b
  have hrhoPos : 0 < delta / 8 := div_pos hdelta (by norm_num)
  have hrho : delta / 8 ≤ (1 / 16 : NNReal) := by
    rw [← NNReal.coe_le_coe]
    have hreal' :
        (delta : Real) ≤ (((2 : NNReal)⁻¹ : NNReal) : Real) :=
      NNReal.coe_le_coe.mpr hdeltaHalf
    have hreal : (delta : Real) ≤ (1 / 2 : Real) := by
      simpa using hreal'
    push_cast
    linarith
  have hconflict : ¬ EssentiallyDistinct T U := by
    intro hTU
    exact hab ((essentiallyDistinct_comm T U).mp hTU)
  exact
    Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3.carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
        T U (normalizedRigidCandidateAlignedFrame motion D a)
        (normalizedRigidCandidateAlignedFrame_two motion D a)
        hrhoPos hrho hconflict

/-- The fixed candidate catalogue gives a singleton conflict cover from the
two raw scale hypotheses, with no admissibility package. -/
theorem exists_canonical_normalizedConflict_bodyMultiCover
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
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
  exact
    Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1.exists_canonical_normalizedConflict_bodyMultiCover
        motion D
        (normalizedConflictContainedInElongatedCandidate
          motion D hdelta hdeltaHalf)
        omega

/-- Uniform loads for the fixed elongated candidate catalogue are exactly
the selector seam needed to bound every normalized conflict neighbourhood. -/
theorem normalizedConflictIndices_card_le_of_candidateElongatedBodyLoads
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions loadThreshold : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (omega : Fin repetitions → motionChoice)
    (hload : ∀ K : Fin (Fintype.card
        (NormalizedRigidCandidate motionChoice iota)),
      (∑ j, normalizedRigidBodyLoadNat motion D
        (normalizedRigidCandidateElongatedBody motion D) K (omega j)) ≤
          loadThreshold) :
    ∀ a,
      (normalizedConflictIndices
        (indexedRigidCopyDatum (fun j ↦ motion (omega j)) D) a).card ≤
          loadThreshold := by
  obtain ⟨cover, hcoverActive, hcoverCard, hcover⟩ :=
    exists_canonical_normalizedConflict_bodyMultiCover
      motion D hdelta hdeltaHalf omega
  have h := normalizedConflictIndices_card_le_of_bodyMultiCover
    motion D (normalizedRigidCandidateElongatedBody motion D)
    Finset.univ omega cover hcoverActive hcoverCard hcover
    (fun K _hK ↦ hload K)
  simpa only [one_mul] using h

#print axioms normalizedRigidBodyIndices_card_eq_sum_load
#print axioms normalizedConflictIndices_card_le_of_bodyMultiCover
#print axioms normalizedConflictContainedInElongatedCandidate
#print axioms exists_canonical_normalizedConflict_bodyMultiCover
#print axioms normalizedConflictIndices_card_le_of_candidateElongatedBodyLoads

end
end Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1
