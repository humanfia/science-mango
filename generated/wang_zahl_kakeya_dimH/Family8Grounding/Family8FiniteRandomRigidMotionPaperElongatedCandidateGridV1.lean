import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1

noncomputable section

/-!
# Fixed finite catalogue of honest elongated tests

Every possible moved normalized source tube in the finite motion law supplies
one elongated test body.  This catalogue is fixed before the random tuple is
chosen.  A selected occurrence is covered by the singleton test indexed by
its own motion/source pair, so all finite multi-cover bookkeeping has literal
multiplicity one.  The only remaining input is the local geometric statement
that a non-essentially-distinct candidate fits in the anchor candidate's
elongated body.
-/

def normalizedRigidCandidateEquivFin
    (motionChoice iota : Type) [Fintype motionChoice] [Fintype iota] :
    NormalizedRigidCandidate motionChoice iota ≃
      Fin (Fintype.card (NormalizedRigidCandidate motionChoice iota)) :=
  Fintype.equivFin _

def normalizedRigidCandidateIndex
    {motionChoice iota : Type} [Fintype motionChoice] [Fintype iota]
    (a : NormalizedRigidCandidate motionChoice iota) :
    Fin (Fintype.card (NormalizedRigidCandidate motionChoice iota)) :=
  normalizedRigidCandidateEquivFin motionChoice iota a

def normalizedRigidCandidateOfIndex
    {motionChoice iota : Type} [Fintype motionChoice] [Fintype iota]
    (K : Fin (Fintype.card (NormalizedRigidCandidate motionChoice iota))) :
    NormalizedRigidCandidate motionChoice iota :=
  (normalizedRigidCandidateEquivFin motionChoice iota).symm K

@[simp] theorem normalizedRigidCandidateOfIndex_index
    {motionChoice iota : Type} [Fintype motionChoice] [Fintype iota]
    (a : NormalizedRigidCandidate motionChoice iota) :
    normalizedRigidCandidateOfIndex (normalizedRigidCandidateIndex a) = a := by
  simp [normalizedRigidCandidateOfIndex, normalizedRigidCandidateIndex,
    normalizedRigidCandidateEquivFin]

/-- Chosen orthonormal frame whose last vector is the candidate tube axis. -/
def normalizedRigidCandidateAlignedFrame
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (a : NormalizedRigidCandidate motionChoice iota) :
    OrthonormalBasis (Fin 3) Real Space :=
  Classical.choose (normalizedRigidCandidateTube motion D a).exists_alignedFrame

theorem normalizedRigidCandidateAlignedFrame_two
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (a : NormalizedRigidCandidate motionChoice iota) :
    normalizedRigidCandidateAlignedFrame motion D a 2 =
      (normalizedRigidCandidateTube motion D a).axis.direction :=
  Classical.choose_spec
    (normalizedRigidCandidateTube motion D a).exists_alignedFrame

/-- The actual fixed convex test catalogue. -/
def normalizedRigidCandidateElongatedBody
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (K : Fin (Fintype.card (NormalizedRigidCandidate motionChoice iota))) :
    ConvexBody Space :=
  let a := normalizedRigidCandidateOfIndex K
  paperElongatedBody (normalizedRigidCandidateTube motion D a)
    (normalizedRigidCandidateAlignedFrame motion D a)

@[simp] theorem normalizedRigidCandidateElongatedBody_index
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (a : NormalizedRigidCandidate motionChoice iota) :
    normalizedRigidCandidateElongatedBody motion D
        (normalizedRigidCandidateIndex a) =
      paperElongatedBody (normalizedRigidCandidateTube motion D a)
        (normalizedRigidCandidateAlignedFrame motion D a) := by
  simp [normalizedRigidCandidateElongatedBody]

/-- Exact local geometry still required by the fixed catalogue. -/
def NormalizedConflictContainedInElongatedCandidate
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota) : Prop :=
  ∀ a b : NormalizedRigidCandidate motionChoice iota,
    ¬ EssentiallyDistinct
        (normalizedRigidCandidateTube motion D b)
        (normalizedRigidCandidateTube motion D a) →
      (normalizedRigidCandidateTube motion D b).carrier ⊆
        (paperElongatedBody
          (normalizedRigidCandidateTube motion D a)
          (normalizedRigidCandidateAlignedFrame motion D a) : Set Space)

/-- Scalar version of the local geometric input. -/
def NormalizedConflictHasElongatedCoordinateBudget
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota) : Prop :=
  ∀ a b : NormalizedRigidCandidate motionChoice iota,
    ¬ EssentiallyDistinct
        (normalizedRigidCandidateTube motion D b)
        (normalizedRigidCandidateTube motion D a) →
      ∀ k : Fin 3,
        ((delta / 8 : NNReal) : Real) +
            |⟪normalizedRigidCandidateAlignedFrame motion D a k,
              tubeAxisMidpoint (normalizedRigidCandidateTube motion D b) -
                tubeAxisMidpoint (normalizedRigidCandidateTube motion D a)⟫_ℝ| +
            (2 : Real)⁻¹ *
              |⟪normalizedRigidCandidateAlignedFrame motion D a k,
                (normalizedRigidCandidateTube motion D b).axis.direction⟫_ℝ| ≤
          ((paperElongatedSides (delta / 8) k : NNReal) : Real) / 2

theorem NormalizedConflictHasElongatedCoordinateBudget.toContained
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    {motion : motionChoice → RigidMotion}
    {D : ActualTubeDatum delta iota}
    (h : NormalizedConflictHasElongatedCoordinateBudget motion D) :
    NormalizedConflictContainedInElongatedCandidate motion D := by
  intro a b hab
  exact carrier_subset_paperElongatedBody_of_midpointDirectionBudget
    (normalizedRigidCandidateTube motion D a)
    (normalizedRigidCandidateTube motion D b)
    (normalizedRigidCandidateAlignedFrame motion D a)
    (h a b hab)

/-- Singleton canonical covers solve the full body-grid multi-cover premise
with multiplicity one. -/
theorem exists_canonical_normalizedConflict_bodyMultiCover
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hgeometry : NormalizedConflictContainedInElongatedCandidate motion D)
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
  let cover : Fin repetitions × iota →
      Finset (Fin (Fintype.card
        (NormalizedRigidCandidate motionChoice iota))) := fun a ↦
    {normalizedRigidCandidateIndex (selectedOccurrenceCandidate omega a)}
  refine ⟨cover, ?_, ?_, ?_⟩
  · intro a
    exact Finset.subset_univ _
  · intro a
    simp [cover]
  · intro a b hconflict
    let K := normalizedRigidCandidateIndex
      (selectedOccurrenceCandidate omega a)
    refine ⟨K, ?_, ?_⟩
    · simp [K, cover]
    · have hliteral :
          ¬ EssentiallyDistinct
              (normalizedRigidCandidateTube motion D
                (selectedOccurrenceCandidate omega b))
              (normalizedRigidCandidateTube motion D
                (selectedOccurrenceCandidate omega a)) := by
          simpa only [normalizedConflict, eighthNormalizedDatum_family,
            eighthNormalizedTubeFamily_tubes, indexedRigidCopyDatum,
            indexedRigidCopyTubeFamily_tubes,
            normalizedRigidCandidateTube_selectedOccurrence] using hconflict
      simpa only [K, normalizedRigidCandidateElongatedBody_index,
        normalizedRigidCandidateTube_selectedOccurrence] using
        hgeometry (selectedOccurrenceCandidate omega a)
          (selectedOccurrenceCandidate omega b) hliteral

#print axioms normalizedRigidCandidateOfIndex_index
#print axioms normalizedRigidCandidateAlignedFrame_two
#print axioms normalizedRigidCandidateElongatedBody_index
#print axioms NormalizedConflictHasElongatedCoordinateBudget.toContained
#print axioms exists_canonical_normalizedConflict_bodyMultiCover

end
end Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
