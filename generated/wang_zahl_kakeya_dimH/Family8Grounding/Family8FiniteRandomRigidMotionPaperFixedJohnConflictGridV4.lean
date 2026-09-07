import Family8Grounding.Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3
import Family8Grounding.Family8PolynomialJohnFrameBoxAllConvexV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxAllConvexV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# A fixed polynomial John catalogue for normalized conflicts

Side-six conflict bodies are clipped to B1 and sent into the existing
polynomial John catalogue.  The test type depends only on the normalized
radius, not on the finite motion law or selected tuple.
-/

def normalizedJohnCatalogueEquivFin
    (rho : NNReal) (hrho : 0 < rho) :
    CatalogueIndex rho hrho ≃ Fin (Fintype.card (CatalogueIndex rho hrho)) :=
  Fintype.equivFin _

def normalizedJohnCatalogueIndex
    {rho : NNReal} {hrho : 0 < rho} (q : CatalogueIndex rho hrho) :
    Fin (Fintype.card (CatalogueIndex rho hrho)) :=
  normalizedJohnCatalogueEquivFin rho hrho q

def normalizedJohnCatalogueOfIndex
    {rho : NNReal} {hrho : 0 < rho}
    (K : Fin (Fintype.card (CatalogueIndex rho hrho))) :
    CatalogueIndex rho hrho :=
  (normalizedJohnCatalogueEquivFin rho hrho).symm K

@[simp] theorem normalizedJohnCatalogueOfIndex_index
    {rho : NNReal} {hrho : 0 < rho} (q : CatalogueIndex rho hrho) :
    normalizedJohnCatalogueOfIndex (normalizedJohnCatalogueIndex q) = q := by
  simp [normalizedJohnCatalogueOfIndex, normalizedJohnCatalogueIndex,
    normalizedJohnCatalogueEquivFin]

def normalizedJohnCatalogueBody
    (rho : NNReal) (hrho : 0 < rho)
    (K : Fin (Fintype.card (CatalogueIndex rho hrho))) : ConvexBody Space :=
  representativeTestBody rho hrho (normalizedJohnCatalogueOfIndex K)

@[simp] theorem normalizedJohnCatalogueBody_index
    {rho : NNReal} {hrho : 0 < rho} (q : CatalogueIndex rho hrho) :
    normalizedJohnCatalogueBody rho hrho (normalizedJohnCatalogueIndex q) =
      representativeTestBody rho hrho q := by
  simp [normalizedJohnCatalogueBody]

/-- Every normalized conflict is covered by one fixed-catalogue test. -/
theorem exists_fixedJohn_normalizedConflict_bodyMultiCover
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice → RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (hunit : ∀ a : NormalizedRigidCandidate motionChoice iota,
      (normalizedRigidCandidateTube motion D a).carrier ⊆
        Metric.closedBall (0 : Space) 1)
    (omega : Fin repetitions → motionChoice) :
    let hrho : 0 < delta / 8 := div_pos hD.delta_pos (by norm_num)
    ∃ cover : Fin repetitions × iota →
        Finset (Fin (Fintype.card (CatalogueIndex (delta / 8) hrho))),
      (∀ a, cover a ⊆ Finset.univ) ∧
      (∀ a, (cover a).card ≤ 1) ∧
      (∀ a b,
        normalizedConflict
            (indexedRigidCopyDatum (fun j ↦ motion (omega j)) D) b a →
          ∃ K, K ∈ cover a ∧
            (eighthNormalizedTube
              (rigidTube (motion (omega b.1))
                (D.family.tubes b.2))).carrier ⊆
              (normalizedJohnCatalogueBody (delta / 8) hrho K :
                Set Space)) := by
  classical
  let hrho : 0 < delta / 8 := div_pos hD.delta_pos (by norm_num)
  let candidate : Fin repetitions × iota →
      NormalizedRigidCandidate motionChoice iota :=
    selectedOccurrenceCandidate omega
  let anchor : Fin repetitions × iota → Tube (delta / 8) :=
    fun a ↦ normalizedRigidCandidateTube motion D (candidate a)
  let anchorFrame : Fin repetitions × iota →
      OrthonormalBasis (Fin 3) Real Space :=
    fun a ↦ normalizedRigidCandidateAlignedFrame motion D (candidate a)
  let body : Fin repetitions × iota → ConvexBody Space :=
    fun a ↦ paperElongatedBody (anchor a) (anchorFrame a)
  have hrhoOne : delta / 8 ≤ (1 : NNReal) := by
    exact (div_le_self (show 0 ≤ delta from bot_le)
      (by norm_num : (1 : NNReal) ≤ 8)).trans
        (hD.delta_le_half.trans (by norm_num))
  have hanchorBody (a : Fin repetitions × iota) :
      (anchor a).carrier ⊆ (body a : Set Space) := by
    exact carrier_subset_paperElongatedBody
      (anchor a) (anchorFrame a)
      (normalizedRigidCandidateAlignedFrame_two motion D (candidate a))
      hrhoOne
  let parameter : Fin repetitions × iota →
      CapturedJohnParameter (delta / 8) := fun a ↦
    CapturedJohnParameter.ofCapturedTube hrho (body a) (anchor a)
      (hanchorBody a) (hunit (candidate a))
  let code : Fin repetitions × iota → CatalogueIndex (delta / 8) hrho :=
    fun a ↦ parameterCode hrho (parameter a)
  let cover : Fin repetitions × iota →
      Finset (Fin (Fintype.card (CatalogueIndex (delta / 8) hrho))) :=
    fun a ↦ {normalizedJohnCatalogueIndex (code a)}
  refine ⟨cover, ?_, ?_, ?_⟩
  · intro a
    exact Finset.subset_univ _
  · intro a
    simp [cover]
  · intro a b hconflict
    refine ⟨normalizedJohnCatalogueIndex (code a), ?_, ?_⟩
    · simp [cover]
    · have hliteral :
          ¬ EssentiallyDistinct (anchor b) (anchor a) := by
        simpa only [anchor, candidate, normalizedConflict,
          eighthNormalizedDatum_family, eighthNormalizedTubeFamily_tubes,
          indexedRigidCopyDatum, indexedRigidCopyTubeFamily_tubes,
          normalizedRigidCandidateTube_selectedOccurrence] using hconflict
      have hbody : (anchor b).carrier ⊆ (body a : Set Space) := by
        have hgeometry :=
          normalizedConflictContainedInElongatedCandidate motion D hD
        exact hgeometry (candidate a) (candidate b) hliteral
      have hcatalogue := capturedTube_subset_catalogueTest
        hrho (body a) (anchor a) (hanchorBody a) (hunit (candidate a))
        (anchor b) hbody (hunit (candidate b))
      simpa only [normalizedJohnCatalogueBody_index, code, parameter,
        anchor, candidate, normalizedRigidCandidateTube_selectedOccurrence]
        using hcatalogue

#print axioms normalizedJohnCatalogueOfIndex_index
#print axioms normalizedJohnCatalogueBody_index
#print axioms exists_fixedJohn_normalizedConflict_bodyMultiCover

end
end Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
