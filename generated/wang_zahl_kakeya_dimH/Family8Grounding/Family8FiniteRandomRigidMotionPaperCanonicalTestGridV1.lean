import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictGridBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperConflictGridBridgeV1
open FamilyStickyRandomModelTubeCollisionGridV1

noncomputable section

/-!
# The canonical finite test-tube grid

For a finite uniform law of rigid motions, every possible honestly normalized
moved source tube is itself a finite test candidate.  Thus no abstract finite
net is needed to test a tube which occurs in the selected product: its test
index is literally `(omega j, i)`.

This file constructs that finite catalogue and the covering map.  The sole
remaining coverage geometry is the local one-sided statement that a
normalized tube which is not volume-essentially-distinct from a candidate is
contained in its `100`-fold radial enlargement.  Keeping that statement as a
single premise makes the distinction between finite bookkeeping and actual
tube geometry explicit.
-/

/-- All possible normalized moved source tubes under the finite motion law. -/
abbrev NormalizedRigidCandidate
    (motionChoice iota : Type) := motionChoice × iota

def normalizedRigidCandidateTube
    {motionChoice iota : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (a : NormalizedRigidCandidate motionChoice iota) : Tube (delta / 8) :=
  eighthNormalizedTube (rigidTube (motion a.1) (D.family.tubes a.2))

@[simp] theorem normalizedRigidCandidateTube_carrier
    {motionChoice iota : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (a : NormalizedRigidCandidate motionChoice iota) :
    (normalizedRigidCandidateTube motion D a).carrier =
      (eighthNormalizedTube
        (rigidTube (motion a.1) (D.family.tubes a.2))).carrier := rfl

/-- The canonical grid index attached to an actual occurrence in a selected
tuple. -/
def selectedOccurrenceCandidate
    {motionChoice iota : Type} {repetitions : Nat}
    (omega : Fin repetitions -> motionChoice)
    (a : Fin repetitions × iota) :
    NormalizedRigidCandidate motionChoice iota :=
  (omega a.1, a.2)

@[simp] theorem normalizedRigidCandidateTube_selectedOccurrence
    {motionChoice iota : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (omega : Fin repetitions -> motionChoice)
    (a : Fin repetitions × iota) :
    normalizedRigidCandidateTube motion D
        (selectedOccurrenceCandidate omega a) =
      eighthNormalizedTube
        (rigidTube (motion (omega a.1)) (D.family.tubes a.2)) := rfl

/-- The local geometric statement still required after choosing the
canonical finite candidate catalogue. -/
def NormalizedConflictContainedInHundredCandidate
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota) : Prop :=
  forall a b : NormalizedRigidCandidate motionChoice iota,
    ¬ EssentiallyDistinct
        (normalizedRigidCandidateTube motion D b)
        (normalizedRigidCandidateTube motion D a) ->
      (normalizedRigidCandidateTube motion D b).carrier ⊆
        (hundredTube (normalizedRigidCandidateTube motion D a)).carrier

/-- The canonical catalogue automatically produces the exact grid-cover
premise consumed by the finite probability-to-conflict bridge. -/
theorem exists_canonical_normalizedConflict_gridCover
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hgeometry : NormalizedConflictContainedInHundredCandidate motion D)
    (omega : Fin repetitions -> motionChoice) :
    exists cover : Fin repetitions × iota ->
        NormalizedRigidCandidate motionChoice iota,
      (forall a, cover a ∈
        (Finset.univ : Finset
          (NormalizedRigidCandidate motionChoice iota))) ∧
      (forall a b,
        normalizedConflict
            (indexedRigidCopyDatum (fun j => motion (omega j)) D) b a ->
          (eighthNormalizedTube
            (rigidTube (motion (omega b.1))
              (D.family.tubes b.2))).carrier ⊆
            (hundredTube
              (normalizedRigidCandidateTube motion D (cover a))).carrier) := by
  let cover : Fin repetitions × iota ->
      NormalizedRigidCandidate motionChoice iota :=
    selectedOccurrenceCandidate omega
  refine ⟨cover, fun a => Finset.mem_univ (cover a), ?_⟩
  intro a b hconflict
  have hliteral :
      ¬ EssentiallyDistinct
          (normalizedRigidCandidateTube motion D
            (selectedOccurrenceCandidate omega b))
          (normalizedRigidCandidateTube motion D
            (selectedOccurrenceCandidate omega a)) := by
    simpa only [normalizedConflict, eighthNormalizedDatum_family,
      eighthNormalizedTubeFamily_tubes, indexedRigidCopyDatum,
      indexedRigidCopyTubeFamily_tubes,
      normalizedRigidCandidateTube_selectedOccurrence] using hconflict
  simpa only [cover, normalizedRigidCandidateTube_selectedOccurrence] using
    hgeometry (selectedOccurrenceCandidate omega a)
      (selectedOccurrenceCandidate omega b) hliteral

#print axioms normalizedRigidCandidateTube_selectedOccurrence
#print axioms exists_canonical_normalizedConflict_gridCover

end
end Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
