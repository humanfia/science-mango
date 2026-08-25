import FamilyStickyGrounding.FamilyStickyAllParentLayerJointCollisionRandomMotionV1
import FamilyStickyRandomFiniteCollisionRefinementV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyRandomLocalExactCarrierDedupV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyAllParentLayerJointRepetitionsV1
open FamilyStickyAllParentLayerJointCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomFiniteCollisionRefinementV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Local exact-carrier deduplication from the collision event

The joint random-motion output bounds, for every model candidate `a`, the
sum over selected translations of the number of source tubes contained in
`100 a`.  This module records the first unconditional counting consequence.
For one fixed parent fibre, every exact carrier fibre of the occurrence map

`(translation choice, active source) -> translated tube carrier`

injects into the collision witnesses of any one occurrence in that fibre.
Consequently exact carrier deduplication loses at most the already proved
collision threshold.

This statement is deliberately local to one layer and one parent.  It does
not assume pairwise separation or injectivity of a global `FinalIndex`, and
it does not identify exact carrier inequality with the paper's stronger
essential-distinctness relation.  Passing from these local classes to the
fully composed hierarchy still needs a cross-scale collision-containment
bridge: equality (or non-separation) after all later translations must be
routed to a collision class at a definite layer.
-/

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Literal occurrences produced by `J` selected translations of one active
source grid. -/
abbrev LocalOccurrence
    (G : ActualTubeTranslationGrid delta translation tubeIndex) (J : Nat) :=
  Fin J × {i // i ∈ G.tubes}

/-- The actual translated tube carried by one local occurrence. -/
def occurrenceTube
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J) : Tube delta :=
  translateTube (G.tube a.2.1) (G.gridVector (omega a.1))

/-- The occurrence itself is one of the finite model candidates tested by
the collision event. -/
def occurrenceCandidate
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J) : ModelCandidate G :=
  (a.2, omega a.1)

/-- The exact-carrier fibre through an occurrence.  This is honest exact
deduplication only; no geometric separation is claimed. -/
abbrev ExactCarrierFiber
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J) :=
  {b : LocalOccurrence G J //
    (occurrenceTube G omega b).carrier =
      (occurrenceTube G omega a).carrier}

/-- Collision witnesses counted by the already constructed sum of candidate
loads around the model candidate belonging to `a`. -/
abbrev CollisionWitness
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J) :=
  Sigma fun j : Fin J =>
    {i // i ∈ candidateCollisionFinset G
      (occurrenceCandidate G omega a) (omega j)}

/-- Forget a collision witness back to its underlying local occurrence. -/
def collisionWitnessOccurrence
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J)
    (w : CollisionWitness G omega a) : LocalOccurrence G J :=
  ⟨w.1, ⟨w.2.1,
    ((mem_candidateCollisionFinset G
      (occurrenceCandidate G omega a) (omega w.1) w.2.1).mp w.2.2).1⟩⟩

/-- Exact equality with the centre carrier puts an occurrence into the
centre's literal `100`-tube collision test. -/
def exactCarrierFiberToCollisionWitness
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J) :
    ExactCarrierFiber G omega a -> CollisionWitness G omega a := by
  intro b
  refine ⟨b.1.1, ⟨b.1.2.1, ?_⟩⟩
  apply (mem_candidateCollisionFinset G
    (occurrenceCandidate G omega a) (omega b.1.1) b.1.2.1).mpr
  refine ⟨b.1.2.2, ?_⟩
  change (occurrenceTube G omega b.1).carrier ⊆ _
  rw [b.2]
  simpa [occurrenceTube, occurrenceCandidate, modelCandidateTube] using
    (carrier_subset_hundredTube
      (modelCandidateTube G (occurrenceCandidate G omega a)))

theorem exactCarrierFiberToCollisionWitness_injective
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J) :
    Function.Injective (exactCarrierFiberToCollisionWitness G omega a) := by
  intro b c hbc
  apply Subtype.ext
  have h := congrArg (collisionWitnessOccurrence G omega a) hbc
  simpa [exactCarrierFiberToCollisionWitness,
    collisionWitnessOccurrence] using h

/-- Every exact carrier fibre is bounded by the collision sum around any one
of its occurrences. -/
theorem exactCarrierFiber_card_le_collisionSum
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation)
    (a : LocalOccurrence G J) :
    Fintype.card (ExactCarrierFiber G omega a) <=
      ∑ j, candidateCollisionLoad G
        (occurrenceCandidate G omega a) (omega j) := by
  classical
  have hcard := Fintype.card_le_of_injective
    (exactCarrierFiberToCollisionWitness G omega a)
    (exactCarrierFiberToCollisionWitness_injective G omega a)
  simpa [CollisionWitness, candidateCollisionLoad] using hcard

/-- Finite exact-carrier image of the local occurrence family. -/
def exactCarrierImage
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J : Nat} (omega : Fin J -> translation) : Finset (Set Space) := by
  classical
  exact Finset.univ.image fun a : LocalOccurrence G J =>
    (occurrenceTube G omega a).carrier

/-- A uniform collision-load bound gives an actual local deduplication card
bound.  The right side counts represented carrier sets, not occurrence
indices. -/
theorem localOccurrence_card_le_mul_exactCarrierImage_card
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {J M : Nat} (omega : Fin J -> translation)
    (hload : forall a : ModelCandidate G,
      (∑ j, candidateCollisionLoad G a (omega j)) <= M) :
    Fintype.card (LocalOccurrence G J) <=
      M * (exactCarrierImage G omega).card := by
  classical
  apply BoundedCollisionCode.card_le_multiplicity_mul_card_image
    (fun a : LocalOccurrence G J => (occurrenceTube G omega a).carrier) M
  intro K hK
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hK
  have hfiber := exactCarrierFiber_card_le_collisionSum G omega a
  have hbound := (hfiber.trans (hload (occurrenceCandidate G omega a)))
  rw [← Fintype.card_subtype]
  exact hbound

section JointLayer

variable {parent : Type*} [Fintype parent] [DecidableEq parent]
  {motionRadius : NNReal}

/-- Direct specialization to one active parent of the B8 joint output.  This
is the exact first seam after the joint analytic/collision construction. -/
theorem jointOutput_parentOccurrence_card_le_dedup
    (L : AllParentLayerData delta parent tubeIndex)
    (O : AllParentLayerJointCollisionOutput L motionRadius)
    (p : parent) (hp : p ∈ L.activeParents) :
    Fintype.card
        (LocalOccurrence (parentPackingGrid L O.certificate p)
          (jointRepetitions L motionRadius)) <=
      Nat.ceil
          (FamilyStickyRandomTwoFamilyTailV1.completionTail
              (activeCollisionTests L O.certificate).card
              (FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter L) *
            FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant) *
        (exactCarrierImage
          (parentPackingGrid L O.certificate p) O.omega).card := by
  apply localOccurrence_card_le_mul_exactCarrierImage_card
  exact O.allParentCollisionLoad p hp

#print axioms jointOutput_parentOccurrence_card_le_dedup

end JointLayer

#print axioms exactCarrierFiber_card_le_collisionSum
#print axioms localOccurrence_card_le_mul_exactCarrierImage_card

/-! A two-scale cancellation counterexample: even injective choices at each
individual scale need not give an injective composed path. -/

def cancellationScaleVector (k j : Fin 2) : Int :=
  if k = 0 then j.1 else -(j.1 : Int)

def cancellationZeroPath : Fin 2 -> Fin 2 := fun _ => 0
def cancellationOnePath : Fin 2 -> Fin 2 := fun _ => 1

theorem cancellationScaleVector_injective (k : Fin 2) :
    Function.Injective (cancellationScaleVector k) := by
  fin_cases k <;> intro a b h <;> fin_cases a <;> fin_cases b <;>
    simp [cancellationScaleVector] at h ⊢

theorem cancellation_paths_ne :
    cancellationZeroPath ≠ cancellationOnePath := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  simp [cancellationZeroPath, cancellationOnePath] at h0

theorem cancellation_composed_eq :
    (∑ k, cancellationScaleVector k (cancellationZeroPath k)) =
      ∑ k, cancellationScaleVector k (cancellationOnePath k) := by
  norm_num [Fin.sum_univ_two, cancellationScaleVector,
    cancellationZeroPath, cancellationOnePath]

#print axioms cancellationScaleVector_injective
#print axioms cancellation_paths_ne
#print axioms cancellation_composed_eq

end

end FamilyStickyRandomLocalExactCarrierDedupV1
