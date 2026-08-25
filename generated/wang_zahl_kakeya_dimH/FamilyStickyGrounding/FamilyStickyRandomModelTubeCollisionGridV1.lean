import FamilyStickyGrounding.FamilyStickyActualSharedPaperRandomMotionAutomaticV1
import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure

open Set
open scoped ENNReal NNReal

namespace FamilyStickyRandomModelTubeCollisionGridV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid

noncomputable section

/-!
# Finite model-tube collision tests on one shared translation packing

In GWZ `lemrandommotion`, pinned source lines 2655--2677, the essential
collision tests are the bodies denoted `100 T₀`.  For a fixed finite
translation packing there is a canonical finite catalogue: every active
source tube translated by every packing center.  This module turns that
catalogue into an actual finite test grid.

We make the dilation convention literal.  `hundredTube T` retains the unit
axis of the `δ`-tube `T` and changes its radius to `100δ`; hence its carrier is
the closed `100δ`-neighborhood of that same axis.  This is carrier
containment, never Tube equality.  The automatic aligned box has side lengths
`200δ, 200δ, 1+200δ`.  Its `HasBoxDimensions 2` certificate requires the
source small-scale condition `100δ ≤ 1/2`.
-/

def hundredRadius (delta : NNReal) : NNReal := 100 * delta

/-- The literal formal counterpart of the paper's `100 T₀`. -/
def hundredTube {delta : NNReal} (T : Tube delta) : Tube (hundredRadius delta) :=
  T.changeRadius (hundredRadius delta)

@[simp] theorem hundredTube_axis {delta : NNReal} (T : Tube delta) :
    (hundredTube T).axis = T.axis := rfl

@[simp] theorem hundredTube_carrier {delta : NNReal} (T : Tube delta) :
    (hundredTube T).carrier =
      Metric.cthickening (hundredRadius delta : Real) T.axis.carrier := rfl

theorem carrier_subset_hundredTube {delta : NNReal} (T : Tube delta) :
    T.carrier ⊆ (hundredTube T).carrier := by
  apply T.carrier_subset_changeRadius
  unfold hundredRadius
  nlinarith [delta.2]

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Every possible translated active tube on this packing is a model cell. -/
abbrev ModelCandidate
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :=
  {i // i ∈ G.tubes} × translation

def modelCandidateTube
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) : Tube delta :=
  translateTube (G.tube a.1.1) (G.gridVector a.2)

def modelCandidateEquivFin
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    ModelCandidate G ≃ Fin (Fintype.card (ModelCandidate G)) :=
  Fintype.equivFin _

def modelCandidateIndex
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) : Fin (Fintype.card (ModelCandidate G)) :=
  modelCandidateEquivFin G a

def modelCandidateOfIndex
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (Fintype.card (ModelCandidate G))) : ModelCandidate G :=
  (modelCandidateEquivFin G).symm K

@[simp] theorem modelCandidateOfIndex_index
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) :
    modelCandidateOfIndex G (modelCandidateIndex G a) = a := by
  simp [modelCandidateOfIndex, modelCandidateIndex]

/-- Replace the old tests by every finite `100T₀` candidate, without changing
the translation packing or source tube family. -/
def collisionGrid
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    ActualTubeTranslationGrid delta translation tubeIndex where
  gridVector := G.gridVector
  tubes := G.tubes
  tube := G.tube
  testCard := Fintype.card (ModelCandidate G)
  testBody := fun K =>
    (hundredTube (modelCandidateTube G (modelCandidateOfIndex G K))).body
  activeTests := Finset.univ

@[simp] theorem collisionGrid_gridVector
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    (collisionGrid G).gridVector = G.gridVector := rfl

@[simp] theorem collisionGrid_tubes
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    (collisionGrid G).tubes = G.tubes := rfl

@[simp] theorem collisionGrid_tube
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    (collisionGrid G).tube = G.tube := rfl

@[simp] theorem collisionGrid_activeTests
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    (collisionGrid G).activeTests = Finset.univ := rfl

@[simp] theorem collisionGrid_testBody_candidate
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) :
    (collisionGrid G).testBody (modelCandidateIndex G a) =
      (hundredTube (modelCandidateTube G a)).body := by
  simp [collisionGrid]

/-- The same actual packing certificate survives replacement of the test
suite. -/
theorem IsSharedTranslationPacking.collisionGrid
    {G : ActualTubeTranslationGrid delta translation tubeIndex}
    {mesh motionRadius : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    IsSharedTranslationPacking (collisionGrid G) mesh motionRadius where
  mesh_pos := P.mesh_pos
  gridVector_injective := P.gridVector_injective
  gridVector_norm_le := P.gridVector_norm_le
  separated := P.separated
  cover_motionBall := P.cover_motionBall

/-- Constant frame-box sides of every `100T₀` collision body. -/
def collisionSide
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    Fin (collisionGrid G).testCard -> Fin 3 -> NNReal :=
  fun _ => Tube.frameBoxSides (hundredRadius delta)

theorem collisionGrid_hasBoxDimensions
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hsmall : hundredRadius delta <= (2 : NNReal)⁻¹) :
    forall K, HasBoxDimensions 2 (collisionSide G K)
      ((collisionGrid G).testBody K) := by
  intro K
  exact (hundredTube
    (modelCandidateTube G (modelCandidateOfIndex G K))).hasBoxDimensions_frameBoxSides hsmall

theorem delta_le_collisionSide_zero
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (collisionGrid G).testCard) :
    delta <= collisionSide G K 0 := by
  simp [collisionSide, Tube.frameBoxSides, hundredRadius]
  nlinarith [delta.2]

theorem delta_le_collisionSide_one
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (collisionGrid G).testCard) :
    delta <= collisionSide G K 1 := by
  simp [collisionSide, Tube.frameBoxSides, hundredRadius]
  nlinarith [delta.2]

/-- Every candidate translated tube is contained in its own `100T₀` test
body. -/
theorem candidate_carrier_subset_own_collisionTest
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) :
    (modelCandidateTube G a).carrier ⊆
      ((collisionGrid G).testBody (modelCandidateIndex G a) : Set Space) := by
  rw [collisionGrid_testBody_candidate G a]
  exact carrier_subset_hundredTube (modelCandidateTube G a)

/-- The literal finite set counted by one candidate collision test, stated
first with the collision-grid fields so its decision procedure is stable. -/
def candidateCollisionFinset
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) (g : translation) : Finset tubeIndex := by
  classical
  exact (collisionGrid G).tubes.filter fun i =>
    (translateTube ((collisionGrid G).tube i)
      ((collisionGrid G).gridVector g)).carrier ⊆
      ((collisionGrid G).testBody (modelCandidateIndex G a) : Set Space)

/-- Literal number of translated source tubes in `100T₀`. -/
def candidateCollisionLoad
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) (g : translation) : Nat :=
  (candidateCollisionFinset G a g).card

@[simp] theorem mem_candidateCollisionFinset
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) (g : translation) (i : tubeIndex) :
    i ∈ candidateCollisionFinset G a g ↔
      i ∈ G.tubes ∧
        (translateTube (G.tube i) (G.gridVector g)).carrier ⊆
          (hundredTube (modelCandidateTube G a)).carrier := by
  classical
  unfold candidateCollisionFinset
  rw [Finset.mem_filter]
  simp only [collisionGrid_tubes, collisionGrid_tube, collisionGrid_gridVector]
  rw [collisionGrid_testBody_candidate G a]
  rfl

/-- The actual collision-grid single load is exactly that literal count. -/
theorem collisionGrid_singleLoad_candidate
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) (g : translation) :
    (collisionGrid G).singleLoad (modelCandidateIndex G a) g =
      candidateCollisionLoad G a g := by
  classical
  unfold ActualTubeTranslationGrid.singleLoad candidateCollisionLoad
    candidateCollisionFinset
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  rfl

#print axioms carrier_subset_hundredTube
#print axioms modelCandidateOfIndex_index
#print axioms collisionGrid_testBody_candidate
#print axioms FamilyStickyRandomModelTubeCollisionGridV1.IsSharedTranslationPacking.collisionGrid
#print axioms collisionGrid_hasBoxDimensions
#print axioms candidate_carrier_subset_own_collisionTest
#print axioms collisionGrid_singleLoad_candidate

end
end FamilyStickyRandomModelTubeCollisionGridV1
