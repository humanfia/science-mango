import FamilyStickyGrounding.FamilyStickyBoxCertifiedTubeTestDataV1
import FamilyStickyGrounding.FamilyStickyActualTubeTestDataV1
import FamilyStickyGrounding.FamilyStickyPaperRandomMotionNumericalChoicesV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyAllParentLayerDataV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyBoxCertifiedTubeTestDataV1
open FamilyStickyPaperRandomMotionNumericalChoicesV1.ActualTubeTestData

noncomputable section

/-!
# One scale with all parent-local tube families

GWZ lines 1520--1524 require one translation family at scale `k` to be good
for every coarse parent.  Each parent therefore keeps its own local tube
finset, maximal concentration, box-certified tests, and cap, while all parent
tests share a single ambient translation vector.
-/

structure AllParentLayerData
    (delta : NNReal) (parent tubeIndex : Type*)
    [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex] where
  activeParents : Finset parent
  parentData : parent -> BoxCertifiedTubeTestData delta tubeIndex

namespace AllParentLayerData

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

/-- Finite dependent index of all parent/test pairs. -/
abbrev Test (L : AllParentLayerData delta parent tubeIndex) :=
  Σ p, Fin (L.parentData p).data.testCard

/-- Only tests active inside an active parent enter the layer union bound. -/
def activeTests (L : AllParentLayerData delta parent tubeIndex) :
    Finset L.Test :=
  L.activeParents.sigma fun p => (L.parentData p).data.activeTests

/-- Literal parent-local load at one ambient vector. -/
def singleLoadAt (L : AllParentLayerData delta parent tubeIndex)
    (q : L.Test) (v : Space) : Nat :=
  (L.parentData q.1).data.singleLoadAt q.2 v

/-- Parent-local paper cap; no global worst-parent concentration is used. -/
def paperCap (L : AllParentLayerData delta parent tubeIndex)
    (q : L.Test) : Real :=
  (L.parentData q.1).data.canonicalPaperSingleLoadCap q.2

/-- Explicit local incidence mean for a parent/test pair. -/
def paperMean (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) (q : L.Test) : Real :=
  paperIncidenceMean (L.parentData q.1).data (L.parentData q.1).side
    motionRadius q.2

/-- A one-point seed grid for a particular parent. -/
def parentSeedGrid (L : AllParentLayerData delta parent tubeIndex)
    (p : parent) : ActualTubeTranslationGrid delta Unit tubeIndex :=
  (L.parentData p).data.seedGrid

theorem mem_activeTests_iff
    (L : AllParentLayerData delta parent tubeIndex)
    (q : L.Test) :
    q ∈ L.activeTests ↔
      q.1 ∈ L.activeParents ∧ q.2 ∈ (L.parentData q.1).data.activeTests := by
  rcases q with ⟨p, K⟩
  simp [activeTests]

theorem paperMean_nonneg
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) (q : L.Test) :
    0 <= L.paperMean motionRadius q :=
  paperIncidenceMean_nonneg (L.parentData q.1).data
    (L.parentData q.1).side motionRadius q.2

#print axioms mem_activeTests_iff
#print axioms paperMean_nonneg

end AllParentLayerData

end
end FamilyStickyAllParentLayerDataV1
