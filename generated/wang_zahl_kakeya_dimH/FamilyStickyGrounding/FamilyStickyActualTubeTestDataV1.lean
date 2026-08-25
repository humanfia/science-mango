import FamilyStickyGrounding.FamilyStickyActualPaperSingleLoadProducerV1
import FamilyStickyGrounding.FamilyStickySharedTranslationPackingExistenceV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualTubeTestDataV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingExistenceV1.ActualTubeTranslationGrid

noncomputable section

/-!
# Tube/test data before choosing a translation grid

The source geometry consists only of the active tubes and convex test bodies.
The finite translation type is an auxiliary object produced later from a
maximal packing of the motion ball, so it does not belong in the final input.
-/

structure ActualTubeTestData
    (delta : NNReal) (tubeIndex : Type*) [DecidableEq tubeIndex] where
  tubes : Finset tubeIndex
  tube : tubeIndex -> Tube delta
  testCard : Nat
  testBody : Fin testCard -> ConvexBody Space
  activeTests : Finset (Fin testCard)

namespace ActualTubeTestData

variable {delta : NNReal} {tubeIndex : Type*} [DecidableEq tubeIndex]

/-- A dummy one-point grid used only to feed the packing-grid constructor.
Its old translation vector is discarded by that constructor. -/
def seedGrid (D : ActualTubeTestData delta tubeIndex) :
    ActualTubeTranslationGrid delta Unit tubeIndex where
  gridVector _ := 0
  tubes := D.tubes
  tube := D.tube
  testCard := D.testCard
  testBody := D.testBody
  activeTests := D.activeTests

/-- Literal load at an ambient translation vector, independent of any finite
sampling type. -/
def singleLoadAt (D : ActualTubeTestData delta tubeIndex)
    (K : Fin D.testCard) (v : Space) : Nat := by
  classical
  exact (D.tubes.filter fun i =>
    (translateTube (D.tube i) v).carrier ⊆
      (D.testBody K : Set Space)).card

/-- The Appendix fixed-test cap, defined before the finite packing is chosen. -/
def canonicalPaperSingleLoadCap
    (D : ActualTubeTestData delta tubeIndex) (K : Fin D.testCard) : Real :=
  paperSingleLoadCap D.seedGrid K

@[simp] theorem packedGrid_singleLoad
    (D : ActualTubeTestData delta tubeIndex)
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    (K : Fin D.testCard) (g : ↥C.centers) :
    (ofMotionBallPackingCertificate D.seedGrid C).singleLoad K g =
      D.singleLoadAt K g.1 := rfl

@[simp] theorem packedGrid_paperSingleLoadCap
    (D : ActualTubeTestData delta tubeIndex)
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    (K : Fin D.testCard) :
    paperSingleLoadCap (ofMotionBallPackingCertificate D.seedGrid C) K =
      D.canonicalPaperSingleLoadCap K := rfl

@[simp] theorem packedGrid_tubes
    (D : ActualTubeTestData delta tubeIndex)
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    (ofMotionBallPackingCertificate D.seedGrid C).tubes = D.tubes := rfl

#print axioms packedGrid_singleLoad
#print axioms packedGrid_paperSingleLoadCap

end ActualTubeTestData

end
end FamilyStickyActualTubeTestDataV1
