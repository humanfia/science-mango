import Family8Grounding.Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictMultiGridBridgeV1
import FamilyStickyGrounding.FamilyStickyActualTranslationPointHitV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperTranslationPointBudgetV1

open Family8FiniteRandomRigidMotionIncidenceV1
open FamilyStickyRandomModelTubeCollisionGridV1
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1

noncomputable section

/-!
# The normalized one-tube choice count from an actual point budget

For a finite law consisting of genuine translations, normalization changes
the translation vector from `v` to `v / 8`.  We package those rescaled
vectors and the literal `100 delta` test-tube bodies as the repository's
existing `ActualTubeTranslationGrid`.  Its proved point-hit bound then
supplies the exact `hchoice` premise of the paper-strength finite Chernoff
argument; no probabilistic or geometric conclusion is assumed here.
-/

/-- The actual translation grid seen after the honest `B2 -> B1`
normalization.  Every source tube has radius `delta / 8`, and every test body
is the literal carrier of the corresponding hundred-fold tube. -/
def normalizedTranslationGrid
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard)) :
    ActualTubeTranslationGrid (delta / 8) translation iota where
  gridVector g := eighthTranslationVector (gridVector g)
  tubes := Finset.univ
  tube i := eighthNormalizedTube (D.family.tubes i)
  testCard := testCard
  testBody K := (hundredTube (testTube K)).body
  activeTests := activeTests

@[simp] theorem normalizedTranslationGrid_gridVector
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard)) (g : translation) :
    (normalizedTranslationGrid gridVector D testTube activeTests).gridVector g =
      eighthTranslationVector (gridVector g) := rfl

@[simp] theorem normalizedTranslationGrid_tubes
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard)) :
    (normalizedTranslationGrid gridVector D testTube activeTests).tubes =
      Finset.univ := rfl

/-- The normalized rigid-motion one-tube incidence is exactly the existing
actual translation-grid tube-hit count. -/
theorem normalizedTranslationGrid_tubeHitCount
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (K : Fin testCard) (i : iota) :
    (normalizedTranslationGrid gridVector D testTube activeTests).tubeHitCount
        K i =
      normalizedRigidHundredChoiceCount
        (fun g => translationRigidMotion (gridVector g)) D testTube K i := by
  classical
  unfold FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid.tubeHitCount
    normalizedRigidHundredChoiceCount normalizedTranslationGrid
  apply congrArg Finset.card
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [eighthNormalizedTube_rigidTranslation, Tube.coe_body]

/-- Any literal point-hit cap for the normalized translation grid
automatically discharges the paper conflict tail's per-tube `hchoice`. -/
theorem normalizedRigidHundredChoiceCount_le_of_pointHitCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (choiceBudget : Fin testCard -> Nat)
    (hpoint :
      FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.HasPointHitCap
        (normalizedTranslationGrid gridVector D testTube activeTests)
        choiceBudget) :
    forall K, K ∈ activeTests -> forall i : iota,
      normalizedRigidHundredChoiceCount
          (fun g => translationRigidMotion (gridVector g)) D testTube K i <=
        choiceBudget K := by
  intro K hK i
  rw [<- normalizedTranslationGrid_tubeHitCount]
  exact
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.tubeHitCount_le_of_hasPointHitCap
      (normalizedTranslationGrid gridVector D testTube activeTests)
      choiceBudget hpoint K hK i (Finset.mem_univ i)

#print axioms normalizedTranslationGrid_tubeHitCount
#print axioms normalizedRigidHundredChoiceCount_le_of_pointHitCap

end
end Family8FiniteRandomRigidMotionPaperTranslationPointBudgetV1
