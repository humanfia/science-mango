import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import FamilyStickyGrounding.FamilyStickyRandomModelTubeCollisionGridV1
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperConflictTailV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTranslationIncidenceV1
open FamilyStickyRandomTestDependentChernoffV1

noncomputable section

/-!
# The finite probabilistic middle layer of the paper conflict argument

The random law here is the uniform law on a literal finite type of genuine
rigid motions.  For a test tube `T0`, the one-choice load counts source tubes
whose *honestly normalized* rigid image is contained in the literal carrier
of `100 T0`.  This is the event used in the appendix proof; it is deliberately
not replaced by the repository's overlap-based `EssentiallyDistinct` relation.

The file proves exact finite double counting and then reuses the finite
test-dependent Chernoff theorem to select one tuple which is simultaneously
good for every member of a supplied finite test-tube grid.  The geometric
single-tube probability estimate is isolated as the finite choice-count
premise `hchoice`.  A later coverage seam converts these all-test containment
loads into a bound on every normalized overlap-conflict neighbourhood.
-/

/-- The number of source tubes whose normalized rigid image lies in one
literal `100 T0` test under one choice of the finite motion law. -/
def normalizedRigidHundredLoadNat
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (g : motionChoice) : Nat := by
  classical
  exact ((Finset.univ : Finset iota).filter fun i =>
    (eighthNormalizedTube
      (rigidTube (motion g) (D.family.tubes i))).carrier ⊆
        (hundredTube (testTube K)).carrier).card

/-- For one source tube and one test, the number of choices in the uniform
finite motion law which create the containment event. -/
def normalizedRigidHundredChoiceCount
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (i : iota) : Nat := by
  classical
  exact ((Finset.univ : Finset motionChoice).filter fun g =>
    (eighthNormalizedTube
      (rigidTube (motion g) (D.family.tubes i))).carrier ⊆
        (hundredTube (testTube K)).carrier).card

/-- The literal containment event as an instance of the repository's generic
finite incidence model. -/
def normalizedRigidHundredIncidenceModel
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8)) :
    TranslationIncidenceModel motionChoice iota testIndex := by
  classical
  exact
    { tubes := Finset.univ
      tests := Finset.univ
      hits := fun g i K => decide
        ((eighthNormalizedTube
          (rigidTube (motion g) (D.family.tubes i))).carrier ⊆
            (hundredTube (testTube K)).carrier) }

@[simp] theorem normalizedRigidHundredIncidenceModel_tubes
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8)) :
    (normalizedRigidHundredIncidenceModel motion D testTube).tubes =
      Finset.univ := rfl

@[simp] theorem normalizedRigidHundredIncidenceModel_tests
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8)) :
    (normalizedRigidHundredIncidenceModel motion D testTube).tests =
      Finset.univ := rfl

theorem normalizedRigidHundredIncidenceModel_loadNat
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (g : motionChoice) :
    (normalizedRigidHundredIncidenceModel motion D testTube).loadNat K g =
      normalizedRigidHundredLoadNat motion D testTube K g := by
  classical
  unfold TranslationIncidenceModel.loadNat
    normalizedRigidHundredIncidenceModel normalizedRigidHundredLoadNat
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [decide_eq_true_eq]

theorem normalizedRigidHundredIncidenceModel_gridHitsTube
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (i : iota) :
    (normalizedRigidHundredIncidenceModel motion D testTube).gridHitsTube K i =
      normalizedRigidHundredChoiceCount motion D testTube K i := by
  classical
  unfold TranslationIncidenceModel.gridHitsTube
    normalizedRigidHundredIncidenceModel normalizedRigidHundredChoiceCount
  apply congrArg Finset.card
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [decide_eq_true_eq]

/-- Exact finite-law double counting: total one-choice load equals the sum of
the individual source-tube hit counts. -/
theorem sum_normalizedRigidHundredLoadNat_eq_sum_choiceCount
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) :
    (∑ g : motionChoice,
        normalizedRigidHundredLoadNat motion D testTube K g) =
      ∑ i : iota,
        normalizedRigidHundredChoiceCount motion D testTube K i := by
  let M := normalizedRigidHundredIncidenceModel motion D testTube
  have h := M.sum_loadNat_eq_sum_gridHitsTube K
  simpa only [M, normalizedRigidHundredIncidenceModel_tubes,
    normalizedRigidHundredIncidenceModel_loadNat,
    normalizedRigidHundredIncidenceModel_gridHitsTube] using h

/-- A local finite-law choice-count estimate gives the required exact mean
bound after cross multiplication. -/
theorem sum_normalizedRigidHundredLoadNat_le_card_mul_mean
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (choiceBudget : testIndex -> Nat)
    (mean : testIndex -> Real)
    (K : testIndex)
    (hchoice : forall i : iota,
      normalizedRigidHundredChoiceCount motion D testTube K i <=
        choiceBudget K)
    (hbalance :
      (Fintype.card iota : Real) * (choiceBudget K : Real) <=
        (Fintype.card motionChoice : Real) * mean K) :
    (∑ g : motionChoice,
        (normalizedRigidHundredLoadNat motion D testTube K g : Real)) <=
      (Fintype.card motionChoice : Real) * mean K := by
  have hsumNat :
      (∑ g : motionChoice,
        normalizedRigidHundredLoadNat motion D testTube K g) <=
        Fintype.card iota * choiceBudget K := by
    rw [sum_normalizedRigidHundredLoadNat_eq_sum_choiceCount]
    calc
      (∑ i : iota,
          normalizedRigidHundredChoiceCount motion D testTube K i) <=
          ∑ _i : iota, choiceBudget K := by
        exact Finset.sum_le_sum fun i _hi => hchoice i
      _ = Fintype.card iota * choiceBudget K := by simp
  have hsumReal :
      (∑ g : motionChoice,
        (normalizedRigidHundredLoadNat motion D testTube K g : Real)) <=
        (Fintype.card iota : Real) * (choiceBudget K : Real) := by
    exact_mod_cast hsumNat
  exact hsumReal.trans hbalance

/-- Bounded load plus the finite-law mean estimate gives an exponential tail
and one tuple which is good for every test tube in the finite grid. -/
theorem exists_rigidMotionTuple_all_normalizedHundredLoads_le
    {motionChoice iota testIndex : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    [Fintype testIndex] [DecidableEq testIndex]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (activeTests : Finset testIndex)
    (choiceBudget : testIndex -> Nat)
    (repetitions : Nat)
    (cap mean : testIndex -> Real) (A : Real)
    (hcap : forall K, K ∈ activeTests -> 0 <= cap K)
    (hmean : forall K, K ∈ activeTests -> 0 <= mean K)
    (hloadCap : forall K, K ∈ activeTests -> forall g,
      (normalizedRigidHundredLoadNat motion D testTube K g : Real) <=
        cap K)
    (hchoice : forall K, K ∈ activeTests -> forall i : iota,
      normalizedRigidHundredChoiceCount motion D testTube K i <=
        choiceBudget K)
    (hbalance : forall K, K ∈ activeTests ->
      (Fintype.card iota : Real) * (choiceBudget K : Real) <=
        (Fintype.card motionChoice : Real) * mean K)
    (hscale : forall K, K ∈ activeTests ->
      (repetitions : Real) * mean K <= cap K)
    (htailRoom :
      (activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A) :
    exists omega : Fin repetitions -> motionChoice,
      forall K, K ∈ activeTests ->
        (∑ j,
          (normalizedRigidHundredLoadNat motion D testTube K
            (omega j) : Real)) <=
          A * cap K := by
  apply exists_product_choice_load_le_A_mul_cap
    activeTests repetitions
    (fun K g =>
      (normalizedRigidHundredLoadNat motion D testTube K g : Real))
    cap mean A hcap hmean
  · intro K _hK g
    exact Nat.cast_nonneg _
  · exact hloadCap
  · intro K hK
    exact sum_normalizedRigidHundredLoadNat_le_card_mul_mean
      motion D testTube choiceBudget mean K
        (hchoice K hK) (hbalance K hK)
  · exact hscale
  · exact htailRoom

#print axioms normalizedRigidHundredIncidenceModel_loadNat
#print axioms normalizedRigidHundredIncidenceModel_gridHitsTube
#print axioms sum_normalizedRigidHundredLoadNat_eq_sum_choiceCount
#print axioms sum_normalizedRigidHundredLoadNat_le_card_mul_mean
#print axioms exists_rigidMotionTuple_all_normalizedHundredLoads_le

end
end Family8FiniteRandomRigidMotionPaperConflictTailV1
