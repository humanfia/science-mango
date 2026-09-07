import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictTailV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperConflictGridBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open FamilyStickyRandomModelTubeCollisionGridV1

noncomputable section

/-!
# From finite `100 T0` loads to normalized conflict neighbourhoods

The probability layer controls every member of a finite test-tube grid.  The
only geometry needed to turn this into the fresh-greedy premise is a covering
map: for each normalized copied tube, every tube which is not essentially
distinct from it must lie in the `100`-fold dilation of one active grid tube.

That covering statement is kept as an explicit premise.  Everything after it
is exact finite-set bookkeeping: product loads split by repetition, coverage
gives a Finset inclusion, and the real Chernoff estimate is cast back to a
uniform natural conflict threshold.
-/

/-- Product indices whose honestly normalized moved tube lies in one literal
`100 T0` test. -/
def normalizedRigidCopyHundredIndices
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (omega : Fin repetitions -> motionChoice)
    (K : testIndex) : Finset (Fin repetitions × iota) := by
  classical
  exact Finset.univ.filter fun a =>
    (eighthNormalizedTube
      (rigidTube (motion (omega a.1)) (D.family.tubes a.2))).carrier ⊆
        (hundredTube (testTube K)).carrier

/-- The product containment count is exactly the sum of the one-choice loads
selected by the tuple. -/
theorem normalizedRigidCopyHundredIndices_card_eq_sum_load
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (omega : Fin repetitions -> motionChoice)
    (K : testIndex) :
    (normalizedRigidCopyHundredIndices motion D testTube omega K).card =
      ∑ j, normalizedRigidHundredLoadNat motion D testTube K (omega j) := by
  classical
  unfold normalizedRigidCopyHundredIndices normalizedRigidHundredLoadNat
  rw [Finset.card_eq_sum_ones]
  rw [← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A supplied finite-grid cover turns every normalized overlap conflict into
membership in the corresponding literal containment test. -/
theorem normalizedConflictIndices_subset_hundredIndices_of_cover
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (omega : Fin repetitions -> motionChoice)
    (cover : Fin repetitions × iota -> testIndex)
    (hcover : forall a b,
      normalizedConflict
          (indexedRigidCopyDatum (fun j => motion (omega j)) D) b a ->
        (eighthNormalizedTube
          (rigidTube (motion (omega b.1))
            (D.family.tubes b.2))).carrier ⊆
          (hundredTube (testTube (cover a))).carrier)
    (a : Fin repetitions × iota) :
    normalizedConflictIndices
        (indexedRigidCopyDatum (fun j => motion (omega j)) D) a ⊆
      normalizedRigidCopyHundredIndices motion D testTube omega (cover a) := by
  classical
  intro b hb
  rw [normalizedConflictIndices, Finset.mem_filter] at hb
  rw [normalizedRigidCopyHundredIndices, Finset.mem_filter]
  exact ⟨Finset.mem_univ b, hcover a b hb.2⟩

/-- Consequently, a natural bound for all active grid loads is already the
uniform normalized-conflict cap required by fresh greedy selection. -/
theorem normalizedConflictIndices_card_le_of_gridCover
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions conflictThreshold : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (omega : Fin repetitions -> motionChoice)
    (cover : Fin repetitions × iota -> testIndex)
    (hcover : forall a b,
      normalizedConflict
          (indexedRigidCopyDatum (fun j => motion (omega j)) D) b a ->
        (eighthNormalizedTube
          (rigidTube (motion (omega b.1))
            (D.family.tubes b.2))).carrier ⊆
          (hundredTube (testTube (cover a))).carrier)
    (hload : forall a,
      (∑ j, normalizedRigidHundredLoadNat motion D testTube
        (cover a) (omega j)) <= conflictThreshold) :
    forall a,
      (normalizedConflictIndices
        (indexedRigidCopyDatum (fun j => motion (omega j)) D) a).card <=
          conflictThreshold := by
  intro a
  calc
    (normalizedConflictIndices
        (indexedRigidCopyDatum (fun j => motion (omega j)) D) a).card <=
        (normalizedRigidCopyHundredIndices
          motion D testTube omega (cover a)).card :=
      Finset.card_le_card
        (normalizedConflictIndices_subset_hundredIndices_of_cover
          motion D testTube omega cover hcover a)
    _ = ∑ j, normalizedRigidHundredLoadNat motion D testTube
          (cover a) (omega j) :=
      normalizedRigidCopyHundredIndices_card_eq_sum_load
        motion D testTube omega (cover a)
    _ <= conflictThreshold := hload a

/-- Complete finite-probability-to-conflict-cap connector.  It consumes the
literal finite-law choice-count estimate through the tail theorem and leaves
only the test-grid coverage producer as a separate geometric premise. -/
theorem exists_rigidMotionTuple_normalizedConflictIndices_card_le
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
    (repetitions conflictThreshold : Nat)
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
        Real.exp A)
    (hthreshold : forall K, K ∈ activeTests ->
      A * cap K <= (conflictThreshold : Real))
    (hgridCover : forall omega : Fin repetitions -> motionChoice,
      exists cover : Fin repetitions × iota -> testIndex,
        (forall a, cover a ∈ activeTests) ∧
        (forall a b,
          normalizedConflict
              (indexedRigidCopyDatum (fun j => motion (omega j)) D) b a ->
            (eighthNormalizedTube
              (rigidTube (motion (omega b.1))
                (D.family.tubes b.2))).carrier ⊆
              (hundredTube (testTube (cover a))).carrier)) :
    exists omega : Fin repetitions -> motionChoice,
        (forall K, K ∈ activeTests ->
          (∑ j,
            (normalizedRigidHundredLoadNat motion D testTube K
              (omega j) : Real)) <= A * cap K) ∧
        (forall a,
          (normalizedConflictIndices
            (indexedRigidCopyDatum (fun j => motion (omega j)) D) a).card <=
              conflictThreshold) := by
  obtain ⟨omega, htail⟩ :=
    exists_rigidMotionTuple_all_normalizedHundredLoads_le
      motion D testTube activeTests choiceBudget repetitions cap mean A
        hcap hmean hloadCap hchoice hbalance hscale htailRoom
  obtain ⟨cover, hcoverActive, hcover⟩ := hgridCover omega
  refine ⟨omega, htail, ?_⟩
  apply normalizedConflictIndices_card_le_of_gridCover
    motion D testTube omega cover hcover
  intro a
  have hreal :
      (∑ j,
        (normalizedRigidHundredLoadNat motion D testTube (cover a)
          (omega j) : Real)) <= (conflictThreshold : Real) :=
    (htail (cover a) (hcoverActive a)).trans
      (hthreshold (cover a) (hcoverActive a))
  have hcast :
      ((∑ j, normalizedRigidHundredLoadNat motion D testTube
        (cover a) (omega j) : Nat) : Real) <=
          (conflictThreshold : Real) := by
    simpa only [Nat.cast_sum] using hreal
  exact_mod_cast hcast

#print axioms normalizedRigidCopyHundredIndices_card_eq_sum_load
#print axioms normalizedConflictIndices_subset_hundredIndices_of_cover
#print axioms normalizedConflictIndices_card_le_of_gridCover
#print axioms exists_rigidMotionTuple_normalizedConflictIndices_card_le

end
end Family8FiniteRandomRigidMotionPaperConflictGridBridgeV1
