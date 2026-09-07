import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictGridBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperConflictMultiGridBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteRandomRigidMotionPaperConflictGridBridgeV1
open FamilyStickyRandomModelTubeCollisionGridV1

noncomputable section

/-!
# Honest finite multi-cover of a normalized conflict neighbourhood

A single unit-axis `100 delta` test does not cover every tube having more
than half-volume overlap with an anchor: longitudinally shifted unit tubes
give a genuine counterexample.  The correct finite seam assigns each anchor
a bounded Finset of longitudinally shifted tests.  Every conflict need only
land in one member of that Finset.

This file proves the exact bookkeeping after such a multi-cover.  The loss is
the transparent factor `coverMultiplicity`; no false one-test containment
statement is used.
-/

/-- A finite multi-cover of each anchor gives a literal Finset inclusion into
the union of its containment tests. -/
theorem normalizedConflictIndices_subset_biUnion_hundredIndices_of_multiCover
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    [DecidableEq testIndex]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (omega : Fin repetitions -> motionChoice)
    (cover : Fin repetitions × iota -> Finset testIndex)
    (hcover : forall a b,
      normalizedConflict
          (indexedRigidCopyDatum (fun j => motion (omega j)) D) b a ->
        exists K, K ∈ cover a ∧
          (eighthNormalizedTube
            (rigidTube (motion (omega b.1))
              (D.family.tubes b.2))).carrier ⊆
            (hundredTube (testTube K)).carrier)
    (a : Fin repetitions × iota) :
    normalizedConflictIndices
        (indexedRigidCopyDatum (fun j => motion (omega j)) D) a ⊆
      (cover a).biUnion fun K =>
        normalizedRigidCopyHundredIndices motion D testTube omega K := by
  classical
  intro b hb
  rw [normalizedConflictIndices, Finset.mem_filter] at hb
  obtain ⟨K, hK, hcontain⟩ := hcover a b hb.2
  apply Finset.mem_biUnion.mpr
  refine ⟨K, hK, ?_⟩
  rw [normalizedRigidCopyHundredIndices, Finset.mem_filter]
  exact ⟨Finset.mem_univ b, hcontain⟩

/-- Uniform single-test loads and a bounded multi-cover give the normalized
conflict cap with exactly the multiplicative cover loss. -/
theorem normalizedConflictIndices_card_le_of_multiGridCover
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    [DecidableEq testIndex]
    {delta : NNReal}
    {repetitions coverMultiplicity loadThreshold : Nat}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testTube : testIndex -> Tube (delta / 8))
    (activeTests : Finset testIndex)
    (omega : Fin repetitions -> motionChoice)
    (cover : Fin repetitions × iota -> Finset testIndex)
    (hcoverActive : forall a, cover a ⊆ activeTests)
    (hcoverCard : forall a, (cover a).card <= coverMultiplicity)
    (hcover : forall a b,
      normalizedConflict
          (indexedRigidCopyDatum (fun j => motion (omega j)) D) b a ->
        exists K, K ∈ cover a ∧
          (eighthNormalizedTube
            (rigidTube (motion (omega b.1))
              (D.family.tubes b.2))).carrier ⊆
            (hundredTube (testTube K)).carrier)
    (hload : forall K, K ∈ activeTests ->
      (∑ j, normalizedRigidHundredLoadNat motion D testTube K (omega j)) <=
        loadThreshold) :
    forall a,
      (normalizedConflictIndices
        (indexedRigidCopyDatum (fun j => motion (omega j)) D) a).card <=
          coverMultiplicity * loadThreshold := by
  intro a
  calc
    (normalizedConflictIndices
        (indexedRigidCopyDatum (fun j => motion (omega j)) D) a).card <=
        ((cover a).biUnion fun K =>
          normalizedRigidCopyHundredIndices motion D testTube omega K).card :=
      Finset.card_le_card
        (normalizedConflictIndices_subset_biUnion_hundredIndices_of_multiCover
          motion D testTube omega cover hcover a)
    _ <= ∑ K ∈ cover a,
        (normalizedRigidCopyHundredIndices
          motion D testTube omega K).card := Finset.card_biUnion_le
    _ = ∑ K ∈ cover a,
        ∑ j, normalizedRigidHundredLoadNat motion D testTube K (omega j) := by
      apply Finset.sum_congr rfl
      intro K _hK
      exact normalizedRigidCopyHundredIndices_card_eq_sum_load
        motion D testTube omega K
    _ <= ∑ _K ∈ cover a, loadThreshold := by
      apply Finset.sum_le_sum
      intro K hK
      exact hload K (hcoverActive a hK)
    _ = (cover a).card * loadThreshold := by simp
    _ <= coverMultiplicity * loadThreshold :=
      Nat.mul_le_mul_right loadThreshold (hcoverCard a)

/-- Full Chernoff-to-conflict-cap connector with a bounded finite multi-cover.
The two honest geometric inputs are now precisely the one-tube choice count
and the bounded shifted-test multi-cover. -/
theorem exists_rigidMotionTuple_normalizedConflictIndices_card_le_of_multiCover
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
    (repetitions coverMultiplicity loadThreshold : Nat)
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
      A * cap K <= (loadThreshold : Real))
    (hgridMultiCover : forall omega : Fin repetitions -> motionChoice,
      exists cover : Fin repetitions × iota -> Finset testIndex,
        (forall a, cover a ⊆ activeTests) ∧
        (forall a, (cover a).card <= coverMultiplicity) ∧
        (forall a b,
          normalizedConflict
              (indexedRigidCopyDatum (fun j => motion (omega j)) D) b a ->
            exists K, K ∈ cover a ∧
              (eighthNormalizedTube
                (rigidTube (motion (omega b.1))
                  (D.family.tubes b.2))).carrier ⊆
                (hundredTube (testTube K)).carrier)) :
    exists omega : Fin repetitions -> motionChoice,
      (forall K, K ∈ activeTests ->
        (∑ j,
          (normalizedRigidHundredLoadNat motion D testTube K
            (omega j) : Real)) <= A * cap K) ∧
      (forall a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum (fun j => motion (omega j)) D) a).card <=
            coverMultiplicity * loadThreshold) := by
  obtain ⟨omega, htail⟩ :=
    exists_rigidMotionTuple_all_normalizedHundredLoads_le
      motion D testTube activeTests choiceBudget repetitions cap mean A
        hcap hmean hloadCap hchoice hbalance hscale htailRoom
  obtain ⟨cover, hcoverActive, hcoverCard, hcover⟩ := hgridMultiCover omega
  refine ⟨omega, htail, ?_⟩
  apply normalizedConflictIndices_card_le_of_multiGridCover
    motion D testTube activeTests omega cover hcoverActive hcoverCard hcover
  intro K hK
  have hreal :
      (∑ j,
        (normalizedRigidHundredLoadNat motion D testTube K
          (omega j) : Real)) <= (loadThreshold : Real) :=
    (htail K hK).trans (hthreshold K hK)
  have hcast :
      ((∑ j, normalizedRigidHundredLoadNat motion D testTube K
        (omega j) : Nat) : Real) <= (loadThreshold : Real) := by
    simpa only [Nat.cast_sum] using hreal
  exact_mod_cast hcast

#print axioms normalizedConflictIndices_subset_biUnion_hundredIndices_of_multiCover
#print axioms normalizedConflictIndices_card_le_of_multiGridCover
#print axioms exists_rigidMotionTuple_normalizedConflictIndices_card_le_of_multiCover

end
end Family8FiniteRandomRigidMotionPaperConflictMultiGridBridgeV1
