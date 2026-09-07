import Family8Grounding.Family8GreedyFirstLowDensityDichotomyV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyHighPrefixActualOccurrenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.GreedyLateTailRestart
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8GreedyFirstLowDensityDichotomyV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

/-!
# Identifying every fine index in the high greedy prefix

Membership in a restarted active set is exactly the inequality saying that
the restart occurrence is no later than the index's unique greedy occurrence.
Thus every fine index in the literal high prefix lies in an actual earlier
block.
-/

/-- An active fine index remains in the restart tail exactly when its unique
greedy occurrence is at or after the restart position. -/
theorem mem_activeAt_iff_le_locate
    {index candidate : Type} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) {candidates : Finset candidate}
    {container : candidate → ConvexBody Space} :
    ∀ {active : Finset index}
      (P : GreedyDensityPartition F candidates container active)
      (k : Fin (blocks F P).length) {i : index} (hi : i ∈ active),
      i ∈ activeAt F P k ↔ k <= locate F P hi
  | _, .empty, k, _, _ => Fin.elim0 k
  | active, .step choice hfiber tail, k, i, hi => by
      induction k using Fin.cases with
      | zero =>
          change i ∈ active ↔ (0 : Nat) <= (locate F
            (.step choice hfiber tail) hi).val
          exact ⟨fun _ => Nat.zero_le _, fun _ => hi⟩
      | succ kprime =>
          by_cases hifiber : i ∈ choice.fiber
          · have hnotTail : i ∉ activeAt F tail kprime := by
              intro hitail
              have hiSdiff : i ∈ active \ choice.fiber :=
                activeAt_subset F tail kprime (fun _ h => h) hitail
              exact (Finset.mem_sdiff.mp hiSdiff).2 hifiber
            change i ∈ activeAt F tail kprime ↔
              kprime.val + 1 <= (locate F
                (.step choice hfiber tail) hi).val
            constructor
            · exact fun hitail => (hnotTail hitail).elim
            · intro hle
              simp [locate, hifiber] at hle
          · have hitail : i ∈ active \ choice.fiber :=
              Finset.mem_sdiff.mpr ⟨hi, hifiber⟩
            have ih := mem_activeAt_iff_le_locate F tail kprime hitail
            change i ∈ activeAt F tail kprime ↔
              kprime.val + 1 <= (locate F
                (.step choice hfiber tail) hi).val
            rw [ih]
            simp [locate, hifiber]

/-- Every fine index in the literal prefix before a restart belongs to an
actual block whose occurrence is strictly earlier than the restart. -/
theorem exists_prior_block_of_mem_sdiff_activeAt
    {index candidate : Type} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) {candidates : Finset candidate}
    {container : candidate → ConvexBody Space} {active : Finset index}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) {i : index}
    (hi : i ∈ active \ activeAt F P k) :
    ∃ q : Fin (blocks F P).length,
      q < k ∧ i ∈ (blockAt F P q).fiber := by
  have hiactive : i ∈ active := (Finset.mem_sdiff.mp hi).1
  let q := locate F P hiactive
  have hnotTail : i ∉ activeAt F P k := (Finset.mem_sdiff.mp hi).2
  have hnotLe : ¬ k <= q := by
    intro hkq
    exact hnotTail ((mem_activeAt_iff_le_locate F P k hiactive).mpr hkq)
  have hqk : q < k := lt_of_not_ge hnotLe
  exact ⟨q, hqk, mem_blockAt_locate F P hiactive⟩

/-- One exact greedy occurrence is an honest actual high-concentration
restriction in its winning convex body. -/
def ActualHighConcentrationOccurrence
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks D.family.bodyFamily P).length) : Prop :=
  A < blockDensity D.family.bodyFamily
      (blockAt D.family.bodyFamily P q) ∧
    (restrictActualTubeDatum D
      (blockAt D.family.bodyFamily P q).fiber).IsAdmissible ∧
    IsFrostmanIn 1
      (restrictActualTubeDatum D
        (blockAt D.family.bodyFamily P q).fiber).family.bodyFamily
      (blockAt D.family.bodyFamily P q).body

/-- A high-density inequality constructs the full actual occurrence
certificate. -/
theorem actualHighConcentrationOccurrence_of_density_gt
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks D.family.bodyFamily P).length)
    (hhigh : A < blockDensity D.family.bodyFamily
      (blockAt D.family.bodyFamily P q)) :
    ActualHighConcentrationOccurrence D P A q := by
  refine ⟨hhigh, ?_, ?_⟩
  · exact
      Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hD (blockAt D.family.bodyFamily P q).fiber
  · apply isFrostmanIn_restrictActualTubeDatum_of_isFrostmanOn
    exact blockAt_isFrostmanOn_one_of_subset
      D.family.bodyFamily Finset.univ P (fun _ hi => hi) q

/-- Strengthened honest dichotomy: every selected fine index in the high
branch belongs to an actual high-density greedy occurrence, and that occurrence
carries an actual admissible constant-one Frostman restriction. -/
theorem exists_factorTwo_lowKatzTaoRestriction_or_actualHighOccurrencePrefix
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible) (A : ENNReal) :
    (∃ selected : Finset index,
        D.shading.shadingMass <= 2 *
          (restrictActualTubeDatum D selected).shading.shadingMass ∧
        D.shading.averageMultiplicity <= 2 *
          (restrictActualTubeDatum D selected).shading.averageMultiplicity ∧
        (restrictActualTubeDatum D selected).IsAdmissible ∧
        IsKatzTao A
          (restrictActualTubeDatum D selected).family.bodyFamily) ∨
      ∃ P : GreedyDensityPartition D.family.bodyFamily
          (hullCandidates (Finset.univ : Finset index))
          (hullContainer D.family.bodyFamily) Finset.univ,
        ∃ selected : Finset index,
          D.shading.shadingMass <= 2 *
            (restrictActualTubeDatum D selected).shading.shadingMass ∧
          D.shading.averageMultiplicity <= 2 *
            (restrictActualTubeDatum D selected).shading.averageMultiplicity ∧
          (restrictActualTubeDatum D selected).IsAdmissible ∧
          ∀ i ∈ selected,
            ∃ q : Fin (blocks D.family.bodyFamily P).length,
              i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
              ActualHighConcentrationOccurrence D P A q := by
  classical
  rcases exists_factorTwo_lowKatzTaoRestriction_or_highConcentrationPrefix
      D hD A with hlow | hhigh
  · exact Or.inl hlow
  · right
    obtain ⟨P, selected, hmass, havg, hadmissible, hshape⟩ := hhigh
    refine ⟨P, selected, hmass, havg, hadmissible, ?_⟩
    rcases hshape with hall | hcut
    · obtain ⟨rfl, hallHigh⟩ := hall
      intro i hi
      let q := locate D.family.bodyFamily P hi
      exact ⟨q, mem_blockAt_locate D.family.bodyFamily P hi,
        actualHighConcentrationOccurrence_of_density_gt
          D hD P A q (hallHigh q)⟩
    · obtain ⟨k0, rfl, _hk0low, hprior⟩ := hcut
      intro i hi
      obtain ⟨q, hqk, hiq⟩ :=
        exists_prior_block_of_mem_sdiff_activeAt
          D.family.bodyFamily P k0 hi
      exact ⟨q, hiq,
        actualHighConcentrationOccurrence_of_density_gt
          D hD P A q (hprior q hqk)⟩

#print axioms mem_activeAt_iff_le_locate
#print axioms exists_prior_block_of_mem_sdiff_activeAt
#print axioms ActualHighConcentrationOccurrence
#print axioms actualHighConcentrationOccurrence_of_density_gt
#print axioms exists_factorTwo_lowKatzTaoRestriction_or_actualHighOccurrencePrefix

end
end Family8GreedyHighPrefixActualOccurrenceV1
