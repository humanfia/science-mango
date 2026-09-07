import Family8Grounding.Family8RestrictedSelectedMassOccupiedSameCoreSumV1
import Family8Grounding.Family8Prop51JointOccurrenceWeightedSelectionV1

/-!
# Weighted same-core selection in one occupied fibre-log bucket

The source of this selection is the finite set of occupied chosen greedy
occurrences, rather than all occurrence positions.  We bucket only by the
literal base-two logarithm of the occurrence-fibre cardinality.  Thus no
common density range and no canonical Proposition 5.1 bucket are needed.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8OccupiedSameCoreFiberLogWeightedSelectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8RestrictedSelectedMassOccupiedSameCoreSumV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- A nonzero selected mass has one occupied fibre-log bucket and one
maximal same-core member of that bucket.  The exact selected mass is retained
with the fibre-label count and the cardinality of the retained bucket as the
only losses. -/
theorem exists_occupiedCoreHighOccurrence_fiberLogBucket_weighted_sameQ
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (hselected0 :
      (restrictActualTubeDatum D selected).shading.shadingMass ≠ 0) :
    ∃ b : Fin (Nat.log 2 (Fintype.card index) + 1),
      let R := dyadicFiber
        (occupiedCoreHighOccurrences D P A selected hcover)
        (occurrenceFiberLogCardLabel P) b
      ∃ q, q ∈ R /\
        R ⊆ occupiedCoreHighOccurrences D P A selected hcover /\
        CoreHighConcentrationOccurrence D P A q /\
        (restrictActualTubeDatum D selected).shading.shadingMass ≤
          (((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal) *
            (R.card : ENNReal)) *
            (sameCoreOccurrenceBlockShading
              D P A selected hcover q).shadingMass /\
        ∀ k ∈ R,
          (((blockAt D.family.bodyFamily P q).fiber.card : Nat) : ENNReal) ≤
            2 *
              (((blockAt D.family.bodyFamily P k).fiber.card : Nat) :
                ENNReal) := by
  classical
  let O := occupiedCoreHighOccurrences D P A selected hcover
  let label := occurrenceFiberLogCardLabel P
  let weight : Fin (blocks D.family.bodyFamily P).length -> ENNReal :=
    fun q => (sameCoreOccurrenceBlockShading
      D P A selected hcover q).shadingMass
  obtain ⟨b, hb⟩ := exists_large_ennreal_finiteBucket O label weight
  let R := dyadicFiber O label b
  have hmassPartition :
      (restrictActualTubeDatum D selected).shading.shadingMass =
        ∑ q ∈ O, weight q := by
    simpa only [O, weight] using
      (restrictActualTubeDatum_shadingMass_eq_sum_occupied_sameCoreOccurrenceBlockShading
        D P A selected hcover)
  have hRnonempty : R.Nonempty := by
    by_contra hnot
    have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    apply hselected0
    apply le_antisymm
    · calc
        (restrictActualTubeDatum D selected).shading.shadingMass =
            ∑ q ∈ O, weight q := hmassPartition
        _ ≤ (Fintype.card
              (Fin (Nat.log 2 (Fintype.card index) + 1)) : ENNReal) *
              ∑ q ∈ R, weight q := by
            simpa only [R] using hb
        _ = 0 := by rw [hRempty]; simp
    · exact bot_le
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image R weight hRnonempty
  have hRsubset :
      R ⊆ occupiedCoreHighOccurrences D P A selected hcover := by
    intro k hk
    exact (mem_dyadicFiber O label b k).mp hk |>.1
  have hbucketWeight :
      (∑ k ∈ R, weight k) ≤ (R.card : ENNReal) * weight q := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul R weight (weight q)
        (fun k hk => hmax k hk))
  have hretained :
      (restrictActualTubeDatum D selected).shading.shadingMass ≤
        (((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal) *
          (R.card : ENNReal)) * weight q := by
    calc
      (restrictActualTubeDatum D selected).shading.shadingMass =
          ∑ k ∈ O, weight k := hmassPartition
      _ ≤ (Fintype.card
            (Fin (Nat.log 2 (Fintype.card index) + 1)) : ENNReal) *
            ∑ k ∈ R, weight k := by
          simpa only [R] using hb
      _ ≤ (Fintype.card
            (Fin (Nat.log 2 (Fintype.card index) + 1)) : ENNReal) *
            ((R.card : ENNReal) * weight q) :=
          mul_le_mul' le_rfl hbucketWeight
      _ = (((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal) *
            (R.card : ENNReal)) * weight q := by
          simp only [Fintype.card_fin]
          ac_rfl
  have huniform : ∀ k ∈ R,
      (((blockAt D.family.bodyFamily P q).fiber.card : Nat) : ENNReal) ≤
        2 * (((blockAt D.family.bodyFamily P k).fiber.card : Nat) :
          ENNReal) := by
    intro k hk
    have hqLabel : label q = b :=
      (mem_dyadicFiber O label b q).mp hq |>.2
    have hkLabel : label k = b :=
      (mem_dyadicFiber O label b k).mp hk |>.2
    exact occurrenceFiberCard_le_two_mul_of_logLabel_eq P q k
      (hqLabel.trans hkLabel.symm)
  refine ⟨b, q, hq, hRsubset, ?_, ?_, huniform⟩
  · exact coreHighOccurrence_of_mem_occupied
      D P A selected hcover (hRsubset hq)
  · simpa only [weight] using hretained

#print axioms
  exists_occupiedCoreHighOccurrence_fiberLogBucket_weighted_sameQ

end

end Family8OccupiedSameCoreFiberLogWeightedSelectionV1
