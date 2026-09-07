import Family8Grounding.Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
import Family8Grounding.Family8OccupiedSameCoreFiberLogWeightedSelectionV1
import Family8Grounding.Family8ArbitraryOccurrenceSameQCardBridgeV1

/-!
# Post-bucket same-q payload from the retained core-high prefix

This module performs only the occupied fibre-log selection following the
first-hit core-high prefix.  It retains the same greedy partition and selected
prefix, chooses no side-shape label, and exposes the exact coefficient in
which the retained bucket cardinality is reserved for the later plank count.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoreHighPrefixPostFiberLogSameQPayloadV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8ArbitraryOccurrenceSameQCardBridgeV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8OccupiedSameCoreFiberLogWeightedSelectionV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The exact post-fibre-bucket same-q payload.  The factor two is the
first-hit prefix loss, the logarithmic factor is the number of fibre-card
labels, and `R.card` remains the literal downstream plank count. -/
abbrev CoreHighPrefixPostFiberLogSameQPayload
    (D : ActualTubeDatum delta index) (A : ENNReal) : Prop :=
  exists P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ,
    exists selected : Finset index,
      exists hcover : (forall i, i ∈ selected ->
        exists q : Fin (blocks D.family.bodyFamily P).length,
          i ∈ (blockAt D.family.bodyFamily P q).fiber /\
            CoreHighConcentrationOccurrence D P A q),
        exists b : Fin (Nat.log 2 (Fintype.card index) + 1),
          let R := dyadicFiber
            (occupiedCoreHighOccurrences D P A selected hcover)
            (occurrenceFiberLogCardLabel P) b
          exists q : Fin (blocks D.family.bodyFamily P).length,
            q ∈ R /\
            R ⊆ occupiedCoreHighOccurrences D P A selected hcover /\
            CoreHighConcentrationOccurrence D P A q /\
            let Z := sameCoreOccurrenceBlockShading
              D P A selected hcover q
            let loss : ENNReal :=
              ((2 : ENNReal) *
                ((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal)) *
                (R.card : ENNReal)
            D.shading.shadingMass <= loss * Z.shadingMass /\
            D.shading.averageMultiplicity <=
              loss * Z.averageMultiplicity /\
            (forall k, k ∈ R ->
              (((blockAt D.family.bodyFamily P q).fiber.card : Nat) :
                  ENNReal) <=
                2 *
                  (((blockAt D.family.bodyFamily P k).fiber.card : Nat) :
                    ENNReal)) /\
            R.card * (blockAt D.family.bodyFamily P q).fiber.card <=
              2 * Fintype.card index

/-- A nonzero source turns the retained core-high prefix into the exact
post-fibre-bucket same-q payload.  No occurrence, bucket, or label is
reselected after the weighted selector returns `R` and `q`. -/
theorem coreHighPrefixWithFirstHitMass_to_postFiberLogSameQPayload
    (D : ActualTubeDatum delta index) (A : ENNReal)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hhigh : CoreHighPrefixWithFirstHitMass D A) :
    CoreHighPrefixPostFiberLogSameQPayload D A := by
  obtain ⟨P, selected, hfirst, hcover⟩ := hhigh
  have hselected0 :
      (restrictActualTubeDatum D selected).shading.shadingMass ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfirst
    exact hsource0 (bot_unique hfirst)
  obtain ⟨b, q, hq, hRsubset, hqHigh, hselectedMass, huniform⟩ :=
    exists_occupiedCoreHighOccurrence_fiberLogBucket_weighted_sameQ
      D P A selected hcover hselected0
  let R := dyadicFiber
    (occupiedCoreHighOccurrences D P A selected hcover)
    (occurrenceFiberLogCardLabel P) b
  let Z := sameCoreOccurrenceBlockShading D P A selected hcover q
  let loss : ENNReal :=
    ((2 : ENNReal) *
      ((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal)) *
      (R.card : ENNReal)
  have hsourceMass : D.shading.shadingMass <= loss * Z.shadingMass := by
    calc
      D.shading.shadingMass <=
          2 * (restrictActualTubeDatum D selected).shading.shadingMass :=
        hfirst
      _ <= 2 *
          ((((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal) *
              (R.card : ENNReal)) * Z.shadingMass) :=
        mul_le_mul' le_rfl hselectedMass
      _ = loss * Z.shadingMass := by
        simp only [loss]
        ac_rfl
  have hunion : Z.shadedUnion ⊆ D.shading.shadedUnion :=
    sameCoreOccurrenceBlockShading_shadedUnion_subset
      D P A selected hcover q
  have hsourceAverage : D.shading.averageMultiplicity <=
      loss * Z.averageMultiplicity := by
    unfold Shading.averageMultiplicity
    calc
      D.shading.shadingMass / volume D.shading.shadedUnion <=
          (loss * Z.shadingMass) / volume D.shading.shadedUnion :=
        ENNReal.div_le_div_right hsourceMass _
      _ <= (loss * Z.shadingMass) / volume Z.shadedUnion :=
        ENNReal.div_le_div_left (measure_mono hunion) _
      _ = loss * (Z.shadingMass / volume Z.shadedUnion) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  have hcountRaw :=
    arbitraryOccurrence_card_mul_sameQ_fiberCard_le_two_mul_active
      P R q hq huniform
  have hcount :
      R.card * (blockAt D.family.bodyFamily P q).fiber.card <=
        2 * Fintype.card index := by
    simpa only [Finset.card_univ] using hcountRaw
  exact ⟨P, selected, hcover, b, q, hq, hRsubset, hqHigh,
    hsourceMass, hsourceAverage, huniform, hcount⟩

#print axioms CoreHighPrefixPostFiberLogSameQPayload
#print axioms coreHighPrefixWithFirstHitMass_to_postFiberLogSameQPayload

end

end Family8CoreHighPrefixPostFiberLogSameQPayloadV1
