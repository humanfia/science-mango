import Family8Grounding.Family8ArbitraryOccurrenceSameQCardBridgeV1
import Family8Grounding.Family8Prop51JointOccurrenceWeightedSelectionV1
import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Family8Grounding.Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
import Mathlib.Tactic

/-!
# Fine-shading retention in one core-high fibre-log bucket

The first-hit high prefix is bucketed on its selected fine indices, before a
maximal occurrence is chosen.  The bucket therefore retains the whole fine
mass assigned to one fibre-log label with only the number of labels as loss.
The corresponding occurrence set is kept intact for a later exact
factorization; no factor `R.card` occurs in the mass or average retention.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoreHighPrefixFiberLogBucketFineShadingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8ArbitraryOccurrenceSameQCardBridgeV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Fibre-log label of one selected fine index, through its fixed chosen
core-high occurrence. -/
def coreHighFiberLogFineLabel
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (i : {i // i ∈ selected}) :
    Fin (Nat.log 2 (Fintype.card index) + 1) :=
  occurrenceFiberLogCardLabel P
    (chosenCoreHighOccurrence D P A selected hcover i)

/-- Fine indices in one selected fibre-log bucket, returned on the original
index type. -/
noncomputable def coreHighFiberLogFineBucket
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1)) : Finset index := by
  classical
  exact (dyadicFiber (Finset.univ : Finset {i // i ∈ selected})
    (coreHighFiberLogFineLabel D P A selected hcover) b).image
      (fun i => i.1)

/-- Occurrences carrying the same fibre-log label as the retained fine
bucket. -/
noncomputable def coreHighFiberLogOccurrenceBucket
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1)) :
    Finset (Fin (blocks D.family.bodyFamily P).length) :=
  dyadicFiber (occupiedCoreHighOccurrences D P A selected hcover)
    (occurrenceFiberLogCardLabel P) b

/-- The source shading restricted to the retained fine fibre-log bucket. -/
noncomputable def coreHighFiberLogFineShading
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1)) :
    Shading D.family.bodyFamily :=
  (IndexedShadingRefinement.restrictTo D.shading
    (coreHighFiberLogFineBucket D P A selected hcover b)).shading

/-- The retained bucket shading has exactly the finite-subtype bucket mass. -/
theorem coreHighFiberLogFineShading_mass_eq
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1)) :
    (coreHighFiberLogFineShading D P A selected hcover b).shadingMass =
      ∑ i ∈ dyadicFiber (Finset.univ : Finset {i // i ∈ selected})
          (coreHighFiberLogFineLabel D P A selected hcover) b,
        volume (D.shading.carrier i.1) := by
  classical
  rw [coreHighFiberLogFineShading, shadingMass_restrictTo_eq_sum]
  unfold coreHighFiberLogFineBucket
  rw [Finset.sum_image]
  intro i _hi k _hk hik
  exact Subtype.ext hik

/-- Restricting to the fine bucket only shrinks the source shaded union. -/
theorem coreHighFiberLogFineShading_shadedUnion_subset
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1)) :
    (coreHighFiberLogFineShading D P A selected hcover b).shadedUnion ⊆
      D.shading.shadedUnion := by
  exact (IndexedShadingRefinement.restrictTo D.shading
    (coreHighFiberLogFineBucket D P A selected hcover b)).shadedUnion_subset

/-- Exact no-`R.card` payload kept after fine-index fibre-log bucketing. -/
abbrev CoreHighPrefixFiberLogBucketFineShadingPayload
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
          let R := coreHighFiberLogOccurrenceBucket
            D P A selected hcover b
          let fineBucket := coreHighFiberLogFineBucket
            D P A selected hcover b
          let Ybucket := coreHighFiberLogFineShading
            D P A selected hcover b
          R.Nonempty /\
          R ⊆ occupiedCoreHighOccurrences D P A selected hcover /\
          fineBucket ⊆ selectedOccurrenceFineIndices P R /\
          (forall q, q ∈ R -> CoreHighConcentrationOccurrence D P A q) /\
          (forall q, q ∈ R -> forall k, k ∈ R ->
            (((blockAt D.family.bodyFamily P q).fiber.card : Nat) :
                ENNReal) <=
              2 * (((blockAt D.family.bodyFamily P k).fiber.card : Nat) :
                ENNReal)) /\
          (forall q, q ∈ R ->
            R.card * (blockAt D.family.bodyFamily P q).fiber.card <=
              2 * Fintype.card index) /\
          D.shading.shadingMass <=
            (((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) :
                ENNReal) * Ybucket.shadingMass) /\
          D.shading.averageMultiplicity <=
            (((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) :
                ENNReal) * Ybucket.averageMultiplicity)

/-- The first-hit source mass admits a whole fine fibre-log bucket with no
linear loss in the number of occurrences in that bucket. -/
theorem coreHighPrefixWithFirstHitMass_to_fiberLogBucketFineShadingPayload
    (D : ActualTubeDatum delta index) (A : ENNReal)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hhigh : CoreHighPrefixWithFirstHitMass D A) :
    CoreHighPrefixFiberLogBucketFineShadingPayload D A := by
  classical
  obtain ⟨P, selected, hfirst, hcover⟩ := hhigh
  let source := (Finset.univ : Finset {i // i ∈ selected})
  let label := coreHighFiberLogFineLabel D P A selected hcover
  let weight : {i // i ∈ selected} -> ENNReal := fun i =>
    volume (D.shading.carrier i.1)
  obtain ⟨b, hb⟩ := exists_large_ennreal_finiteBucket source label weight
  let R := coreHighFiberLogOccurrenceBucket D P A selected hcover b
  let fineBucket := coreHighFiberLogFineBucket D P A selected hcover b
  let Ybucket := coreHighFiberLogFineShading D P A selected hcover b
  have hselectedMass :
      (restrictActualTubeDatum D selected).shading.shadingMass =
        ∑ i ∈ source, weight i := by
    dsimp only [source, weight]
    rw [restrictActualTubeDatum_shadingMass]
    exact (Finset.sum_attach selected
      (fun i => volume (D.shading.carrier i))).symm
  have hYbucketMass : Ybucket.shadingMass =
      ∑ i ∈ dyadicFiber source label b, weight i := by
    simpa only [Ybucket, source, label, weight] using
      (coreHighFiberLogFineShading_mass_eq D P A selected hcover b)
  have hselectedToBucket :
      (restrictActualTubeDatum D selected).shading.shadingMass <=
        (((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal) *
          Ybucket.shadingMass) := by
    calc
      (restrictActualTubeDatum D selected).shading.shadingMass =
          ∑ i ∈ source, weight i := hselectedMass
      _ <= (Fintype.card
            (Fin (Nat.log 2 (Fintype.card index) + 1)) : ENNReal) *
          ∑ i ∈ dyadicFiber source label b, weight i := hb
      _ = (((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal) *
          Ybucket.shadingMass) := by
        rw [<- hYbucketMass]
        simp only [Fintype.card_fin]
  have hmass : D.shading.shadingMass <=
      (((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) *
        Ybucket.shadingMass) := by
    calc
      D.shading.shadingMass <=
          2 * (restrictActualTubeDatum D selected).shading.shadingMass :=
        hfirst
      _ <= (2 : ENNReal) *
          ((((Nat.log 2 (Fintype.card index) + 1 : Nat) : ENNReal) *
            Ybucket.shadingMass)) := mul_le_mul' le_rfl hselectedToBucket
      _ = (((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) *
          Ybucket.shadingMass) := by
        norm_num [mul_assoc]
  have hYbucket0 : Ybucket.shadingMass ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmass
    exact hsource0 (bot_unique hmass)
  have hfineNonempty : fineBucket.Nonempty := by
    by_contra hnot
    have hempty : fineBucket = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    apply hYbucket0
    dsimp only [Ybucket]
    rw [coreHighFiberLogFineShading, show
      coreHighFiberLogFineBucket D P A selected hcover b = ∅ by
        simpa only [fineBucket] using hempty,
      shadingMass_restrictTo_eq_sum]
    simp
  have hchosenMemR : forall i,
      i ∈ dyadicFiber source label b ->
        chosenCoreHighOccurrence D P A selected hcover i ∈ R := by
    intro i hi
    have hqOccupied :
        chosenCoreHighOccurrence D P A selected hcover i ∈
          occupiedCoreHighOccurrences D P A selected hcover := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hqLabel : occurrenceFiberLogCardLabel P
        (chosenCoreHighOccurrence D P A selected hcover i) = b := by
      have hiLabel := (mem_dyadicFiber source label b i).mp hi |>.2
      simpa only [label, coreHighFiberLogFineLabel] using hiLabel
    exact (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceFiberLogCardLabel P) b _).mpr ⟨hqOccupied, hqLabel⟩
  have hRnonempty : R.Nonempty := by
    obtain ⟨i, hi⟩ := hfineNonempty
    have hiImage : i ∈ coreHighFiberLogFineBucket
        D P A selected hcover b := by
      simpa only [fineBucket] using hi
    unfold coreHighFiberLogFineBucket at hiImage
    obtain ⟨j, hj, _hji⟩ := Finset.mem_image.mp hiImage
    exact ⟨chosenCoreHighOccurrence D P A selected hcover j,
      hchosenMemR j (by simpa only [source, label] using hj)⟩
  have hRsubset :
      R ⊆ occupiedCoreHighOccurrences D P A selected hcover := by
    intro q hq
    exact (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceFiberLogCardLabel P) b q).mp hq |>.1
  have hfineSubset : fineBucket ⊆ selectedOccurrenceFineIndices P R := by
    intro i hi
    have hiImage : i ∈ coreHighFiberLogFineBucket
        D P A selected hcover b := by
      simpa only [fineBucket] using hi
    unfold coreHighFiberLogFineBucket at hiImage
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hiImage
    subst i
    let q := chosenCoreHighOccurrence D P A selected hcover j
    have hqR : q ∈ R := by
      exact hchosenMemR j (by simpa only [source, label] using hj)
    exact Finset.mem_biUnion.mpr ⟨q, hqR,
      chosenCoreHighOccurrence_mem_block D P A selected hcover j⟩
  have hcore : forall q, q ∈ R ->
      CoreHighConcentrationOccurrence D P A q := by
    intro q hq
    exact coreHighOccurrence_of_mem_occupied
      D P A selected hcover (hRsubset hq)
  have huniform : forall q, q ∈ R -> forall k, k ∈ R ->
      (((blockAt D.family.bodyFamily P q).fiber.card : Nat) : ENNReal) <=
        2 * (((blockAt D.family.bodyFamily P k).fiber.card : Nat) :
          ENNReal) := by
    intro q hq k hk
    have hqLabel := (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceFiberLogCardLabel P) b q).mp hq |>.2
    have hkLabel := (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceFiberLogCardLabel P) b k).mp hk |>.2
    exact occurrenceFiberCard_le_two_mul_of_logLabel_eq P q k
      (hqLabel.trans hkLabel.symm)
  have hcount : forall q, q ∈ R ->
      R.card * (blockAt D.family.bodyFamily P q).fiber.card <=
        2 * Fintype.card index := by
    intro q hq
    have hraw :=
      arbitraryOccurrence_card_mul_sameQ_fiberCard_le_two_mul_active
        P R q hq (huniform q hq)
    simpa only [Finset.card_univ] using hraw
  have hunion : Ybucket.shadedUnion ⊆ D.shading.shadedUnion := by
    simpa only [Ybucket] using
      (coreHighFiberLogFineShading_shadedUnion_subset
        D P A selected hcover b)
  have haverage : D.shading.averageMultiplicity <=
      (((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) *
        Ybucket.averageMultiplicity) := by
    unfold Shading.averageMultiplicity
    calc
      D.shading.shadingMass / volume D.shading.shadedUnion <=
          ((((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) :
              ENNReal) * Ybucket.shadingMass) /
            volume D.shading.shadedUnion) :=
        ENNReal.div_le_div_right hmass _
      _ <= ((((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) :
              ENNReal) * Ybucket.shadingMass) /
            volume Ybucket.shadedUnion) :=
        ENNReal.div_le_div_left (measure_mono hunion) _
      _ = (((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) :
              ENNReal) *
            (Ybucket.shadingMass / volume Ybucket.shadedUnion)) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  refine ⟨P, selected, hcover, b, ?_⟩
  dsimp only
  exact ⟨hRnonempty, hRsubset, hfineSubset, hcore, huniform,
    hcount, hmass, haverage⟩

#print axioms coreHighFiberLogFineShading_mass_eq
#print axioms coreHighFiberLogFineShading_shadedUnion_subset
#print axioms CoreHighPrefixFiberLogBucketFineShadingPayload
#print axioms
  coreHighPrefixWithFirstHitMass_to_fiberLogBucketFineShadingPayload

end
end Family8CoreHighPrefixFiberLogBucketFineShadingV1
