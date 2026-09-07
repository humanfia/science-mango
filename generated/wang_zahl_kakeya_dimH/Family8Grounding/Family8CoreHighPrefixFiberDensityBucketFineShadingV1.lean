import Family8Grounding.Family8CoreHighPrefixFiberLogBucketFineShadingV1
import Mathlib.Tactic

/-!
# Fine-shading retention in one joint fibre-density bucket

This successor refines the first-hit selected fine indices by the product of
their chosen occurrence's fibre-log label and literal block-density dyadic
label.  The whole fine bucket is retained before any occurrence is selected,
so the loss is only twice the finite joint-label count and contains no factor
depending on the number of retained occurrences.

The density label is total and uses a default value outside its advertised
range.  Consequently the one genuinely necessary extra input is an occupied-
occurrence density-band cover.  No range hypothesis is imposed on unoccupied
greedy blocks.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoreHighPrefixFiberDensityBucketFineShadingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8CoreHighPrefixFiberLogBucketFineShadingV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Joint fibre-log and density-band label of one selected fine index. -/
def coreHighFiberDensityJointFineLabel
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A base : ENNReal) (M : Nat) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (i : {i // i ∈ selected}) :
    Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1) :=
  occurrenceJointDyadicLabel P base M
    (chosenCoreHighOccurrence D P A selected hcover i)

/-- Original fine indices whose chosen occurrence has the selected joint
label. -/
noncomputable def coreHighFiberDensityFineBucket
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A base : ENNReal) (M : Nat) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1)) :
    Finset index := by
  classical
  exact (dyadicFiber (Finset.univ : Finset {i // i ∈ selected})
    (coreHighFiberDensityJointFineLabel
      D P A base M selected hcover) b).image (fun i => i.1)

/-- Occupied occurrences having the selected joint fibre-density label. -/
noncomputable def coreHighFiberDensityOccurrenceBucket
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A base : ENNReal) (M : Nat) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1)) :
    Finset (Fin (blocks D.family.bodyFamily P).length) :=
  dyadicFiber (occupiedCoreHighOccurrences D P A selected hcover)
    (occurrenceJointDyadicLabel P base M) b

/-- Source shading restricted to the retained joint fine bucket. -/
noncomputable def coreHighFiberDensityFineShading
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A base : ENNReal) (M : Nat) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1)) :
    Shading D.family.bodyFamily :=
  (IndexedShadingRefinement.restrictTo D.shading
    (coreHighFiberDensityFineBucket
      D P A base M selected hcover b)).shading

/-- Exact mass of the joint fine-bucket restriction. -/
theorem coreHighFiberDensityFineShading_mass_eq
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A base : ENNReal) (M : Nat) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1)) :
    (coreHighFiberDensityFineShading
      D P A base M selected hcover b).shadingMass =
      ∑ i ∈ dyadicFiber (Finset.univ : Finset {i // i ∈ selected})
          (coreHighFiberDensityJointFineLabel
            D P A base M selected hcover) b,
        volume (D.shading.carrier i.1) := by
  classical
  rw [coreHighFiberDensityFineShading, shadingMass_restrictTo_eq_sum]
  unfold coreHighFiberDensityFineBucket
  rw [Finset.sum_image]
  intro i _hi k _hk hik
  exact Subtype.ext hik

/-- The joint bucket restriction only shrinks the source shaded union. -/
theorem coreHighFiberDensityFineShading_shadedUnion_subset
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A base : ENNReal) (M : Nat) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P A q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1)) :
    (coreHighFiberDensityFineShading
      D P A base M selected hcover b).shadedUnion ⊆
      D.shading.shadedUnion := by
  exact (IndexedShadingRefinement.restrictTo D.shading
    (coreHighFiberDensityFineBucket
      D P A base M selected hcover b)).shadedUnion_subset

/-- First-hit high-prefix data together with the exact occupied-only density
range needed to interpret the total density label. -/
abbrev CoreHighPrefixWithFirstHitMassDensityCovered
    (D : ActualTubeDatum delta index) (A base : ENNReal) (M : Nat) : Prop :=
  exists P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ,
    exists selected : Finset index,
      exists hcover : (forall i, i ∈ selected ->
        exists q : Fin (blocks D.family.bodyFamily P).length,
          i ∈ (blockAt D.family.bodyFamily P q).fiber /\
            CoreHighConcentrationOccurrence D P A q),
        D.shading.shadingMass <= 2 *
            (restrictActualTubeDatum D selected).shading.shadingMass /\
          forall q, q ∈ occupiedCoreHighOccurrences
              D P A selected hcover ->
            exists n, n <= M /\
              InENNRealDyadicBand base n
                (blockDensity D.family.bodyFamily
                  (blockAt D.family.bodyFamily P q))

/-- Whole-bucket joint fibre-density output.  Pairwise comparison is stated
in one direction for arbitrary ordered pairs, hence supplies both directions
without duplicating fields. -/
abbrev CoreHighPrefixFiberDensityBucketFineShadingPayload
    (D : ActualTubeDatum delta index) (A base : ENNReal) (M : Nat) : Prop :=
  exists P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ,
    exists selected : Finset index,
      exists hcover : (forall i, i ∈ selected ->
        exists q : Fin (blocks D.family.bodyFamily P).length,
          i ∈ (blockAt D.family.bodyFamily P q).fiber /\
            CoreHighConcentrationOccurrence D P A q),
        exists b : Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1),
          let R := coreHighFiberDensityOccurrenceBucket
            D P A base M selected hcover b
          let fineBucket := coreHighFiberDensityFineBucket
            D P A base M selected hcover b
          let Ybucket := coreHighFiberDensityFineShading
            D P A base M selected hcover b
          R.Nonempty /\
          R ⊆ occupiedCoreHighOccurrences D P A selected hcover /\
          fineBucket ⊆ selectedOccurrenceFineIndices P R /\
          (forall q, q ∈ R -> CoreHighConcentrationOccurrence D P A q) /\
          (forall q, q ∈ R ->
            InENNRealDyadicBand base b.2.1
              (blockDensity D.family.bodyFamily
                (blockAt D.family.bodyFamily P q))) /\
          (forall q, q ∈ R -> forall k, k ∈ R ->
            ((((blockAt D.family.bodyFamily P q).fiber.card : Nat) :
                ENNReal) <=
                2 * (((blockAt D.family.bodyFamily P k).fiber.card : Nat) :
                  ENNReal) /\
              blockDensity D.family.bodyFamily
                  (blockAt D.family.bodyFamily P q) <=
                2 * blockDensity D.family.bodyFamily
                  (blockAt D.family.bodyFamily P k))) /\
          D.shading.shadingMass <=
            (((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
              Ybucket.shadingMass) /\
          D.shading.averageMultiplicity <=
            (((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
              Ybucket.averageMultiplicity)

/-- Jointly bucket the first-hit fine indices, retaining their full bucket
mass and average with exactly twice the joint label count. -/
theorem coreHighPrefixWithFirstHitMassDensityCovered_to_fiberDensityBucketFineShadingPayload
    (D : ActualTubeDatum delta index) (A base : ENNReal) (M : Nat)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hhigh : CoreHighPrefixWithFirstHitMassDensityCovered D A base M) :
    CoreHighPrefixFiberDensityBucketFineShadingPayload D A base M := by
  classical
  obtain ⟨P, selected, hcover, hfirst, hcovered⟩ := hhigh
  let source := (Finset.univ : Finset {i // i ∈ selected})
  let label := coreHighFiberDensityJointFineLabel
    D P A base M selected hcover
  let weight : {i // i ∈ selected} -> ENNReal := fun i =>
    volume (D.shading.carrier i.1)
  obtain ⟨b, hb⟩ := exists_large_ennreal_finiteBucket source label weight
  let R := coreHighFiberDensityOccurrenceBucket
    D P A base M selected hcover b
  let fineBucket := coreHighFiberDensityFineBucket
    D P A base M selected hcover b
  let Ybucket := coreHighFiberDensityFineShading
    D P A base M selected hcover b
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
      (coreHighFiberDensityFineShading_mass_eq
        D P A base M selected hcover b)
  have hselectedToBucket :
      (restrictActualTubeDatum D selected).shading.shadingMass <=
        ((prop51JointOccurrenceLoss index M : ENNReal) *
          Ybucket.shadingMass) := by
    calc
      (restrictActualTubeDatum D selected).shading.shadingMass =
          ∑ i ∈ source, weight i := hselectedMass
      _ <= (Fintype.card
            (Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1)) :
              ENNReal) *
          ∑ i ∈ dyadicFiber source label b, weight i := hb
      _ = ((prop51JointOccurrenceLoss index M : ENNReal) *
          Ybucket.shadingMass) := by
        rw [<- hYbucketMass]
        simp [prop51JointOccurrenceLoss]
  have hmass : D.shading.shadingMass <=
      (((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
        Ybucket.shadingMass) := by
    calc
      D.shading.shadingMass <=
          2 * (restrictActualTubeDatum D selected).shading.shadingMass :=
        hfirst
      _ <= (2 : ENNReal) *
          ((prop51JointOccurrenceLoss index M : ENNReal) *
            Ybucket.shadingMass) := mul_le_mul' le_rfl hselectedToBucket
      _ = (((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
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
    rw [coreHighFiberDensityFineShading, show
      coreHighFiberDensityFineBucket D P A base M selected hcover b = ∅ by
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
    have hqLabel : occurrenceJointDyadicLabel P base M
        (chosenCoreHighOccurrence D P A selected hcover i) = b := by
      have hiLabel := (mem_dyadicFiber source label b i).mp hi |>.2
      simpa only [label, coreHighFiberDensityJointFineLabel] using hiLabel
    exact (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceJointDyadicLabel P base M) b _).mpr
        ⟨hqOccupied, hqLabel⟩
  have hRnonempty : R.Nonempty := by
    obtain ⟨i, hi⟩ := hfineNonempty
    have hiImage : i ∈ coreHighFiberDensityFineBucket
        D P A base M selected hcover b := by
      simpa only [fineBucket] using hi
    unfold coreHighFiberDensityFineBucket at hiImage
    obtain ⟨j, hj, _hji⟩ := Finset.mem_image.mp hiImage
    exact ⟨chosenCoreHighOccurrence D P A selected hcover j,
      hchosenMemR j (by simpa only [source, label] using hj)⟩
  have hRsubset :
      R ⊆ occupiedCoreHighOccurrences D P A selected hcover := by
    intro q hq
    exact (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceJointDyadicLabel P base M) b q).mp hq |>.1
  have hfineSubset : fineBucket ⊆ selectedOccurrenceFineIndices P R := by
    intro i hi
    have hiImage : i ∈ coreHighFiberDensityFineBucket
        D P A base M selected hcover b := by
      simpa only [fineBucket] using hi
    unfold coreHighFiberDensityFineBucket at hiImage
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
  have hband : forall q, q ∈ R ->
      InENNRealDyadicBand base b.2.1
        (blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q)) := by
    intro q hq
    have hspec := ennrealDyadicLabel_spec
      (hcovered q (hRsubset hq))
    have hqLabel := (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceJointDyadicLabel P base M) b q).mp hq |>.2
    have hdensityLabel : occurrenceDensityDyadicLabel P base M q = b.2 :=
      congrArg Prod.snd hqLabel
    have hdensityVal :
        (ennrealDyadicLabel base M
          (blockDensity D.family.bodyFamily
            (blockAt D.family.bodyFamily P q))).1 = b.2.1 := by
      simpa [occurrenceDensityDyadicLabel] using
        congrArg Fin.val hdensityLabel
    rw [hdensityVal] at hspec
    exact hspec
  have hcomparable : forall q, q ∈ R -> forall k, k ∈ R ->
      ((((blockAt D.family.bodyFamily P q).fiber.card : Nat) : ENNReal) <=
          2 * (((blockAt D.family.bodyFamily P k).fiber.card : Nat) :
            ENNReal) /\
        blockDensity D.family.bodyFamily
            (blockAt D.family.bodyFamily P q) <=
          2 * blockDensity D.family.bodyFamily
            (blockAt D.family.bodyFamily P k)) := by
    intro q hq k hk
    have hqLabel := (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceJointDyadicLabel P base M) b q).mp hq |>.2
    have hkLabel := (mem_dyadicFiber
      (occupiedCoreHighOccurrences D P A selected hcover)
      (occurrenceJointDyadicLabel P base M) b k).mp hk |>.2
    refine ⟨occurrenceFiberCard_le_two_mul_of_logLabel_eq P q k
      ((congrArg Prod.fst hqLabel).trans
        (congrArg Prod.fst hkLabel).symm), ?_⟩
    calc
      blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) <=
          (2 : ENNReal) ^ (b.2.1 + 1) * base := (hband q hq).2.le
      _ = 2 * ((2 : ENNReal) ^ b.2.1 * base) := by
        rw [pow_succ]
        ac_rfl
      _ <= 2 * blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P k) :=
        mul_le_mul' le_rfl (hband k hk).1
  have hunion : Ybucket.shadedUnion ⊆ D.shading.shadedUnion := by
    simpa only [Ybucket] using
      (coreHighFiberDensityFineShading_shadedUnion_subset
        D P A base M selected hcover b)
  have haverage : D.shading.averageMultiplicity <=
      (((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
        Ybucket.averageMultiplicity) := by
    unfold Shading.averageMultiplicity
    calc
      D.shading.shadingMass / volume D.shading.shadedUnion <=
          ((((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
              Ybucket.shadingMass) / volume D.shading.shadedUnion) :=
        ENNReal.div_le_div_right hmass _
      _ <= ((((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
              Ybucket.shadingMass) / volume Ybucket.shadedUnion) :=
        ENNReal.div_le_div_left (measure_mono hunion) _
      _ = (((2 * prop51JointOccurrenceLoss index M : Nat) : ENNReal) *
            (Ybucket.shadingMass / volume Ybucket.shadedUnion)) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  refine ⟨P, selected, hcover, b, ?_⟩
  dsimp only
  exact ⟨hRnonempty, hRsubset, hfineSubset, hcore, hband,
    hcomparable, hmass, haverage⟩

#print axioms coreHighFiberDensityFineShading_mass_eq
#print axioms coreHighFiberDensityFineShading_shadedUnion_subset
#print axioms CoreHighPrefixWithFirstHitMassDensityCovered
#print axioms CoreHighPrefixFiberDensityBucketFineShadingPayload
#print axioms
  coreHighPrefixWithFirstHitMassDensityCovered_to_fiberDensityBucketFineShadingPayload

end
end Family8CoreHighPrefixFiberDensityBucketFineShadingV1
