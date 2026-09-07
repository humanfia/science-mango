import Family8Grounding.Family8GreedyHighPrefixActualOccurrenceV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement
import Mathlib.Tactic

/-!
# Weighted selection of one actual high greedy occurrence

The high-prefix dichotomy supplies a selected set of source indices and, for
each selected index, at least one *actual* high greedy occurrence containing
it.  This file chooses one such occurrence for each selected index and runs a
single finite weighted pigeonhole with the literal shading-piece masses.

The retained indices need only be contained in the winning occurrence fibre;
they are not required to equal that fibre.  To match the arbitrary-block
Cordoba API, the retained shading is represented on the whole winning block
family, with zero carriers outside the retained bucket.  The only new loss is
the number of certified high-occurrence labels.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyHighPrefixSameOccurrenceWeightedMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The finite label type consisting only of genuinely certified high greedy
occurrences.  Using this subtype, rather than every greedy occurrence, avoids
paying for labels which cannot occur in the selected high prefix. -/
abbrev CertifiedHighOccurrenceLabel
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) : Type :=
  {q : Fin (blocks D.family.bodyFamily P).length //
    ActualHighConcentrationOccurrence D P A q}

/-- Choose one certified containing occurrence for each selected source
index.  No uniqueness or disjointness assumption is used. -/
noncomputable def chosenCertifiedHighOccurrence
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (i : {i // i ∈ selected}) : CertifiedHighOccurrenceLabel D P A :=
  ⟨Classical.choose (hcover i.1 i.2),
    (Classical.choose_spec (hcover i.1 i.2)).2⟩

/-- The chosen occurrence contains the source index which chose it. -/
theorem chosenCertifiedHighOccurrence_mem_block
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (i : {i // i ∈ selected}) :
    i.1 ∈ (blockAt D.family.bodyFamily P
      (chosenCertifiedHighOccurrence D P A selected hcover i).1).fiber := by
  exact (Classical.choose_spec (hcover i.1 i.2)).1

/-- The literal fibre, inside the winning block subtype, of one chosen
high-occurrence label. -/
noncomputable def sameOccurrenceBlockBucket
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (q : CertifiedHighOccurrenceLabel D P A) :
    Finset {i // i ∈ (blockAt D.family.bodyFamily P q.1).fiber} := by
  classical
  let source := (Finset.univ : Finset {i // i ∈ selected})
  let label := chosenCertifiedHighOccurrence D P A selected hcover
  let selectedFiber := dyadicFiber source label q
  exact selectedFiber.attach.image fun i =>
    ⟨i.1.1, by
      have hiLabel : label i.1 = q :=
        (mem_dyadicFiber source label q i.1).mp i.2 |>.2
      have hiBlock := chosenCertifiedHighOccurrence_mem_block
        D P A selected hcover i.1
      simpa only [label, hiLabel] using hiBlock⟩

/-- The finite set of certified occurrence labels actually chosen by at least
one selected source index.  This occupied count is the sharp pigeonhole loss;
unoccupied high occurrences are not charged. -/
noncomputable def occupiedCertifiedHighOccurrences
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q) :
    Finset (CertifiedHighOccurrenceLabel D P A) := by
  classical
  exact (Finset.univ : Finset {i // i ∈ selected}).image
    (chosenCertifiedHighOccurrence D P A selected hcover)

/-- The retained bucket as a shading on the whole winning block family.
Indices outside the bucket have empty carrier through `restrictTo`; hence this
is accepted directly by arbitrary-block Cordoba without asserting that the
bucket equals the greedy block. -/
noncomputable def sameOccurrenceBlockShading
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (q : CertifiedHighOccurrenceLabel D P A) :
    Shading (selectedCoarseFamily D.family.bodyFamily
      (blockAt D.family.bodyFamily P q.1).fiber) :=
  (IndexedShadingRefinement.restrictTo
    (selectedCoarseShading D.shading
      (blockAt D.family.bodyFamily P q.1).fiber)
    (sameOccurrenceBlockBucket D P A selected hcover q)).shading

/-- The zero-extended winning-block shading has exactly the weighted mass of
the chosen-label fibre in the selected set. -/
theorem sameOccurrenceBlockShading_mass_eq
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (q : CertifiedHighOccurrenceLabel D P A) :
    (sameOccurrenceBlockShading D P A selected hcover q).shadingMass =
      ∑ i ∈ dyadicFiber
          (Finset.univ : Finset {i // i ∈ selected})
          (chosenCertifiedHighOccurrence D P A selected hcover) q,
        volume (D.shading.carrier i.1) := by
  classical
  rw [sameOccurrenceBlockShading, shadingMass_restrictTo_eq_sum]
  simp only [selectedCoarseShading_carrier]
  rw [sameOccurrenceBlockBucket]
  rw [Finset.sum_image]
  · simpa only using
      (Finset.sum_attach
        (dyadicFiber
          (Finset.univ : Finset {i // i ∈ selected})
          (chosenCertifiedHighOccurrence D P A selected hcover) q)
        (fun i => volume (D.shading.carrier i.1)))
  · intro a _ha b _hb hab
    have habVal : a.1.1 = b.1.1 := congrArg (fun z => z.1) hab
    exact Subtype.ext (Subtype.ext habVal)

/-- The retained zero-extended shading has shaded union contained in the
source shaded union. -/
theorem sameOccurrenceBlockShading_shadedUnion_subset
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (q : CertifiedHighOccurrenceLabel D P A) :
    (sameOccurrenceBlockShading D P A selected hcover q).shadedUnion ⊆
      D.shading.shadedUnion := by
  let blockShading := selectedCoarseShading D.shading
    (blockAt D.family.bodyFamily P q.1).fiber
  have hrestricted :
      (sameOccurrenceBlockShading D P A selected hcover q).shadedUnion ⊆
        blockShading.shadedUnion := by
    exact (IndexedShadingRefinement.restrictTo blockShading
      (sameOccurrenceBlockBucket D P A selected hcover q)).shadedUnion_subset
  intro x hx
  have hxBlock := hrestricted hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxBlock
  exact Set.mem_iUnion.mpr ⟨i.1, hxi⟩

/-- A single same-occurrence bucket retains the selected shading mass with
the exact number of *occupied* certified high-occurrence labels.  Composing
an existing source-to-selected weighted loss gives both mass and
average-multiplicity retention into the zero-extended shading consumed by
arbitrary-block Cordoba. -/
theorem exists_sameOccurrenceBlockShading_weighted_retention
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hselected : selected.Nonempty)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (firstLoss : ENNReal)
    (hfirst : D.shading.shadingMass ≤ firstLoss *
      (restrictActualTubeDatum D selected).shading.shadingMass) :
    ∃ q : CertifiedHighOccurrenceLabel D P A,
      q ∈ occupiedCertifiedHighOccurrences D P A selected hcover ∧
      (restrictActualTubeDatum D selected).shading.shadingMass ≤
          ((occupiedCertifiedHighOccurrences
            D P A selected hcover).card : ENNReal) *
            (sameOccurrenceBlockShading D P A selected hcover q).shadingMass ∧
      D.shading.shadingMass ≤
          (firstLoss *
            ((occupiedCertifiedHighOccurrences
              D P A selected hcover).card : ENNReal)) *
            (sameOccurrenceBlockShading D P A selected hcover q).shadingMass ∧
      D.shading.averageMultiplicity ≤
          (firstLoss *
            ((occupiedCertifiedHighOccurrences
              D P A selected hcover).card : ENNReal)) *
            (sameOccurrenceBlockShading D P A selected hcover q).averageMultiplicity := by
  classical
  let source := (Finset.univ : Finset {i // i ∈ selected})
  let label := chosenCertifiedHighOccurrence D P A selected hcover
  let labels := occupiedCertifiedHighOccurrences D P A selected hcover
  let weight : {i // i ∈ selected} → ENNReal := fun i =>
    volume (D.shading.carrier i.1)
  let fiberWeight : CertifiedHighOccurrenceLabel D P A → ENNReal := fun q =>
    ∑ i ∈ dyadicFiber source label q, weight i
  have hlabels : labels.Nonempty := by
    let i0 : {i // i ∈ selected} :=
      ⟨hselected.choose, hselected.choose_spec⟩
    refine ⟨label i0, ?_⟩
    exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩
  obtain ⟨q, hq, hmax⟩ :=
    Finset.exists_max_image labels fiberWeight hlabels
  have hmaps : ∀ i ∈ source, label i ∈ labels := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hpartition :
      (∑ i ∈ source, weight i) =
        ∑ q' ∈ labels, fiberWeight q' := by
    change (∑ i ∈ source, weight i) =
      ∑ q' ∈ labels, ∑ i ∈ source with label i = q', weight i
    exact (Finset.sum_fiberwise_of_maps_to
      (s := source) (t := labels) (g := label) hmaps weight).symm
  have hweighted :
      (∑ i ∈ source, weight i) ≤ labels.card • fiberWeight q := by
    calc
      (∑ i ∈ source, weight i) =
          ∑ q' ∈ labels, fiberWeight q' := hpartition
      _ ≤ labels.card • fiberWeight q :=
        Finset.sum_le_card_nsmul labels fiberWeight (fiberWeight q)
          (fun q' hq' => hmax q' hq')
  have hselectedMass :
      (restrictActualTubeDatum D selected).shading.shadingMass =
        ∑ i ∈ (Finset.univ : Finset {i // i ∈ selected}),
          volume (D.shading.carrier i.1) := by
    rw [restrictActualTubeDatum_shadingMass]
    exact (Finset.sum_attach selected
      (fun i => volume (D.shading.carrier i))).symm
  have hbucketMass := sameOccurrenceBlockShading_mass_eq
    D P A selected hcover q
  have hretained :
      (restrictActualTubeDatum D selected).shading.shadingMass ≤
        ((occupiedCertifiedHighOccurrences
          D P A selected hcover).card : ENNReal) *
          (sameOccurrenceBlockShading D P A selected hcover q).shadingMass := by
    rw [hselectedMass, hbucketMass]
    simpa only [source, weight, fiberWeight, labels, label,
      nsmul_eq_mul] using hweighted
  have hsourceMass : D.shading.shadingMass ≤
      (firstLoss *
        ((occupiedCertifiedHighOccurrences
          D P A selected hcover).card : ENNReal)) *
        (sameOccurrenceBlockShading D P A selected hcover q).shadingMass := by
    calc
      D.shading.shadingMass ≤ firstLoss *
          (restrictActualTubeDatum D selected).shading.shadingMass := hfirst
      _ ≤ firstLoss *
          (((occupiedCertifiedHighOccurrences
            D P A selected hcover).card : ENNReal) *
            (sameOccurrenceBlockShading D P A selected hcover q).shadingMass) :=
        mul_le_mul' le_rfl hretained
      _ = (firstLoss *
          ((occupiedCertifiedHighOccurrences
            D P A selected hcover).card : ENNReal)) *
            (sameOccurrenceBlockShading D P A selected hcover q).shadingMass := by
        ac_rfl
  refine ⟨q, ?_, hretained, hsourceMass, ?_⟩
  · simpa only [labels] using hq
  let Z := sameOccurrenceBlockShading D P A selected hcover q
  have hunion : Z.shadedUnion ⊆ D.shading.shadedUnion :=
    sameOccurrenceBlockShading_shadedUnion_subset
      D P A selected hcover q
  unfold Shading.averageMultiplicity
  calc
    D.shading.shadingMass / volume D.shading.shadedUnion ≤
        ((firstLoss *
          ((occupiedCertifiedHighOccurrences
            D P A selected hcover).card : ENNReal)) *
            Z.shadingMass) / volume D.shading.shadedUnion :=
      ENNReal.div_le_div_right hsourceMass _
    _ ≤ ((firstLoss *
          ((occupiedCertifiedHighOccurrences
            D P A selected hcover).card : ENNReal)) *
            Z.shadingMass) / volume Z.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = (firstLoss *
          ((occupiedCertifiedHighOccurrences
            D P A selected hcover).card : ENNReal)) *
            (Z.shadingMass / volume Z.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Nonzero source mass plus the existing source-to-selected retention
automatically rules out an empty selected set. -/
theorem exists_sameOccurrenceBlockShading_weighted_retention_of_source_ne_zero
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q)
    (firstLoss : ENNReal)
    (hfirst : D.shading.shadingMass ≤ firstLoss *
      (restrictActualTubeDatum D selected).shading.shadingMass)
    (hsource : D.shading.shadingMass ≠ 0) :
    ∃ q : CertifiedHighOccurrenceLabel D P A,
      q ∈ occupiedCertifiedHighOccurrences D P A selected hcover ∧
      (restrictActualTubeDatum D selected).shading.shadingMass ≤
          ((occupiedCertifiedHighOccurrences
            D P A selected hcover).card : ENNReal) *
            (sameOccurrenceBlockShading D P A selected hcover q).shadingMass ∧
      D.shading.shadingMass ≤
          (firstLoss *
            ((occupiedCertifiedHighOccurrences
              D P A selected hcover).card : ENNReal)) *
            (sameOccurrenceBlockShading D P A selected hcover q).shadingMass ∧
      D.shading.averageMultiplicity ≤
          (firstLoss *
            ((occupiedCertifiedHighOccurrences
              D P A selected hcover).card : ENNReal)) *
            (sameOccurrenceBlockShading D P A selected hcover q).averageMultiplicity := by
  have hselected : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero :
        (restrictActualTubeDatum D selected).shading.shadingMass = 0 := by
      rw [restrictActualTubeDatum_shadingMass, hselectedEmpty]
      simp
    rw [hzero, mul_zero] at hfirst
    exact hsource (bot_unique hfirst)
  exact exists_sameOccurrenceBlockShading_weighted_retention
    D P A selected hselected hcover firstLoss hfirst

#print axioms CertifiedHighOccurrenceLabel
#print axioms chosenCertifiedHighOccurrence
#print axioms chosenCertifiedHighOccurrence_mem_block
#print axioms sameOccurrenceBlockBucket
#print axioms occupiedCertifiedHighOccurrences
#print axioms sameOccurrenceBlockShading
#print axioms sameOccurrenceBlockShading_mass_eq
#print axioms sameOccurrenceBlockShading_shadedUnion_subset
#print axioms exists_sameOccurrenceBlockShading_weighted_retention
#print axioms
  exists_sameOccurrenceBlockShading_weighted_retention_of_source_ne_zero

end
end Family8GreedyHighPrefixSameOccurrenceWeightedMassV1
