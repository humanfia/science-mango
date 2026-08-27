import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
import FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

open scoped BigOperators

noncomputable section

universe u v w

/-!
# Producing the literal q-regular relation G' and its rich coarse mass

The incidence data layer deliberately exposes an arbitrary predicate `keep`.
This module constructs that predicate from the literal finite good-pair set.
For a pair `(i,r)`, its statistic is the number of good pairs with the same
curve index `i` and the same assigned coarse rectangle.  A finite logarithmic
pigeonhole selects one comparable-multiplicity bucket, retaining a
`1 / (log₂ (#fineLabels) + 2)` fraction of all good pairs.

Because the predicate depends only on `(i, coarseRectangleAt r)`, it retains
or discards a whole local incidence block.  Every nonempty retained block
therefore has degree in `[q,2q]`, not merely a stored degree callback.
Filtering the coarse rectangles by fibre cardinality then supplies richness
by definition, while an explicit poor-rectangle subtraction supplies the
retained mass lower bound used by the separated-pair producer.
-/

/-- The literal good-pair block with fixed curve and fixed coarse rectangle. -/
noncomputable def coarseGoodPairBlock
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (i : iota) (R : C2GraphRectangle) : Finset (iota × fineLabel) := by
  classical
  exact D.goodPairs.filter fun pair =>
    pair.1 = i ∧ D.coarseRectangleAt pair.2 = R

/-- The actual local coarse degree before regularization. -/
def coarseGoodPairDegree
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (i : iota) (R : C2GraphRectangle) : Nat :=
  (coarseGoodPairBlock D i R).card

/-- Logarithmic q-bucket selection.  It is constant on every local block. -/
def coarseDegreeBucketKeep
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (bucket : Nat) (i : iota) (r : fineLabel) : Prop :=
  comparableLabel (coarseGoodPairDegree D i (D.coarseRectangleAt r)) =
    bucket

/-- The number of possible zero-or-dyadic degree labels. -/
def coarseDegreeBucketLoss
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel) : Nat :=
  Nat.log 2 D.fineLabels.card + 2

@[simp]
theorem mem_coarseGoodPairBlock_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    {i : iota} {R : C2GraphRectangle} {pair : iota × fineLabel} :
    pair ∈ coarseGoodPairBlock D i R ↔
      D.GoodPair pair.1 pair.2 ∧ pair.1 = i ∧
        D.coarseRectangleAt pair.2 = R := by
  classical
  simp only [coarseGoodPairBlock, Finset.mem_filter, D.mem_goodPairs_iff]

/-- A fixed-curve block injects into the finite fine-label family. -/
theorem coarseGoodPairDegree_le_fineLabels_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (i : iota) (R : C2GraphRectangle) :
    coarseGoodPairDegree D i R ≤ D.fineLabels.card := by
  classical
  have hsubset : coarseGoodPairBlock D i R ⊆
      ({i} : Finset iota) ×ˢ D.fineLabels := by
    intro pair hpair
    have hdata := (mem_coarseGoodPairBlock_iff D).mp hpair
    exact Finset.mem_product.mpr
      ⟨by simp [hdata.2.1], hdata.1.2.1⟩
  have hcard := Finset.card_le_card hsubset
  simpa [coarseGoodPairDegree] using hcard

/-- Literal Fubini identity: good-pair mass is the sum of actual Y₁ active
degrees at the selected fine-label source points. -/
theorem goodPairs_card_eq_sum_activeAtPoint
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel) :
    D.goodPairs.card =
      ∑ r ∈ D.fineLabels,
        (D.shading.activeAtPoint (D.pointAt r)).card := by
  classical
  have hpartition : D.goodPairs.card =
      ∑ r ∈ D.fineLabels,
        (D.goodPairs.filter fun pair => pair.2 = r).card :=
    Finset.card_eq_sum_card_fiberwise (fun pair hpair =>
      (D.mem_goodPairs_iff.mp hpair).2.1)
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro r hr
  symm
  apply Finset.card_bij
    (fun i _hi => (i, r))
  · intro i hi
    apply Finset.mem_filter.mpr
    have hactive := (D.shading.mem_activeAtPoint (D.pointAt r) i).mp hi
    exact ⟨D.mem_goodPairs_iff.mpr ⟨hactive.1, hr, hactive.2⟩, rfl⟩
  · intro i₁ _hi₁ i₂ _hi₂ heq
    exact congrArg Prod.fst heq
  · intro pair hpair
    have hfilter := Finset.mem_filter.mp hpair
    have hgood := D.mem_goodPairs_iff.mp hfilter.1
    refine ⟨pair.1, ?_, ?_⟩
    · apply (D.shading.mem_activeAtPoint (D.pointAt r) pair.1).mpr
      exact ⟨hgood.1, by simpa [hfilter.2] using hgood.2.2⟩
    · apply Prod.ext
      · rfl
      · exact hfilter.2.symm

/-- One literal active incidence at a selected fine label proves that the
source good-pair relation is nonempty. -/
theorem goodPairs_nonempty_of_activeAtPoint
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    {r : fineLabel} (hr : r ∈ D.fineLabels) {i : iota}
    (hi : i ∈ D.shading.activeAtPoint (D.pointAt r)) :
    D.goodPairs.Nonempty := by
  have hactive := (D.shading.mem_activeAtPoint (D.pointAt r) i).mp hi
  exact ⟨(i, r), D.mem_goodPairs_iff.mpr
    ⟨hactive.1, hr, hactive.2⟩⟩

/-- Nonempty fine labels with nonempty actual active fibres automatically
supply the nonemptiness needed by logarithmic q-pigeonholing. -/
theorem goodPairs_nonempty_of_fineLabels
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (hfine : D.fineLabels.Nonempty)
    (hactive : ∀ r, r ∈ D.fineLabels →
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty) :
    D.goodPairs.Nonempty := by
  obtain ⟨r, hr⟩ := hfine
  obtain ⟨i, hi⟩ := hactive r hr
  exact goodPairs_nonempty_of_activeAtPoint D hr hi


/-- A uniform actual Y₁ active-degree lower bound yields a numerical source
mass lower bound for the literal good-pair relation. -/
theorem fineLabels_mul_activeDegreeLower_le_goodPairs_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (degreeLower : Nat)
    (hdegree : ∀ r, r ∈ D.fineLabels →
      degreeLower ≤ (D.shading.activeAtPoint (D.pointAt r)).card) :
    D.fineLabels.card * degreeLower ≤ D.goodPairs.card := by
  rw [goodPairs_card_eq_sum_activeAtPoint D]
  calc
    D.fineLabels.card * degreeLower =
        ∑ _r ∈ D.fineLabels, degreeLower := by simp
    _ ≤ ∑ r ∈ D.fineLabels,
        (D.shading.activeAtPoint (D.pointAt r)).card :=
      Finset.sum_le_sum fun r hr => hdegree r hr


/-- If every fine-label source point lies in one actual E₂ dyadic cell,
the cell's canonical natural lower endpoint supplies the source mass lower. -/
theorem fineLabels_mul_pyzE2DegreeLower_le_goodPairs_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (label : Int)
    (hcell : ∀ r, r ∈ D.fineLabels →
      D.pointAt r ∈
        projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : ∀ r, r ∈ D.fineLabels →
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty) :
    D.fineLabels.card * pyzE2DegreeLower label ≤
      D.goodPairs.card := by
  apply fineLabels_mul_activeDegreeLower_le_goodPairs_card
  intro r hr
  exact pyzE2DegreeLower_le_active_card_of_mem_cell D.shading label
    (D.pointAt r) (hcell r hr) (hactive r hr)


/-- The retained relation is exactly the selected statistic fibre. -/
theorem retainedGoodPairs_degreeBucket_eq_filter
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (bucket : Nat) :
    D.retainedGoodPairs (coarseDegreeBucketKeep D bucket) =
      D.goodPairs.filter fun pair =>
        comparableLabel (coarseGoodPairDegree D pair.1
          (D.coarseRectangleAt pair.2)) = bucket := by
  classical
  ext pair
  simp only [Finset.mem_filter, D.mem_retainedGoodPairs_iff,
    D.mem_goodPairs_iff, coarseDegreeBucketKeep]

/-- A logarithmic pigeonhole produces a genuine nonzero q-window and retains
an explicit fraction of the literal good-pair cardinality. -/
theorem exists_coarseDegreeBucket_with_retained_mass
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (hgood : D.goodPairs.Nonempty) :
    ∃ bucket ∈ Finset.range (coarseDegreeBucketLoss D),
      0 < comparableBase bucket ∧
      D.goodPairs.card ≤ coarseDegreeBucketLoss D *
        (D.retainedGoodPairs
          (coarseDegreeBucketKeep D bucket)).card := by
  classical
  let label : (iota × fineLabel) → Nat := fun pair =>
    comparableLabel (coarseGoodPairDegree D pair.1
      (D.coarseRectangleAt pair.2))
  let candidates := Finset.range (coarseDegreeBucketLoss D)
  have hcandidates : candidates.Nonempty := by
    exact ⟨0, by simp [candidates, coarseDegreeBucketLoss]⟩
  have hlabel : ∀ pair ∈ D.goodPairs, label pair ∈ candidates := by
    intro pair hpair
    have hdegree := coarseGoodPairDegree_le_fineLabels_card D pair.1
      (D.coarseRectangleAt pair.2)
    have hle := comparableLabel_le_of_le hdegree
    rw [Finset.mem_range]
    dsimp only [label, candidates, coarseDegreeBucketLoss]
    omega
  let fiberCard : Nat → Nat := fun bucket =>
    (D.goodPairs.filter fun pair => label pair = bucket).card
  obtain ⟨bucket, hbucket, hmax⟩ :=
    Finset.exists_max_image candidates fiberCard hcandidates
  have hmass : D.goodPairs.card ≤ candidates.card * fiberCard bucket := by
    calc
      D.goodPairs.card = ∑ b ∈ candidates,
          (D.goodPairs.filter fun pair => label pair = b).card :=
        Finset.card_eq_sum_card_fiberwise hlabel
      _ ≤ ∑ _b ∈ candidates, fiberCard bucket := by
        apply Finset.sum_le_sum
        intro b hb
        exact hmax b hb
      _ = candidates.card * fiberCard bucket := by simp
  have hfiberNonempty :
      (D.goodPairs.filter fun pair => label pair = bucket).Nonempty := by
    obtain ⟨pair, hpair⟩ := hgood
    have hpairLabel : label pair ∈ candidates := hlabel pair hpair
    have hsourceFiber : 0 < fiberCard (label pair) := by
      apply Finset.card_pos.mpr
      exact ⟨pair, Finset.mem_filter.mpr ⟨hpair, rfl⟩⟩
    have hselectedPos : 0 < fiberCard bucket :=
      hsourceFiber.trans_le (hmax (label pair) hpairLabel)
    exact Finset.card_pos.mp hselectedPos
  have hbasePos : 0 < comparableBase bucket := by
    obtain ⟨pair, hpair⟩ := hfiberNonempty
    have hpairData := Finset.mem_filter.mp hpair
    have hblockNonempty :
        (coarseGoodPairBlock D pair.1
          (D.coarseRectangleAt pair.2)).Nonempty := by
      refine ⟨pair, ?_⟩
      exact (mem_coarseGoodPairBlock_iff D).mpr
        ⟨D.mem_goodPairs_iff.mp hpairData.1, rfl, rfl⟩
    have hcomp := zeroOrComparable_of_comparableLabel_eq hpairData.2
    rcases hcomp with hzero | hpositive
    · have hdegreePos : 0 < coarseGoodPairDegree D pair.1
          (D.coarseRectangleAt pair.2) := by
        exact Finset.card_pos.mpr hblockNonempty
      omega
    · exact hpositive.1
  refine ⟨bucket, hbucket, hbasePos, ?_⟩
  rw [retainedGoodPairs_degreeBucket_eq_filter]
  simpa [candidates, fiberCard, label, coarseDegreeBucketLoss] using hmass

/-- Once a block's label is selected, filtering keeps that whole block. -/
theorem coarseDegreeBucket_curveBlock_eq_sourceBlock
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (bucket : Nat) (i : iota) (R : C2GraphRectangle)
    (hlabel : comparableLabel (coarseGoodPairDegree D i R) = bucket) :
    (D.coarseIncidencePairs (coarseDegreeBucketKeep D bucket) R).filter
        (fun pair => pair.1 = i) =
      coarseGoodPairBlock D i R := by
  classical
  ext pair
  constructor
  · intro hpair
    have hfilter := Finset.mem_filter.mp hpair
    have hincidence :=
      (D.mem_coarseIncidencePairs_iff
        (coarseDegreeBucketKeep D bucket)).mp hfilter.1
    exact (mem_coarseGoodPairBlock_iff D).mpr
      ⟨hincidence.1, hfilter.2, hincidence.2.2⟩
  · intro hpair
    have hblock := (mem_coarseGoodPairBlock_iff D).mp hpair
    apply Finset.mem_filter.mpr
    refine ⟨(D.mem_coarseIncidencePairs_iff
      (coarseDegreeBucketKeep D bucket)).mpr ?_, hblock.2.1⟩
    refine ⟨hblock.1, ?_, hblock.2.2⟩
    unfold coarseDegreeBucketKeep
    simpa [hblock.2.1, hblock.2.2] using hlabel

/-- Every nonempty retained curve block lies in the actual selected q-window. -/
theorem coarseDegreeBucket_curve_degree_bounds
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (bucket : Nat) (R : C2GraphRectangle) (i : iota)
    (hi : i ∈ D.coarseCurveIndexFiber
      (coarseDegreeBucketKeep D bucket) R) :
    comparableBase bucket ≤
        ((D.coarseIncidencePairs (coarseDegreeBucketKeep D bucket) R).filter
          fun pair => pair.1 = i).card ∧
      ((D.coarseIncidencePairs (coarseDegreeBucketKeep D bucket) R).filter
          fun pair => pair.1 = i).card ≤ 2 * comparableBase bucket := by
  obtain ⟨r, hgood, hkeep, hcoarse⟩ :=
    (D.mem_coarseCurveIndexFiber_iff
      (coarseDegreeBucketKeep D bucket)).mp hi
  have hlabel : comparableLabel (coarseGoodPairDegree D i R) = bucket := by
    unfold coarseDegreeBucketKeep at hkeep
    simpa [hcoarse] using hkeep
  have heq := coarseDegreeBucket_curveBlock_eq_sourceBlock
    D bucket i R hlabel
  have hblockNonempty : (coarseGoodPairBlock D i R).Nonempty := by
    refine ⟨(i, r), (mem_coarseGoodPairBlock_iff D).mpr ?_⟩
    exact ⟨hgood, rfl, hcoarse⟩
  have hcomp := zeroOrComparable_of_comparableLabel_eq hlabel
  rcases hcomp with hzero | hpositive
  · have hdegreePos : 0 < coarseGoodPairDegree D i R := by
      exact Finset.card_pos.mpr hblockNonempty
    omega
  · rw [heq]
    exact ⟨hpositive.2.1, hpositive.2.2.le⟩

/-- Coarse rectangles whose literal retained curve fibre has the displayed
richness. -/
noncomputable def richCoarseRectangleFamily
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota → fineLabel → Prop) (richness : Nat) :
    Finset C2GraphRectangle := by
  classical
  exact D.coarseRectangleFamily.filter fun R =>
    richness ≤ (D.coarseCurveIndexFiber keep R).card

@[simp]
theorem mem_richCoarseRectangleFamily_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota → fineLabel → Prop) (richness : Nat)
    {R : C2GraphRectangle} :
    R ∈ richCoarseRectangleFamily D keep richness ↔
      R ∈ D.coarseRectangleFamily ∧
        richness ≤ (D.coarseCurveIndexFiber keep R).card := by
  classical
  simp [richCoarseRectangleFamily]

/-- The explicit retained-mass lower bound after discarding poor coarse
rectangles. -/
def automaticRichRetainedMassLower
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (richness degreeUpper : Nat) : Nat :=
  D.goodPairs.card / coarseDegreeBucketLoss D -
    D.coarseRectangleFamily.card * (richness * degreeUpper)

/-- The selected q-mass minus the explicit contribution of poor rectangles
is retained over the literal rich coarse subfamily. -/
theorem automaticRichRetainedMassLower_le
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota → fineLabel → Prop)
    (richness degreeUpper : Nat)
    (hselection : D.goodPairs.card ≤ coarseDegreeBucketLoss D *
      (D.retainedGoodPairs keep).card)
    (hdegree : ∀ R i,
      i ∈ D.coarseCurveIndexFiber keep R →
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card ≤ degreeUpper) :
    automaticRichRetainedMassLower D richness degreeUpper ≤
      (retainedGoodPairsOver D keep
        (richCoarseRectangleFamily D keep richness)).card := by
  classical
  let rich := richCoarseRectangleFamily D keep richness
  let poor := D.coarseRectangleFamily.filter fun R =>
    ¬richness ≤ (D.coarseCurveIndexFiber keep R).card
  have hselectedLower : D.goodPairs.card / coarseDegreeBucketLoss D ≤
      (D.retainedGoodPairs keep).card := by
    exact Nat.div_le_of_le_mul hselection
  have hsplit :
      (∑ R ∈ D.coarseRectangleFamily,
          (D.coarseIncidencePairs keep R).card) =
        (∑ R ∈ rich, (D.coarseIncidencePairs keep R).card) +
          ∑ R ∈ poor, (D.coarseIncidencePairs keep R).card := by
    simpa [rich, poor, richCoarseRectangleFamily] using
      (Finset.sum_filter_add_sum_filter_not
        (s := D.coarseRectangleFamily)
        (p := fun R => richness ≤
          (D.coarseCurveIndexFiber keep R).card)
        (fun R => (D.coarseIncidencePairs keep R).card)).symm
  have hpoorPointwise : ∀ R ∈ poor,
      (D.coarseIncidencePairs keep R).card ≤ richness * degreeUpper := by
    intro R hR
    have hnotRich : ¬richness ≤
        (D.coarseCurveIndexFiber keep R).card :=
      (Finset.mem_filter.mp hR).2
    have hincidence :=
      coarseIncidencePairs_card_le_curveFiber_card_mul_degreeUpper
        D keep R degreeUpper (fun i hi => hdegree R i hi)
    exact hincidence.trans (Nat.mul_le_mul_right degreeUpper
      (Nat.le_of_lt (Nat.lt_of_not_ge hnotRich)))
  have hpoorSum :
      (∑ R ∈ poor, (D.coarseIncidencePairs keep R).card) ≤
        D.coarseRectangleFamily.card * (richness * degreeUpper) := by
    calc
      (∑ R ∈ poor, (D.coarseIncidencePairs keep R).card) ≤
          ∑ _R ∈ poor, richness * degreeUpper := by
        exact Finset.sum_le_sum fun R hR => hpoorPointwise R hR
      _ = poor.card * (richness * degreeUpper) := by simp
      _ ≤ D.coarseRectangleFamily.card * (richness * degreeUpper) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card
          (Finset.filter_subset _ _))
  have htotal : (D.retainedGoodPairs keep).card ≤
      (retainedGoodPairsOver D keep rich).card +
        D.coarseRectangleFamily.card * (richness * degreeUpper) := by
    rw [D.retainedGoodPairs_card_eq_sum_coarse keep, hsplit,
      retainedGoodPairsOver_card_eq_sum_coarseIncidencePairs]
    exact Nat.add_le_add_left hpoorSum _
  unfold automaticRichRetainedMassLower
  apply (Nat.sub_le_sub_right hselectedLower _).trans
  rw [Nat.sub_le_iff_le_add]
  simpa [rich, Nat.add_comm] using htotal

/-- A numerical version of the rich retained-mass lower bound, sourced from
a uniform actual active degree on the fine labels. -/
def activeDegreeRichRetainedMassLower
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (activeDegreeLower richness degreeUpper : Nat) : Nat :=
  (D.fineLabels.card * activeDegreeLower) / coarseDegreeBucketLoss D -
    D.coarseRectangleFamily.card * (richness * degreeUpper)

/-- The literal active-degree lower bound feeds through logarithmic q-selection
and the poor-rectangle subtraction without any retained-mass assumption. -/
theorem activeDegreeRichRetainedMassLower_le
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota → fineLabel → Prop)
    (activeDegreeLower richness degreeUpper : Nat)
    (hactiveDegree : ∀ r, r ∈ D.fineLabels →
      activeDegreeLower ≤
        (D.shading.activeAtPoint (D.pointAt r)).card)
    (hselection : D.goodPairs.card ≤ coarseDegreeBucketLoss D *
      (D.retainedGoodPairs keep).card)
    (hdegree : ∀ R i,
      i ∈ D.coarseCurveIndexFiber keep R →
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card ≤ degreeUpper) :
    activeDegreeRichRetainedMassLower D activeDegreeLower richness
        degreeUpper ≤
      (retainedGoodPairsOver D keep
        (richCoarseRectangleFamily D keep richness)).card := by
  have hsource :=
    fineLabels_mul_activeDegreeLower_le_goodPairs_card D activeDegreeLower
      hactiveDegree
  have hdiv := Nat.div_le_div_right
    (c := coarseDegreeBucketLoss D) hsource
  have hautomatic :=
    automaticRichRetainedMassLower_le D keep richness degreeUpper
      hselection hdegree
  unfold activeDegreeRichRetainedMassLower
  apply (Nat.sub_le_sub_right hdiv _).trans
  exact hautomatic


/-- The canonical near-pair cap chosen as the ceiling of the actual
non-concentration expression. -/
def automaticCanonicalNearCap
    {iota : Type v} [DecidableEq iota]
    (N : CanonicalNormNonconcentrationData iota) (ballRadius : Real) : Nat :=
  Nat.ceil (((10 * ballRadius) / N.criticalScale) ^ N.exponent *
    ((N.criticalBall.card : Nat) : Real))

/-- With automatic richness `nearCap + 1`, strict room after near-pair
subtraction is built into the construction. -/
def automaticCanonicalRichness
    {iota : Type v} [DecidableEq iota]
    (N : CanonicalNormNonconcentrationData iota) (ballRadius : Real) : Nat :=
  automaticCanonicalNearCap N ballRadius + 1

/-- For one selected logarithmic degree bucket, all source-level hypotheses
of the separated-pair producer are generated.  The only remaining geometric
interface is the literal inclusion of the selected coarse fibres in the
canonical norm family. -/
theorem automatic_bucket_separatedPairLower_le_total
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (hselection : D.goodPairs.card ≤ coarseDegreeBucketLoss D *
      (D.retainedGoodPairs (coarseDegreeBucketKeep D bucket)).card)
    (hfiberSubset : ∀ R,
      R ∈ richCoarseRectangleFamily D (coarseDegreeBucketKeep D bucket)
        (automaticCanonicalRichness N ballRadius) →
      D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
        N.family)
    (hsymm : ∀ x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta ≤ 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius ≤ N.ceiling) :
    canonicalCoarseSeparatedPairProducedLower
        (automaticCanonicalRichness N ballRadius)
        (automaticCanonicalNearCap N ballRadius)
        (automaticRichRetainedMassLower D
          (automaticCanonicalRichness N ballRadius)
          (2 * comparableBase bucket))
        (2 * comparableBase bucket) ≤
      canonicalCoarseRichSeparatedPairCountTotal N D
        (coarseDegreeBucketKeep D bucket) ballRadius := by
  let keep := coarseDegreeBucketKeep D bucket
  let nearCap := automaticCanonicalNearCap N ballRadius
  let richness := automaticCanonicalRichness N ballRadius
  let degreeUpper := 2 * comparableBase bucket
  let rectangles := richCoarseRectangleFamily D keep richness
  have hrectangles : rectangles ⊆ D.coarseRectangleFamily := by
    exact Finset.filter_subset _ _
  have hdegreeAll : ∀ R i,
      i ∈ D.coarseCurveIndexFiber keep R →
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card ≤ degreeUpper := by
    intro R i hi
    exact (coarseDegreeBucket_curve_degree_bounds D bucket R i hi).2
  have hdegree : ∀ R, R ∈ rectangles → ∀ i,
      i ∈ D.coarseCurveIndexFiber keep R →
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card ≤ degreeUpper := by
    intro R _hR i hi
    exact hdegreeAll R i hi
  have hmass : automaticRichRetainedMassLower D richness degreeUpper ≤
      (retainedGoodPairsOver D keep rectangles).card := by
    simpa only [rectangles] using
      automaticRichRetainedMassLower_le D keep richness degreeUpper hselection hdegreeAll
  have hrichness : ∀ R, R ∈ rectangles →
      richness ≤ (D.coarseCurveIndexFiber keep R).card := by
    intro R hR
    exact (mem_richCoarseRectangleFamily_iff D keep richness).mp hR |>.2
  have hnumeric :
      ((10 * ballRadius) / N.criticalScale) ^ N.exponent *
          ((N.criticalBall.card : Nat) : Real) ≤ (nearCap : Real) := by
    exact Nat.le_ceil _
  apply canonicalCoarseSeparatedPairProducedLower_le_total
    N D keep ballRadius rectangles richness nearCap
      (automaticRichRetainedMassLower D richness degreeUpper) degreeUpper
  · exact hrectangles
  · intro R hR
    exact hfiberSubset R hR
  · exact hmass
  · exact hdegree
  · exact hrichness
  · exact hsymm
  · exact hnearRadiusLower
  · exact hnearRadiusUpper
  · exact hnumeric

/-- A hierarchy/E₂-style active-degree lower bound can be substituted for
the exact good-pair cardinality in the final separated-pair estimate. -/
theorem activeDegree_bucket_separatedPairLower_le_total
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket activeDegreeLower : Nat)
    (hactiveDegree : ∀ r, r ∈ D.fineLabels →
      activeDegreeLower ≤
        (D.shading.activeAtPoint (D.pointAt r)).card)
    (hselection : D.goodPairs.card ≤ coarseDegreeBucketLoss D *
      (D.retainedGoodPairs (coarseDegreeBucketKeep D bucket)).card)
    (hfiberSubset : ∀ R,
      R ∈ richCoarseRectangleFamily D (coarseDegreeBucketKeep D bucket)
        (automaticCanonicalRichness N ballRadius) →
      D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
        N.family)
    (hsymm : ∀ x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta ≤ 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius ≤ N.ceiling) :
    canonicalCoarseSeparatedPairProducedLower
        (automaticCanonicalRichness N ballRadius)
        (automaticCanonicalNearCap N ballRadius)
        (activeDegreeRichRetainedMassLower D activeDegreeLower
          (automaticCanonicalRichness N ballRadius)
          (2 * comparableBase bucket))
        (2 * comparableBase bucket) ≤
      canonicalCoarseRichSeparatedPairCountTotal N D
        (coarseDegreeBucketKeep D bucket) ballRadius := by
  have hsource :=
    fineLabels_mul_activeDegreeLower_le_goodPairs_card D activeDegreeLower
      hactiveDegree
  have hmass :
      activeDegreeRichRetainedMassLower D activeDegreeLower
          (automaticCanonicalRichness N ballRadius)
          (2 * comparableBase bucket) ≤
        automaticRichRetainedMassLower D
          (automaticCanonicalRichness N ballRadius)
          (2 * comparableBase bucket) := by
    unfold activeDegreeRichRetainedMassLower automaticRichRetainedMassLower
    exact Nat.sub_le_sub_right
      (Nat.div_le_div_right (c := coarseDegreeBucketLoss D) hsource) _
  have hproduced :
      canonicalCoarseSeparatedPairProducedLower
          (automaticCanonicalRichness N ballRadius)
          (automaticCanonicalNearCap N ballRadius)
          (activeDegreeRichRetainedMassLower D activeDegreeLower
            (automaticCanonicalRichness N ballRadius)
            (2 * comparableBase bucket))
          (2 * comparableBase bucket) ≤
        canonicalCoarseSeparatedPairProducedLower
          (automaticCanonicalRichness N ballRadius)
          (automaticCanonicalNearCap N ballRadius)
          (automaticRichRetainedMassLower D
            (automaticCanonicalRichness N ballRadius)
            (2 * comparableBase bucket))
          (2 * comparableBase bucket) := by
    unfold canonicalCoarseSeparatedPairProducedLower
    exact Nat.mul_le_mul_left _
      (Nat.div_le_div_right (c := 2 * comparableBase bucket) hmass)
  exact hproduced.trans
    (automatic_bucket_separatedPairLower_le_total N D ballRadius bucket
      hselection hfiberSubset hsymm hnearRadiusLower hnearRadiusUpper)


/-- The automatic ceiling and successor choices leave strict room for the
near-pair subtraction, with no scalar hypothesis. -/
theorem automaticCanonicalNearCap_lt_richness
    {iota : Type v} [DecidableEq iota]
    (N : CanonicalNormNonconcentrationData iota) (ballRadius : Real) :
    automaticCanonicalNearCap N ballRadius <
      automaticCanonicalRichness N ballRadius := by
  exact Nat.lt_succ_self _

/-- The generated separated-pair lower bound is positive as soon as the
explicit rich retained mass contains one full selected degree block. -/
theorem automatic_bucket_separatedPairLower_pos
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (hbasePos : 0 < comparableBase bucket)
    (hmassBlock : 2 * comparableBase bucket ≤
      automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket)) :
    0 < canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket) := by
  apply canonicalCoarseSeparatedPairProducedLower_pos
  · exact automaticCanonicalNearCap_lt_richness N ballRadius
  · exact Nat.mul_pos (by omega) hbasePos
  · exact hmassBlock

/-- Fully automatic source-side production.  The existential bucket carries
its logarithmic retained-mass estimate and q-positivity.  The final
implication displays the one missing cross-record geometric statement:
selected rich coarse fibres must lie in the canonical norm family. -/
theorem exists_actualGPrime_bucket_separatedPairLower
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (hgood : D.goodPairs.Nonempty)
    (hsymm : ∀ x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta ≤ 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius ≤ N.ceiling) :
    ∃ bucket ∈ Finset.range (coarseDegreeBucketLoss D),
      0 < comparableBase bucket ∧
      D.goodPairs.card ≤ coarseDegreeBucketLoss D *
        (D.retainedGoodPairs (coarseDegreeBucketKeep D bucket)).card ∧
      ((∀ R,
          R ∈ richCoarseRectangleFamily D
            (coarseDegreeBucketKeep D bucket)
            (automaticCanonicalRichness N ballRadius) →
          D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
            N.family) →
        canonicalCoarseSeparatedPairProducedLower
            (automaticCanonicalRichness N ballRadius)
            (automaticCanonicalNearCap N ballRadius)
            (automaticRichRetainedMassLower D
              (automaticCanonicalRichness N ballRadius)
              (2 * comparableBase bucket))
            (2 * comparableBase bucket) ≤
          canonicalCoarseRichSeparatedPairCountTotal N D
            (coarseDegreeBucketKeep D bucket) ballRadius) := by
  obtain ⟨bucket, hbucket, hbasePos, hselection⟩ :=
    exists_coarseDegreeBucket_with_retained_mass D hgood
  refine ⟨bucket, hbucket, hbasePos, hselection, ?_⟩
  intro hfiberSubset
  exact automatic_bucket_separatedPairLower_le_total N D ballRadius bucket
    hselection hfiberSubset hsymm hnearRadiusLower hnearRadiusUpper

#print axioms coarseGoodPairDegree_le_fineLabels_card
#print axioms goodPairs_card_eq_sum_activeAtPoint
#print axioms goodPairs_nonempty_of_activeAtPoint
#print axioms goodPairs_nonempty_of_fineLabels
#print axioms fineLabels_mul_activeDegreeLower_le_goodPairs_card
#print axioms fineLabels_mul_pyzE2DegreeLower_le_goodPairs_card
#print axioms exists_coarseDegreeBucket_with_retained_mass
#print axioms coarseDegreeBucket_curve_degree_bounds
#print axioms automaticRichRetainedMassLower_le
#print axioms activeDegreeRichRetainedMassLower_le
#print axioms automatic_bucket_separatedPairLower_le_total
#print axioms activeDegree_bucket_separatedPairLower_le_total
#print axioms automaticCanonicalNearCap_lt_richness
#print axioms automatic_bucket_separatedPairLower_pos
#print axioms exists_actualGPrime_bucket_separatedPairLower

end

end FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
