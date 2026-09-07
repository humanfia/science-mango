import Family8Grounding.Family8GreedyWinnerAutomaticJohnSideBucketV1
import Family8Grounding.Family8SelectedOccurrenceFineBucketSupportV1
import Submission.Kakeya.ConvexFactoring.RefinementMultiplicity
import Mathlib.Tactic

/-!
# Weighted winner-side bucketing on an arbitrary selected occurrence set

This is the side-geometry seam needed after the first-hit fibre-density
bucket.  Occurrences are weighted by the *actual shaded mass* of their fibre
in the retained fine shading.  Thus one common winner-side label is selected
with only `winnerSideBucketLoss delta`; there is no loss by `R.card` and no
distinguished occurrence is chosen.

The output shading is the literal restriction to all fine indices over the
retained side bucket.  In particular, a later exact-outer assembly may choose
its own coarse witness in this same occurrence set, without a second
mass-popularity selection.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceWeightedWinnerSideBucketV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFineBucketSupportV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- Actual retained shaded mass in one selected greedy fibre. -/
def selectedOccurrenceFiberShadingWeight
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (Y : Shading fine.bodyFamily)
    (q : Fin (blocks fine.bodyFamily P).length) : ENNReal :=
  fiberShadingMass (selectedOccurrenceFactorization P R) Y (some q)

/-- Retained occurrences with one common automatic John-side label. -/
def selectedOccurrenceWinnerSideBucket
    (hdelta : 0 < delta)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (label : Fin 3 -> Int) :
    Finset (Fin (blocks fine.bodyFamily P).length) :=
  sideShapeBucket R (winnerLongSide P hdelta) label

/-- Restrict a fine shading to all fibres over a retained occurrence set. -/
def selectedOccurrenceFineShading
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (Y : Shading fine.bodyFamily) : Shading fine.bodyFamily :=
  (IndexedShadingRefinement.restrictTo Y
    (selectedOccurrenceFineIndices P R)).shading

/-- A generic finite `ENNReal`-weighted bucket retains mass up to the exact
number of occupied labels. -/
private theorem exists_ennreal_bucket_retention
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (items : Finset alpha) (hitems : items.Nonempty)
    (label : alpha -> beta) (weight : alpha -> ENNReal) :
    ∃ b ∈ occupiedWeightBuckets items label,
      (∑ x ∈ items, weight x) <=
        ((occupiedWeightBuckets items label).card : ENNReal) *
          ∑ x ∈ items.filter (fun x => label x = b), weight x := by
  classical
  let labels := occupiedWeightBuckets items label
  let fiberWeight : beta -> ENNReal := fun b =>
    ∑ x ∈ items with label x = b, weight x
  have hlabels : labels.Nonempty := occupiedWeightBuckets_nonempty hitems
  obtain ⟨b, hb, hmax⟩ :=
    Finset.exists_max_image labels fiberWeight hlabels
  refine ⟨b, hb, ?_⟩
  have hmaps : ∀ x ∈ items, label x ∈ labels := by
    intro x hx
    exact mem_occupiedWeightBuckets_iff.mpr ⟨x, hx, rfl⟩
  calc
    (∑ x ∈ items, weight x) = ∑ c ∈ labels, fiberWeight c :=
      (Finset.sum_fiberwise_of_maps_to
        (s := items) (t := labels) (g := label) hmaps weight).symm
    _ <= labels.card • fiberWeight b :=
      Finset.sum_le_card_nsmul labels fiberWeight (fiberWeight b)
        (fun c hc => hmax c hc)
    _ = (labels.card : ENNReal) *
        ∑ x ∈ items.filter (fun x => label x = b), weight x := by
      simp [labels, fiberWeight, nsmul_eq_mul]

/-- Exact partition of a supported fine bucket's mass into the selected
occurrence fibres. -/
theorem selectedOccurrenceFineBucket_mass_eq_sum_fiberShadingWeight
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (Y : Shading fine.bodyFamily) (fineBucket : Finset iota)
    (hfineBucket : fineBucket ⊆ selectedOccurrenceFineIndices P R) :
    (IndexedShadingRefinement.restrictTo Y fineBucket).shading.shadingMass =
      ∑ q ∈ R,
        selectedOccurrenceFiberShadingWeight P R
          (IndexedShadingRefinement.restrictTo Y fineBucket).shading q := by
  classical
  let Q := selectedOccurrenceFactorization P R
  let Ybucket := (IndexedShadingRefinement.restrictTo Y fineBucket).shading
  have hrestrict :
      (IndexedShadingRefinement.restrictTo
        Ybucket Q.index.fine).shading.shadingMass = Ybucket.shadingMass := by
    simpa only [Q, Ybucket] using
      (selectedOccurrenceFineBucket_restrictTo_fine_shadingMass_eq
        P R Y fineBucket hfineBucket)
  calc
    (IndexedShadingRefinement.restrictTo Y fineBucket).shading.shadingMass =
        Ybucket.shadingMass := rfl
    _ = (IndexedShadingRefinement.restrictTo
          Ybucket Q.index.fine).shading.shadingMass := hrestrict.symm
    _ = activeShadingMass Q Ybucket := by
      rw [shadingMass_restrictTo_eq_sum]
      rfl
    _ = ∑ k ∈ Q.index.coarse, fiberShadingMass Q Ybucket k :=
      activeShadingMass_eq_sum_fiberShadingMass Q Ybucket
    _ = ∑ q ∈ R,
        selectedOccurrenceFiberShadingWeight P R Ybucket q := by
      rw [selectedOccurrenceFactorization_coarse]
      unfold selectedOccurrenceIndices
      rw [Finset.sum_image]
      · rfl
      · intro q _ k _ hqk
        exact Option.some.inj hqk
    _ = ∑ q ∈ R,
        selectedOccurrenceFiberShadingWeight P R
          (IndexedShadingRefinement.restrictTo Y fineBucket).shading q := rfl

/-- Exact mass of a further occurrence restriction, expressed with the same
fibre weights from the larger selected factorization. -/
theorem selectedOccurrenceFineShading_mass_eq_sum_fiberShadingWeight
    (R T : Finset (Fin (blocks fine.bodyFamily P).length))
    (hTR : T ⊆ R) (Y : Shading fine.bodyFamily) :
    (selectedOccurrenceFineShading P T Y).shadingMass =
      ∑ q ∈ T, selectedOccurrenceFiberShadingWeight P R Y q := by
  classical
  let Q := selectedOccurrenceFactorization P R
  let Qside := selectedOccurrenceFactorization P T
  calc
    (selectedOccurrenceFineShading P T Y).shadingMass =
        activeShadingMass Qside Y := by
      rw [selectedOccurrenceFineShading, shadingMass_restrictTo_eq_sum]
      unfold activeShadingMass
      rw [selectedOccurrenceFactorization_fine P T]
    _ = ∑ k ∈ Qside.index.coarse, fiberShadingMass Qside Y k :=
      activeShadingMass_eq_sum_fiberShadingMass Qside Y
    _ = ∑ q ∈ T, fiberShadingMass Qside Y (some q) := by
      rw [show Qside.index.coarse = selectedOccurrenceIndices P T by
        exact selectedOccurrenceFactorization_coarse P T]
      unfold selectedOccurrenceIndices
      rw [Finset.sum_image]
      intro q _ k _ hqk
      exact Option.some.inj hqk
    _ = ∑ q ∈ T, selectedOccurrenceFiberShadingWeight P R Y q := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold selectedOccurrenceFiberShadingWeight fiberShadingMass
      rw [show Qside.index.fiber (some q) =
            (blockAt fine.bodyFamily P q).fiber by
          simpa only [Qside] using
            (selectedOccurrenceFactorization_fiber P T q hq),
        show Q.index.fiber (some q) =
            (blockAt fine.bodyFamily P q).fiber by
          simpa only [Q] using
            (selectedOccurrenceFactorization_fiber P R q (hTR hq))]

/-- Restricting the set of occurrences cannot introduce any new side label,
so the full automatic cubic logarithmic bound also controls an arbitrary
`R`. -/
theorem occupied_selectedOccurrenceWinnerSideLabels_card_le
    (hdelta : 0 < delta)
    (hfineContained : ∀ i, i ∈ active →
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (occupiedWeightBuckets R
      (fun q => sideShapeLabel (winnerLongSide P hdelta q))).card <=
        winnerSideBucketLoss delta := by
  classical
  apply le_trans (Finset.card_le_card ?_)
    (occupied_winnerSideLabels_card_le P hdelta hfineContained)
  intro label hlabel
  obtain ⟨q, hqR, hqLabel⟩ :=
    mem_occupiedWeightBuckets_iff.mp hlabel
  exact mem_occupiedWeightBuckets_iff.mpr
    ⟨q, Finset.mem_univ q, hqLabel⟩

/-- One actual-shaded-mass-weighted winner-side bucket.  The same complete
bucket `Rside` is retained for every downstream construction; no occurrence
is selected here. -/
theorem exists_selectedOccurrence_weightedWinnerSideBucket
    (hdelta : 0 < delta)
    (hfineContained : ∀ i, i ∈ active →
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (Y : Shading fine.bodyFamily) (fineBucket : Finset iota)
    (hfineBucket : fineBucket ⊆ selectedOccurrenceFineIndices P R)
    (hYbucket0 :
      (IndexedShadingRefinement.restrictTo
        Y fineBucket).shading.shadingMass ≠ 0) :
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets R
        (fun q => sideShapeLabel (winnerLongSide P hdelta q)) /\
      let Rside := selectedOccurrenceWinnerSideBucket P hdelta R label
      let Ybucket :=
        (IndexedShadingRefinement.restrictTo Y fineBucket).shading
      let Yside := selectedOccurrenceFineShading P Rside Ybucket
      Rside.Nonempty /\
      Rside ⊆ R /\
      Yside.shadingMass ≠ 0 /\
      Ybucket.shadingMass <=
        (winnerSideBucketLoss delta : ENNReal) * Yside.shadingMass /\
      Ybucket.averageMultiplicity <=
        (winnerSideBucketLoss delta : ENNReal) *
          Yside.averageMultiplicity /\
      ∀ q, q ∈ Rside → ∀ j,
        sideShapeUpper label j / 2 < winnerLongSide P hdelta q j /\
          winnerLongSide P hdelta q j <= sideShapeUpper label j := by
  classical
  let Ybucket :=
    (IndexedShadingRefinement.restrictTo Y fineBucket).shading
  let labelFn := fun q : Fin (blocks fine.bodyFamily P).length =>
    sideShapeLabel (winnerLongSide P hdelta q)
  let weight := selectedOccurrenceFiberShadingWeight P R Ybucket
  have hsourceSum : Ybucket.shadingMass = ∑ q ∈ R, weight q := by
    simpa only [Ybucket, weight] using
      (selectedOccurrenceFineBucket_mass_eq_sum_fiberShadingWeight
        P R Y fineBucket hfineBucket)
  have hRnonempty : R.Nonempty := by
    by_contra hnot
    have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hRempty] at hsourceSum
    apply hYbucket0
    change Ybucket.shadingMass = 0
    simpa only [Finset.sum_empty] using hsourceSum
  obtain ⟨label, hlabel, hweighted⟩ :=
    exists_ennreal_bucket_retention R hRnonempty labelFn weight
  let Rside := selectedOccurrenceWinnerSideBucket P hdelta R label
  let Yside := selectedOccurrenceFineShading P Rside Ybucket
  have hRsideSubset : Rside ⊆ R := by
    intro q hq
    exact (mem_sideShapeBucket_iff R
      (winnerLongSide P hdelta) label q).mp hq |>.1
  have hsideSum : Yside.shadingMass = ∑ q ∈ Rside, weight q := by
    simpa only [Yside, weight] using
      (selectedOccurrenceFineShading_mass_eq_sum_fiberShadingWeight
        P R Rside hRsideSubset Ybucket)
  have hcard := occupied_selectedOccurrenceWinnerSideLabels_card_le
    P hdelta hfineContained R
  have hmass : Ybucket.shadingMass <=
      (winnerSideBucketLoss delta : ENNReal) * Yside.shadingMass := by
    calc
      Ybucket.shadingMass = ∑ q ∈ R, weight q := hsourceSum
      _ <= ((occupiedWeightBuckets R labelFn).card : ENNReal) *
          ∑ q ∈ R.filter (fun q => labelFn q = label), weight q :=
        hweighted
      _ = ((occupiedWeightBuckets R labelFn).card : ENNReal) *
          ∑ q ∈ Rside, weight q := by
        congr 1
      _ <= (winnerSideBucketLoss delta : ENNReal) *
          ∑ q ∈ Rside, weight q := by
        exact mul_le_mul' (by exact_mod_cast hcard) le_rfl
      _ = (winnerSideBucketLoss delta : ENNReal) *
          Yside.shadingMass := by rw [hsideSum]
  have hYside0 : Yside.shadingMass ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmass
    apply hYbucket0
    change Ybucket.shadingMass = 0
    exact bot_unique hmass
  have hRsideNonempty : Rside.Nonempty := by
    obtain ⟨q, hqR, hqLabel⟩ :=
      mem_occupiedWeightBuckets_iff.mp hlabel
    exact ⟨q, (mem_sideShapeBucket_iff R
      (winnerLongSide P hdelta) label q).mpr ⟨hqR, hqLabel⟩⟩
  have havg : Ybucket.averageMultiplicity <=
      (winnerSideBucketLoss delta : ENNReal) *
        Yside.averageMultiplicity := by
    let sideRefinement := IndexedShadingRefinement.restrictTo Ybucket
      (selectedOccurrenceFineIndices P Rside)
    have hwithin : WithinFactor (winnerSideBucketLoss delta)
        Ybucket.shadingMass sideRefinement.shading.shadingMass := by
      unfold WithinFactor
      simpa only [sideRefinement, Yside, selectedOccurrenceFineShading,
        nsmul_eq_mul] using hmass
    have h := sideRefinement.averageMultiplicity_le
      (winnerSideBucketLoss delta) hwithin
    simpa only [sideRefinement, Yside, selectedOccurrenceFineShading,
      nsmul_eq_mul] using h
  refine ⟨label, hlabel, ?_⟩
  dsimp only
  refine ⟨hRsideNonempty, hRsideSubset, hYside0, hmass, havg, ?_⟩
  intro q hq j
  have hqLabel := (mem_sideShapeBucket_iff R
    (winnerLongSide P hdelta) label q).mp hq |>.2
  have hband := sideShapeUpper_half_lt_and_le
    (winnerLongSide_pos P hdelta q) j
  simpa only [hqLabel] using hband

#print axioms selectedOccurrenceFineBucket_mass_eq_sum_fiberShadingWeight
#print axioms selectedOccurrenceFineShading_mass_eq_sum_fiberShadingWeight
#print axioms occupied_selectedOccurrenceWinnerSideLabels_card_le
#print axioms exists_selectedOccurrence_weightedWinnerSideBucket

end
end Family8SelectedOccurrenceWeightedWinnerSideBucketV1
