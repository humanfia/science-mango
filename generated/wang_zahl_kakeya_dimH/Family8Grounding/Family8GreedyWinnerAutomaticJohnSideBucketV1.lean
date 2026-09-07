import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import FamilyStickyGrounding.JohnCapturedTubeCertificateCleanAdapterV1
import Submission.Kakeya.ConvexFactoring.GreedyDensityCoverCost
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8GreedyWinnerAutomaticJohnSideBucketV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.GreedyDensityCoverCost
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

/-!
# Automatic John sides and a faithful dyadic bucket for greedy winners

Every occurrence of a full-convex greedy partition has a nonempty fine
fiber.  Choosing one actual fine tube in that fiber makes the genuine winner
hull full dimensional and therefore supplies a positive John certificate.
The chosen tube also gives the literal side floor `2 * delta`.  Unit-ball
support gives the uniform ceiling `576` for the comparison-`288` John sides.

The final theorems perform an honest three-coordinate dyadic selection, with
separate mass and cardinality witnesses and the explicit finite label loss.
They deliberately stop at a common factor-two bucket of the *original* John
sides.  Dividing by the common long endpoint requires a common scalar image
of every body; the existing scalar-normalization API does not by itself pull
that image back to an honest unit-length tube cover of the original fine
family.  Accordingly this module proves no `PlankDimensionsCertificate`.
-/

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-! ## One captured fine tube and an automatic positive John certificate -/

/-- A literal fine index in the nonempty occurrence fiber. -/
noncomputable def winnerWitness
    (k : Fin (blocks fine.bodyFamily P).length) : iota :=
  Classical.choose (blockAt fine.bodyFamily P k).fiber_nonempty

theorem winnerWitness_mem
    (k : Fin (blocks fine.bodyFamily P).length) :
    winnerWitness P k ∈ (blockAt fine.bodyFamily P k).fiber :=
  Classical.choose_spec (blockAt fine.bodyFamily P k).fiber_nonempty

/-- The complete actual fine tube of the chosen occurrence witness lies in
the genuine greedy winner body. -/
theorem winnerWitness_tube_subset
    (k : Fin (blocks fine.bodyFamily P).length) :
    (fine.tubes (winnerWitness P k)).carrier ⊆
      ((blockAt fine.bodyFamily P k).body : Set Space) := by
  simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
    (blockAt fine.bodyFamily P k).contained
      (winnerWitness P k) (winnerWitness_mem P k)

/-- The automatically selected raw John side vector for an occurrence
winner. -/
noncomputable def winnerJohnSide
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) : Fin 3 -> NNReal :=
  Classical.choose
    (exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
      (blockAt fine.bodyFamily P k).body
      (fine.tubes (winnerWitness P k)) hdelta
      (winnerWitness_tube_subset P k))

/-- The actual comparison-`288` certificate behind `winnerJohnSide`. -/
noncomputable def winnerJohnCertificate
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) :
    BoxDimensionsCertificate 288 (winnerJohnSide P hdelta k)
      (blockAt fine.bodyFamily P k).body :=
  Classical.choice
    (Classical.choose_spec
      (exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
        (blockAt fine.bodyFamily P k).body
        (fine.tubes (winnerWitness P k)) hdelta
        (winnerWitness_tube_subset P k))).2

theorem winnerJohnSide_pos
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (j : Fin 3) :
    0 < winnerJohnSide P hdelta k j :=
  (Classical.choose_spec
    (exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
      (blockAt fine.bodyFamily P k).body
      (fine.tubes (winnerWitness P k)) hdelta
      (winnerWitness_tube_subset P k))).1 j

/-- The captured fine tube forces the literal lower width `2 * delta` in
every raw John coordinate. -/
theorem two_mul_delta_le_winnerJohnSide
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (j : Fin 3) :
    2 * delta ≤ winnerJohnSide P hdelta k j := by
  exact JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset
    (fine.tubes (winnerWitness P k)) (winnerWitness_tube_subset P k)
    (winnerJohnCertificate P hdelta k) j

/-! ## Carrier-preserving longest-axis relabeling -/

/-- Move the longest chosen John side to coordinate `2`, changing only the
certificate labels. -/
noncomputable def winnerLongSide
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) : Fin 3 -> NNReal :=
  relabeledSide (winnerJohnSide P hdelta k)
    (longAxisPermutation (winnerJohnSide P hdelta k))

noncomputable def winnerLongCertificate
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) :
    BoxDimensionsCertificate 288 (winnerLongSide P hdelta k)
      (blockAt fine.bodyFamily P k).body :=
  relabelBoxDimensionsCertificate (winnerJohnCertificate P hdelta k)
    (longAxisPermutation (winnerJohnSide P hdelta k))

theorem winnerLongSide_pos
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (j : Fin 3) :
    0 < winnerLongSide P hdelta k j := by
  exact winnerJohnSide_pos P hdelta k _

theorem winnerLongSide_le_two
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (j : Fin 3) :
    winnerLongSide P hdelta k j ≤ winnerLongSide P hdelta k 2 := by
  exact relabeledSide_le_two (winnerJohnSide P hdelta k) j

theorem two_mul_delta_le_winnerLongSide
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (j : Fin 3) :
    2 * delta ≤ winnerLongSide P hdelta k j := by
  exact two_mul_delta_le_winnerJohnSide P hdelta k _

/-! ## The unit-ball support ceiling -/

/-- Unit-ball support of the active fine family passes to every actual
greedy winner hull. -/
theorem winnerBody_subset_unitBall
    (hfineContained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (k : Fin (blocks fine.bodyFamily P).length) :
    ((blockAt fine.bodyFamily P k).body : Set Space) ⊆
      Metric.closedBall (0 : Space) 1 := by
  simpa only [coe_unitBallBody] using
    (blockAt_body_subset_of_base fine.bodyFamily active P unitBallBody
      (fun i hi => by
        simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
          hfineContained i hi) k)

/-- Opposite points of the inner comparison-`288` box inside the unit ball
give the uniform raw side ceiling `288 * 2 = 576`. -/
theorem winnerJohnSide_le_576
    (hdelta : 0 < delta)
    (hfineContained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (k : Fin (blocks fine.bodyFamily P).length) (j : Fin 3) :
    winnerJohnSide P hdelta k j ≤ 576 := by
  let cert := winnerJohnCertificate P hdelta k
  let B := cert.box.rescale (288 : NNReal)⁻¹
  have hHull := winnerBody_subset_unitBall P hfineContained k
  have hxBall : B.positiveFacePoint j ∈ Metric.closedBall (0 : Space) 1 :=
    hHull (cert.inner_le (B.positiveFacePoint_mem_carrier j))
  have hyBall : B.negativeFacePoint j ∈ Metric.closedBall (0 : Space) 1 :=
    hHull (cert.inner_le (B.negativeFacePoint_mem_carrier j))
  have hdistReal :
      dist (B.positiveFacePoint j) (B.negativeFacePoint j) ≤ (2 : Real) := by
    rw [Metric.mem_closedBall] at hxBall hyBall
    calc
      dist (B.positiveFacePoint j) (B.negativeFacePoint j) ≤
          dist (B.positiveFacePoint j) 0 +
            dist 0 (B.negativeFacePoint j) := dist_triangle _ _ _
      _ ≤ 1 + 1 := add_le_add hxBall (by simpa [dist_comm] using hyBall)
      _ = 2 := by norm_num
  rw [B.dist_positiveFacePoint_negativeFacePoint] at hdistReal
  have hdist : B.side j ≤ (2 : NNReal) := by exact_mod_cast hdistReal
  change (288 : NNReal)⁻¹ * cert.box.side j ≤ 2 at hdist
  rw [cert.side_eq] at hdist
  have hscaled :=
    (inv_mul_le_iff₀ (by norm_num : (0 : NNReal) < 288)).1 hdist
  norm_num at hscaled ⊢
  simpa [cert, winnerJohnCertificate] using hscaled

theorem winnerLongSide_le_576
    (hdelta : 0 < delta)
    (hfineContained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (k : Fin (blocks fine.bodyFamily P).length) (j : Fin 3) :
    winnerLongSide P hdelta k j ≤ 576 := by
  exact winnerJohnSide_le_576 P hdelta hfineContained k _

/-! ## Explicit finite side labels -/

/-- Cubic ceil-log count for the automatic interval `[2*delta,576]`. -/
def winnerSideBucketLoss (delta : NNReal) : Nat :=
  threeSideDyadicLoss (((2 * delta : NNReal) : Real)) 576

theorem occupied_winnerSideLabels_card_le
    (hdelta : 0 < delta)
    (hfineContained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    (occupiedWeightBuckets
      (Finset.univ : Finset (Fin (blocks fine.bodyFamily P).length))
      (fun k => sideShapeLabel (winnerLongSide P hdelta k))).card ≤
        winnerSideBucketLoss delta := by
  apply card_occupied_sideShapeLabel_le
    (lower := (((2 * delta : NNReal) : Real))) (upper := 576)
  · exact_mod_cast mul_pos (by norm_num : (0 : NNReal) < 2) hdelta
  · intro k _hk j
    constructor
    · exact_mod_cast two_mul_delta_le_winnerLongSide P hdelta k j
    · exact_mod_cast winnerLongSide_le_576 P hdelta hfineContained k j

/-! ## Separate honest mass and count selections -/

private theorem exists_ennreal_bucket_retention
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (items : Finset alpha) (hitems : items.Nonempty)
    (label : alpha -> beta) (weight : alpha -> ENNReal) :
    ∃ b ∈ occupiedWeightBuckets items label,
      (∑ x ∈ items, weight x) ≤
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
    _ ≤ labels.card • fiberWeight b :=
      Finset.sum_le_card_nsmul labels fiberWeight (fiberWeight b)
        (fun c hc => hmax c hc)
    _ = (labels.card : ENNReal) *
        ∑ x ∈ items.filter (fun x => label x = b), weight x := by
      simp [labels, fiberWeight, nsmul_eq_mul]

/-- One side-shape class retains the full active fine body mass up to the
explicit cubic label loss.  This is an `ENNReal` statement, so no hidden
`toReal` finiteness conversion occurs. -/
theorem exists_winnerSideBucket_blockMass_retention
    (hdelta : 0 < delta)
    (hactive : active.Nonempty)
    (hfineContained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    ∃ label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset (Fin (blocks fine.bodyFamily P).length))
        (fun k => sideShapeLabel (winnerLongSide P hdelta k)) ∧
      (∑ i ∈ active, volume (fine.bodyFamily i : Set Space)) ≤
        (winnerSideBucketLoss delta : ENNReal) *
          ∑ k ∈ sideShapeBucket Finset.univ
            (winnerLongSide P hdelta) label,
              blockMass fine.bodyFamily (blockAt fine.bodyFamily P k) ∧
      ∀ k, k ∈ sideShapeBucket Finset.univ
          (winnerLongSide P hdelta) label -> ∀ j,
        sideShapeUpper label j / 2 < winnerLongSide P hdelta k j ∧
          winnerLongSide P hdelta k j ≤ sideShapeUpper label j := by
  let items : Finset (Fin (blocks fine.bodyFamily P).length) := Finset.univ
  have hitems : items.Nonempty := by
    obtain ⟨i, hi⟩ := hactive
    exact ⟨locate fine.bodyFamily P hi, Finset.mem_univ _⟩
  obtain ⟨label, hlabel, hmass⟩ := exists_ennreal_bucket_retention
    items hitems (fun k => sideShapeLabel (winnerLongSide P hdelta k))
    (fun k => blockMass fine.bodyFamily (blockAt fine.bodyFamily P k))
  have hcard := occupied_winnerSideLabels_card_le
    P hdelta hfineContained
  have hbucketMassNonneg : 0 ≤
      ∑ k ∈ sideShapeBucket Finset.univ
        (winnerLongSide P hdelta) label,
          blockMass fine.bodyFamily (blockAt fine.bodyFamily P k) := bot_le
  refine ⟨label, hlabel, ?_, ?_⟩
  · rw [← sum_blockMass_univ_eq_activeMass P]
    calc
      (∑ k : Fin (blocks fine.bodyFamily P).length,
          blockMass fine.bodyFamily (blockAt fine.bodyFamily P k)) ≤
          ((occupiedWeightBuckets
            (Finset.univ : Finset
              (Fin (blocks fine.bodyFamily P).length))
            (fun k => sideShapeLabel
              (winnerLongSide P hdelta k))).card : ENNReal) *
            ∑ k ∈ sideShapeBucket Finset.univ
              (winnerLongSide P hdelta) label,
                blockMass fine.bodyFamily
                  (blockAt fine.bodyFamily P k) := by
        simpa [items, sideShapeBucket] using hmass
      _ ≤ (winnerSideBucketLoss delta : ENNReal) *
            ∑ k ∈ sideShapeBucket Finset.univ
              (winnerLongSide P hdelta) label,
                blockMass fine.bodyFamily
                  (blockAt fine.bodyFamily P k) := by
        exact mul_le_mul' (by exact_mod_cast hcard) le_rfl
  · intro k hk j
    have hkLabel :=
      (mem_sideShapeBucket_iff Finset.univ
        (winnerLongSide P hdelta) label k).1 hk |>.2
    have hband := sideShapeUpper_half_lt_and_le
      (winnerLongSide_pos P hdelta k) j
    simpa only [hkLabel] using hband

/-- A possibly different side-shape class retains occurrence count up to the
same explicit cubic label loss.  It is intentionally a separate witness from
the mass-selected class. -/
theorem exists_winnerSideBucket_card_retention
    (hdelta : 0 < delta)
    (hactive : active.Nonempty)
    (hfineContained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    ∃ label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset (Fin (blocks fine.bodyFamily P).length))
        (fun k => sideShapeLabel (winnerLongSide P hdelta k)) ∧
      (blocks fine.bodyFamily P).length ≤
        winnerSideBucketLoss delta *
          (sideShapeBucket Finset.univ
            (winnerLongSide P hdelta) label).card ∧
      ∀ k, k ∈ sideShapeBucket Finset.univ
          (winnerLongSide P hdelta) label -> ∀ j,
        sideShapeUpper label j / 2 < winnerLongSide P hdelta k j ∧
          winnerLongSide P hdelta k j ≤ sideShapeUpper label j := by
  let items : Finset (Fin (blocks fine.bodyFamily P).length) := Finset.univ
  have hitems : items.Nonempty := by
    obtain ⟨i, hi⟩ := hactive
    exact ⟨locate fine.bodyFamily P hi, Finset.mem_univ _⟩
  obtain ⟨label, hlabel, hweight⟩ :=
    exists_totalWeight_le_card_mul_bucketWeight
      (items := items)
      (bucket := fun k => sideShapeLabel (winnerLongSide P hdelta k))
      (fun _ => (1 : Real)) hitems
  have hcardNat :
      (blocks fine.bodyFamily P).length ≤
        (occupiedWeightBuckets
          (Finset.univ : Finset (Fin (blocks fine.bodyFamily P).length))
          (fun k => sideShapeLabel (winnerLongSide P hdelta k))).card *
          (sideShapeBucket Finset.univ
            (winnerLongSide P hdelta) label).card := by
    have hweightReal :
        ((blocks fine.bodyFamily P).length : Real) ≤
          ((occupiedWeightBuckets
            (Finset.univ : Finset
              (Fin (blocks fine.bodyFamily P).length))
            (fun k => sideShapeLabel
              (winnerLongSide P hdelta k))).card : Real) *
            ((sideShapeBucket Finset.univ
              (winnerLongSide P hdelta) label).card : Real) := by
      simpa [items, bucketWeight, sideShapeBucket] using hweight
    exact_mod_cast hweightReal
  have hlabels := occupied_winnerSideLabels_card_le
    P hdelta hfineContained
  refine ⟨label, hlabel, hcardNat.trans ?_, ?_⟩
  · exact Nat.mul_le_mul_right _ hlabels
  · intro k hk j
    have hkLabel :=
      (mem_sideShapeBucket_iff Finset.univ
        (winnerLongSide P hdelta) label k).1 hk |>.2
    have hband := sideShapeUpper_half_lt_and_le
      (winnerLongSide_pos P hdelta k) j
    simpa only [hkLabel] using hband

#print axioms winnerWitness_tube_subset
#print axioms winnerJohnCertificate
#print axioms two_mul_delta_le_winnerJohnSide
#print axioms winnerLongCertificate
#print axioms winnerBody_subset_unitBall
#print axioms winnerJohnSide_le_576
#print axioms occupied_winnerSideLabels_card_le
#print axioms exists_winnerSideBucket_blockMass_retention
#print axioms exists_winnerSideBucket_card_retention

end
end Family8GreedyWinnerAutomaticJohnSideBucketV1
