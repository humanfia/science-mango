import FamilyStickyCinematicL32WZL3UniformTubeSourceV1
import FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
import FamilyStickyCinematicL32FiniteWeightedBucketV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators NNReal

namespace Family8Family7WeightedVerticalGraphCBucketV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! # Lightweight weighted graph-c bucket on an arbitrary vertical source -/

def verticalGraphCBucket {radius : NNReal}
    (eta : Real) (T : Tube radius) : Int :=
  Int.floor (projectedTubeGraphC T / eta)

theorem abs_projectedTubeGraphC_sub_le_of_verticalGraphCBucket_eq
    {radius : NNReal} {eta : Real} (heta : 0 < eta)
    {T U : Tube radius}
    (hbucket : verticalGraphCBucket eta T =
      verticalGraphCBucket eta U) :
    |projectedTubeGraphC T - projectedTubeGraphC U| ≤ eta := by
  have hscaled :
      |projectedTubeGraphC T / eta - projectedTubeGraphC U / eta| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor hbucket
  rw [← sub_div, abs_div, abs_of_pos heta] at hscaled
  exact ((div_lt_one heta).mp hscaled).le

def verticalGraphCBucketCandidateLabels (eta : Real) : Finset Int :=
  Finset.Icc (Int.floor ((-2 : Real) / eta))
    (Int.floor ((2 : Real) / eta))

def verticalGraphCBucketLoss (eta : Real) : Nat :=
  (verticalGraphCBucketCandidateLabels eta).card

theorem verticalGraphCBucketLoss_eq (eta : Real) :
    verticalGraphCBucketLoss eta =
      (Int.floor ((2 : Real) / eta) + 1 -
        Int.floor ((-2 : Real) / eta)).toNat := by
  simp [verticalGraphCBucketLoss, verticalGraphCBucketCandidateLabels,
    Int.card_Icc]

theorem verticalGraphCBucket_mem_candidates_of_vertical_half
    {radius : NNReal} {eta : Real} (heta : 0 < eta)
    {T : Tube radius}
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    verticalGraphCBucket eta T ∈
      verticalGraphCBucketCandidateLabels eta := by
  have hc := abs_projectedTubeGraphC_le_two_of_vertical_half hvertical
  have hlower : (-2 : Real) ≤ projectedTubeGraphC T := (abs_le.mp hc).1
  have hupper : projectedTubeGraphC T ≤ (2 : Real) := (abs_le.mp hc).2
  rw [verticalGraphCBucketCandidateLabels, Finset.mem_Icc]
  constructor
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right heta).2 hlower)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right heta).2 hupper)

def verticalSourceOccupiedGraphCBuckets
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (eta : Real) (S : WZL3UniformTubeSource radius iota) : Finset Int :=
  occupiedWeightBuckets S.source
    (fun i ↦ verticalGraphCBucket eta (S.family.tubes i))

def verticalSourceGraphCBucketFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (eta : Real) (S : WZL3UniformTubeSource radius iota)
    (label : Int) : Finset iota :=
  S.source.filter fun i ↦
    verticalGraphCBucket eta (S.family.tubes i) = label

@[simp] theorem mem_verticalSourceGraphCBucketFiber_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (eta : Real) (S : WZL3UniformTubeSource radius iota)
    (label : Int) (i : iota) :
    i ∈ verticalSourceGraphCBucketFiber eta S label ↔
      i ∈ S.source ∧
        verticalGraphCBucket eta (S.family.tubes i) = label := by
  simp [verticalSourceGraphCBucketFiber]

theorem verticalSourceOccupiedGraphCBuckets_subset_candidates
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {eta : Real} (heta : 0 < eta)
    (S : WZL3UniformTubeSource radius iota) :
    verticalSourceOccupiedGraphCBuckets eta S ⊆
      verticalGraphCBucketCandidateLabels eta := by
  intro label hlabel
  obtain ⟨i, hi, rfl⟩ := (mem_occupiedWeightBuckets_iff).mp hlabel
  exact verticalGraphCBucket_mem_candidates_of_vertical_half heta
    (S.source_direction_final_half i hi)

theorem verticalSourceOccupiedGraphCBuckets_card_le_loss
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {eta : Real} (heta : 0 < eta)
    (S : WZL3UniformTubeSource radius iota) :
    (verticalSourceOccupiedGraphCBuckets eta S).card ≤
      verticalGraphCBucketLoss eta := by
  exact Finset.card_le_card
    (verticalSourceOccupiedGraphCBuckets_subset_candidates heta S)

/-- A genuine occupied bucket retains the exact reciprocal of the number of
occupied labels, and therefore of the explicit `|c| ≤ 2` label cap. -/
theorem exists_verticalSourceGraphCBucket_weight_retention
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {eta : Real} (heta : 0 < eta)
    (S : WZL3UniformTubeSource radius iota)
    (hsource : S.source.Nonempty) (weight : iota → NNReal) :
    ∃ label : Int,
      (verticalSourceGraphCBucketFiber eta S label).Nonempty ∧
      (∑ i ∈ S.source, weight i) ≤
        (verticalSourceOccupiedGraphCBuckets eta S).card •
          ∑ i ∈ verticalSourceGraphCBucketFiber eta S label, weight i ∧
      (∑ i ∈ S.source, weight i) ≤
        verticalGraphCBucketLoss eta •
          ∑ i ∈ verticalSourceGraphCBucketFiber eta S label, weight i ∧
      ∀ i, i ∈ verticalSourceGraphCBucketFiber eta S label →
        verticalGraphCBucket eta (S.family.tubes i) = label := by
  classical
  let labels := verticalSourceOccupiedGraphCBuckets eta S
  let fiberWeight : Int → NNReal := fun label ↦
    ∑ i ∈ verticalSourceGraphCBucketFiber eta S label, weight i
  have hlabels : labels.Nonempty := occupiedWeightBuckets_nonempty hsource
  obtain ⟨label, hlabel, hmax⟩ :=
    Finset.exists_max_image labels fiberWeight hlabels
  have hweight : (∑ i ∈ S.source, weight i) ≤
      labels.card • fiberWeight label := by
    calc
      (∑ i ∈ S.source, weight i) =
          ∑ b ∈ labels, fiberWeight b := by
        apply (Finset.sum_fiberwise_of_maps_to
          (s := S.source) (t := labels)
          (g := fun i ↦ verticalGraphCBucket eta (S.family.tubes i))
          (fun i hi ↦
            (mem_occupiedWeightBuckets_iff).mpr ⟨i, hi, rfl⟩)
          weight).symm
      _ ≤ labels.card • fiberWeight label :=
        Finset.sum_le_card_nsmul labels fiberWeight (fiberWeight label)
          (fun b hb ↦ hmax b hb)
  obtain ⟨i, hi, hilabel⟩ :=
    (mem_occupiedWeightBuckets_iff).mp hlabel
  have hfiber :
      (verticalSourceGraphCBucketFiber eta S label).Nonempty := by
    exact ⟨i, (mem_verticalSourceGraphCBucketFiber_iff eta S label i).2
      ⟨hi, hilabel⟩⟩
  have hoccupied :=
    verticalSourceOccupiedGraphCBuckets_card_le_loss heta S
  refine ⟨label, hfiber, ?_, ?_, ?_⟩
  · simpa [labels, fiberWeight] using hweight
  · calc
      (∑ i ∈ S.source, weight i) ≤
          (verticalSourceOccupiedGraphCBuckets eta S).card •
            ∑ i ∈ verticalSourceGraphCBucketFiber eta S label,
              weight i := by
        simpa [labels, fiberWeight] using hweight
      _ ≤ verticalGraphCBucketLoss eta •
            ∑ i ∈ verticalSourceGraphCBucketFiber eta S label,
              weight i :=
        nsmul_le_nsmul_left bot_le hoccupied
  · intro i hi
    exact (mem_verticalSourceGraphCBucketFiber_iff eta S label i).1 hi |>.2

#print axioms verticalGraphCBucket
#print axioms abs_projectedTubeGraphC_sub_le_of_verticalGraphCBucket_eq
#print axioms verticalGraphCBucketLoss_eq
#print axioms verticalGraphCBucket_mem_candidates_of_vertical_half
#print axioms verticalSourceOccupiedGraphCBuckets_subset_candidates
#print axioms verticalSourceOccupiedGraphCBuckets_card_le_loss
#print axioms exists_verticalSourceGraphCBucket_weight_retention

end

end Family8Family7WeightedVerticalGraphCBucketV1
