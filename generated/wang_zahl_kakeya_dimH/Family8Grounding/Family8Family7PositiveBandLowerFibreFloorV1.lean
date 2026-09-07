import Family8Grounding.Family8ShadingAwareProjectedPhysicalLowerBucketV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7PositiveBandLowerFibreFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2ProjectionSliceRetentionV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

/-!
# Extract a genuine positive fibre floor from a positive projected band

For a finite active pattern, pointwise positivity has a common positive
lower bound.  Reciprocal natural levels form a countable exhaustion, so one
fixed level preserves positive measure of any positive multiplicity band.
This is qualitative; no quantitative mass-retention factor is claimed.
-/

theorem exists_common_pos_lowerBound_on_finset
    {alpha : Type*} (s : Finset alpha) (mass : alpha -> ENNReal)
    (hpos : forall i, i ∈ s -> 0 < mass i) :
    ∃ level : ENNReal, 0 < level ∧ forall i, i ∈ s -> level <= mass i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨level, hlevel, hlower⟩ := ih <| by
        intro i hi
        exact hpos i (Finset.mem_insert_of_mem hi)
      refine ⟨min level (mass a), lt_min hlevel ?_, ?_⟩
      · exact hpos a (Finset.mem_insert_self a s)
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hlower i hi)

theorem exists_positive_fibreFloor_preserving_multiplicityBand
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper : Nat)
    (hband : 0 < volume
      (FiniteProjectedShading.multiplicityBand
        (shadingAwareProjectedPhysical Y active f hf X hX I hI)
        lower upper)) :
    ∃ fibreFloor : ENNReal, 0 < fibreFloor ∧
      0 < volume
        (FiniteProjectedShading.multiplicityBand
          (shadingAwareProjectedPhysicalLowerBucket
            Y active f hf X hX I hI fibreFloor) lower upper) := by
  let positive := shadingAwareProjectedPhysical
    Y active f hf X hX I hI
  let lowerAt := fun n : Nat => shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI ((n : ENNReal)⁻¹)
  have hsubset : positive.multiplicityBand lower upper ⊆
      ⋃ n : Nat, (lowerAt n).multiplicityBand lower upper := by
    intro u hu
    have huband := (positive.mem_multiplicityBand).mp hu
    have hmassPos : forall i, i ∈ positive.activeAtPoint u ->
        0 < shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u := by
      intro i hi
      exact (mem_activeAtPoint_shadingAwareProjectedPhysical
        Y active f hf X hX I hI u i).mp hi |>.2.2
    obtain ⟨pointFloor, hpointFloor, hpointLower⟩ :=
      exists_common_pos_lowerBound_on_finset
        (positive.activeAtPoint u)
        (fun i => shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u)
        hmassPos
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hpointFloor)
    have hnPos : 0 < (n : ENNReal)⁻¹ :=
      ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n)
    have hactiveEq : (lowerAt n).activeAtPoint u =
        positive.activeAtPoint u := by
      ext i
      rw [mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket,
        mem_activeAtPoint_shadingAwareProjectedPhysical]
      constructor
      · rintro ⟨hi, huX, himass⟩
        exact ⟨hi, huX, hnPos.trans_le himass⟩
      · rintro hi
        refine ⟨hi.1, hi.2.1, ?_⟩
        exact (le_of_lt hn).trans <| hpointLower i <|
          (mem_activeAtPoint_shadingAwareProjectedPhysical
            Y active f hf X hX I hI u i).mpr hi
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    apply (lowerAt n).mem_multiplicityBand.mpr
    constructor
    · exact huband.1
    · rw [hactiveEq]
      exact huband.2
  have hexists : ∃ n : Nat,
      0 < volume ((lowerAt n).multiplicityBand lower upper) := by
    by_contra hnot
    have hnot' : forall n : Nat,
        ¬ 0 < volume ((lowerAt n).multiplicityBand lower upper) := by
      intro n hn
      exact hnot ⟨n, hn⟩
    have hzero : forall n : Nat,
        volume ((lowerAt n).multiplicityBand lower upper) = 0 := by
      intro n
      exact le_antisymm (le_of_not_gt (hnot' n)) bot_le
    have hunionZero : volume
        (⋃ n : Nat, (lowerAt n).multiplicityBand lower upper) = 0 :=
      measure_iUnion_null hzero
    have hle : (volume : Measure ProjectionSpace)
        (positive.multiplicityBand lower upper) <=
        volume (⋃ n : Nat, (lowerAt n).multiplicityBand lower upper) :=
      measure_mono hsubset
    rw [hunionZero] at hle
    exact (not_le_of_gt hband) hle
  obtain ⟨n, hn⟩ := hexists
  refine ⟨(n : ENNReal)⁻¹, ?_, ?_⟩
  · exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n)
  · simpa only [lowerAt] using hn

#print axioms exists_common_pos_lowerBound_on_finset
#print axioms exists_positive_fibreFloor_preserving_multiplicityBand

end

end Family8Family7PositiveBandLowerFibreFloorV1
