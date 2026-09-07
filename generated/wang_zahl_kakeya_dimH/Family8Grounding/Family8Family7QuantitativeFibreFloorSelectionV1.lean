import Family8Grounding.Family8Family7PositiveBandLowerFibreFloorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7QuantitativeFibreFloorSelectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8Family7PositiveBandLowerFibreFloorV1

noncomputable section

/-!
# Quantitative selection of a positive fibre floor

There is no a priori positive lower bound for the positive fibre masses in
the source multiplicity band.  Consequently no fixed finite list of positive
levels covers that band pointwise.  The honest replacement has three steps.

* inverse powers of two cover the source band countably;
* finite measure gives a data-dependent finite initial segment retaining at
  least half of the source-band measure;
* a weighted finite pigeonhole selects one lower-bucket band, with the
  explicit loss `2 * (cutoff + 1)`.

Every selected bucket uses the original shading, graph, projected base, and
fibre window.  Nothing is reselected on a different datum.
-/

/-- The positive dyadic fibre floors used by the exhaustion. -/
def dyadicFibreFloor (level : Nat) : ENNReal :=
  (2 : ENNReal)⁻¹ ^ level

/-- The exact loss: a factor two for finite truncation and one factor for the
number of admitted dyadic levels. -/
def fibreLevelBinLoss (cutoff : Nat) : Nat :=
  2 * (cutoff + 1)

theorem dyadicFibreFloor_pos (level : Nat) :
    0 < dyadicFibreFloor level := by
  unfold dyadicFibreFloor
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) level

theorem fibreLevelBinLoss_pos (cutoff : Nat) :
    0 < fibreLevelBinLoss cutoff := by
  simp [fibreLevelBinLoss]

/-- The input positivity-based multiplicity band. -/
noncomputable def positiveFibreMultiplicityBand
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper : Nat) : Set ProjectionSpace :=
  FiniteProjectedShading.multiplicityBand
    (shadingAwareProjectedPhysical Y active f hf X hX I hI) lower upper

/-- The multiplicity band on the same datum after imposing one dyadic fibre
floor. -/
noncomputable def dyadicLowerFibreMultiplicityBand
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper level : Nat) : Set ProjectionSpace :=
  FiniteProjectedShading.multiplicityBand
    (shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI (dyadicFibreFloor level)) lower upper

theorem measurableSet_dyadicLowerFibreMultiplicityBand
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper level : Nat) :
    MeasurableSet (dyadicLowerFibreMultiplicityBand
      Y active f hf X hX I hI lower upper level) := by
  exact FiniteProjectedShading.measurableSet_multiplicityBand _ _ _

/-- Thin coverage lemma: inverse powers of two exhaust the positive source
band.  This is countable, not finite; a finite pointwise cover is unavailable
without a uniform positive fibre lower bound. -/
theorem positiveFibreMultiplicityBand_subset_iUnion_dyadic
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper : Nat) :
    positiveFibreMultiplicityBand
        Y active f hf X hX I hI lower upper ⊆
      ⋃ level : Nat, dyadicLowerFibreMultiplicityBand
        Y active f hf X hX I hI lower upper level := by
  classical
  let positive := shadingAwareProjectedPhysical
    Y active f hf X hX I hI
  let lowerAt := fun level : Nat => shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI (dyadicFibreFloor level)
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
  obtain ⟨level, hlevel⟩ :=
    ENNReal.exists_inv_two_pow_lt (ne_of_gt hpointFloor)
  have hactiveEq : (lowerAt level).activeAtPoint u =
      positive.activeAtPoint u := by
    ext i
    rw [mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket,
      mem_activeAtPoint_shadingAwareProjectedPhysical]
    constructor
    · rintro ⟨hi, huX, himass⟩
      exact ⟨hi, huX, (dyadicFibreFloor_pos level).trans_le himass⟩
    · rintro hi
      refine ⟨hi.1, hi.2.1, ?_⟩
      exact (le_of_lt hlevel).trans <| hpointLower i <|
        (mem_activeAtPoint_shadingAwareProjectedPhysical
          Y active f hf X hX I hI u i).mpr hi
  apply Set.mem_iUnion.mpr
  refine ⟨level, ?_⟩
  apply (lowerAt level).mem_multiplicityBand.mpr
  constructor
  · exact huband.1
  · rw [hactiveEq]
    exact huband.2

/-- Finite truncation of the dyadic exhaustion retains at least half of a
positive finite input-band measure.  Finiteness is the only additional
measure hypothesis; without it a countable union of finite-measure buckets
can have infinite input measure while every finite truncation stays finite. -/
theorem exists_finite_dyadic_fibre_cover_half
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper : Nat)
    (hband : 0 < volume (positiveFibreMultiplicityBand
      Y active f hf X hX I hI lower upper))
    (hbandFinite : volume (positiveFibreMultiplicityBand
      Y active f hf X hX I hI lower upper) ≠ ⊤) :
    ∃ cutoff : Nat,
      volume (positiveFibreMultiplicityBand
          Y active f hf X hX I hI lower upper) / 2 <
        volume (Set.accumulate (dyadicLowerFibreMultiplicityBand
          Y active f hf X hX I hI lower upper) cutoff) := by
  let sourceBand := positiveFibreMultiplicityBand
    Y active f hf X hX I hI lower upper
  let levelBand := dyadicLowerFibreMultiplicityBand
    Y active f hf X hX I hI lower upper
  have hsourceUnion : (volume : Measure ProjectionSpace) sourceBand ≤
      volume (⋃ level : Nat, levelBand level) :=
    measure_mono (positiveFibreMultiplicityBand_subset_iUnion_dyadic
      Y active f hf X hX I hI lower upper)
  have hhalfSource : (volume : Measure ProjectionSpace) sourceBand / 2 <
      volume sourceBand :=
    ENNReal.half_lt_self hband.ne' hbandFinite
  have hhalfUnion : (volume : Measure ProjectionSpace) sourceBand / 2 <
      volume (⋃ level : Nat, levelBand level) :=
    hhalfSource.trans_le hsourceUnion
  rw [measure_iUnion_eq_iSup_accumulate] at hhalfUnion
  exact lt_iSup_iff.mp hhalfUnion

/-- Weighted pigeonhole on one finite initial segment of dyadic levels. -/
theorem exists_dyadic_level_retaining_accumulate_average
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper cutoff : Nat) :
    ∃ level : Nat, level ≤ cutoff ∧
      volume (Set.accumulate (dyadicLowerFibreMultiplicityBand
          Y active f hf X hX I hI lower upper) cutoff) ≤
        (cutoff + 1 : Nat) *
          volume (dyadicLowerFibreMultiplicityBand
            Y active f hf X hX I hI lower upper level) := by
  classical
  let levelBand := dyadicLowerFibreMultiplicityBand
    Y active f hf X hX I hI lower upper
  let levels := Finset.range (cutoff + 1)
  let weight : Nat -> ENNReal := fun level => volume (levelBand level)
  have hlevels : levels.Nonempty := by
    exact ⟨0, by simp [levels]⟩
  obtain ⟨level, hlevel, hmax⟩ :=
    Finset.exists_max_image levels weight hlevels
  have haccSubset : Set.accumulate levelBand cutoff ⊆
      ⋃ level ∈ (levels : Set Nat), levelBand level := by
    intro u hu
    obtain ⟨k, hk, huk⟩ := Set.mem_accumulate.mp hu
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨by simpa [levels] using Nat.lt_succ_iff.mpr hk, huk⟩
  have hsum : (∑ k ∈ levels, weight k) ≤ levels.card • weight level :=
    Finset.sum_le_card_nsmul levels weight (weight level)
      (fun k hk => hmax k hk)
  have hmeasure : (volume : Measure ProjectionSpace)
      (Set.accumulate levelBand cutoff) ≤
        (levels.card : ENNReal) * weight level := by
    calc
      volume (Set.accumulate levelBand cutoff) ≤
          volume (⋃ k ∈ (levels : Set Nat), levelBand k) :=
        measure_mono haccSubset
      _ ≤ ∑ k ∈ levels, volume (levelBand k) :=
        measure_biUnion_finset_le levels levelBand
      _ ≤ (levels.card : ENNReal) * weight level := by
        simpa only [weight, nsmul_eq_mul] using hsum
  refine ⟨level, ?_, ?_⟩
  · exact Nat.le_of_lt_succ <| by simpa [levels] using hlevel
  · simpa only [levelBand, levels, Finset.card_range, Nat.cast_add,
      Nat.cast_one, weight] using hmeasure

/-- Quantitative strengthening of the qualitative positive-floor selector.
The returned floor is dyadic and the selected multiplicity band retains at
least `1 / fibreLevelBinLoss cutoff` of the input multiplicity-band volume. -/
theorem exists_quantitative_positive_fibreFloor_preserving_multiplicityBand
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper : Nat)
    (hband : 0 < volume (positiveFibreMultiplicityBand
      Y active f hf X hX I hI lower upper))
    (hbandFinite : volume (positiveFibreMultiplicityBand
      Y active f hf X hX I hI lower upper) ≠ ⊤) :
    ∃ cutoff level : Nat, level ≤ cutoff ∧
      0 < dyadicFibreFloor level ∧
      volume (positiveFibreMultiplicityBand
          Y active f hf X hX I hI lower upper) /
          (fibreLevelBinLoss cutoff : ENNReal) ≤
        volume (dyadicLowerFibreMultiplicityBand
          Y active f hf X hX I hI lower upper level) := by
  obtain ⟨cutoff, hhalf⟩ := exists_finite_dyadic_fibre_cover_half
    Y active f hf X hX I hI lower upper hband hbandFinite
  obtain ⟨level, hlevel, haverage⟩ :=
    exists_dyadic_level_retaining_accumulate_average
      Y active f hf X hX I hI lower upper cutoff
  let sourceMass : ENNReal := volume (positiveFibreMultiplicityBand
    Y active f hf X hX I hI lower upper)
  let selectedMass : ENNReal := volume (dyadicLowerFibreMultiplicityBand
    Y active f hf X hX I hI lower upper level)
  have hhalfLe : sourceMass / 2 ≤
      volume (Set.accumulate (dyadicLowerFibreMultiplicityBand
        Y active f hf X hX I hI lower upper) cutoff) := by
    exact le_of_lt hhalf
  have hsourceDouble : sourceMass ≤
      volume (Set.accumulate (dyadicLowerFibreMultiplicityBand
        Y active f hf X hX I hI lower upper) cutoff) * 2 :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp hhalfLe
  have htotal : sourceMass ≤
      (fibreLevelBinLoss cutoff : ENNReal) * selectedMass := by
    calc
      sourceMass ≤
          volume (Set.accumulate (dyadicLowerFibreMultiplicityBand
            Y active f hf X hX I hI lower upper) cutoff) * 2 :=
        hsourceDouble
      _ ≤ ((cutoff + 1 : Nat) * selectedMass) * 2 :=
        by gcongr
      _ = (fibreLevelBinLoss cutoff : ENNReal) * selectedMass := by
        simp [fibreLevelBinLoss, mul_comm, mul_left_comm, mul_assoc]
  refine ⟨cutoff, level, hlevel, dyadicFibreFloor_pos level, ?_⟩
  have hlossZero : (fibreLevelBinLoss cutoff : ENNReal) ≠ 0 := by
    exact_mod_cast (fibreLevelBinLoss_pos cutoff).ne'
  have hlossTop : (fibreLevelBinLoss cutoff : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  exact (ENNReal.div_le_iff hlossZero hlossTop).mpr <| by
    simpa only [sourceMass, selectedMass, mul_comm] using htotal

#print axioms dyadicFibreFloor
#print axioms fibreLevelBinLoss
#print axioms dyadicFibreFloor_pos
#print axioms fibreLevelBinLoss_pos
#print axioms positiveFibreMultiplicityBand
#print axioms dyadicLowerFibreMultiplicityBand
#print axioms measurableSet_dyadicLowerFibreMultiplicityBand
#print axioms positiveFibreMultiplicityBand_subset_iUnion_dyadic
#print axioms exists_finite_dyadic_fibre_cover_half
#print axioms exists_dyadic_level_retaining_accumulate_average
#print axioms exists_quantitative_positive_fibreFloor_preserving_multiplicityBand

end

end Family8Family7QuantitativeFibreFloorSelectionV1
