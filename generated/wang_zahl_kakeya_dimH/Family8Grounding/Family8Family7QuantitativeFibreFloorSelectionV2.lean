import Family8Grounding.Family8Family7PositiveBandLowerFibreFloorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Family8Family7QuantitativeFibreFloorSelectionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2ProjectionSliceRetentionV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8Family7PositiveBandLowerFibreFloorV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

/-!
# Quantitative dyadic fibre-floor selection

The floor has no absolute scale.  In the original positive multiplicity band,
inverse powers of two give a monotone exhaustion by points whose full active
pattern survives the lower cut.  Continuity from below therefore selects one
finite dyadic level retaining half of the original finite band volume.
-/

/-- The dyadic lower-fibre level used by the exhaustion. -/
def dyadicFibreFloor (n : Nat) : ENNReal :=
  (2 : ENNReal)⁻¹ ^ n

/-- The exact, scale-free loss in the monotone-exhaustion selector. -/
def fibreLevelBinLoss : ENNReal := 2

theorem dyadicFibreFloor_pos (n : Nat) :
    0 < dyadicFibreFloor n := by
  unfold dyadicFibreFloor
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) n

theorem dyadicFibreFloor_antitone : Antitone dyadicFibreFloor := by
  intro n m hnm
  unfold dyadicFibreFloor
  exact pow_le_pow_right_of_le_one'
    (ENNReal.inv_le_one.mpr ENNReal.one_lt_two.le) hnm

/-- A finite positive multiplicity band has one dyadic lower-fibre bucket
retaining at least half of its volume.  The shading, active family, graph,
projected window, fibre window, and multiplicity band are unchanged. -/
theorem exists_dyadic_fibreFloor_half_multiplicityBand
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
        lower upper))
    (hbandFinite : volume
      (FiniteProjectedShading.multiplicityBand
        (shadingAwareProjectedPhysical Y active f hf X hX I hI)
        lower upper) ≠ ∞) :
    ∃ n : Nat, 0 < dyadicFibreFloor n ∧
      volume
          (FiniteProjectedShading.multiplicityBand
            (shadingAwareProjectedPhysical Y active f hf X hX I hI)
            lower upper) ≤
        fibreLevelBinLoss *
          volume
            (FiniteProjectedShading.multiplicityBand
              (shadingAwareProjectedPhysicalLowerBucket
                Y active f hf X hX I hI (dyadicFibreFloor n))
              lower upper) := by
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lowerAt := fun n : Nat => shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI (dyadicFibreFloor n)
  let E := positive.multiplicityBand lower upper
  let kept := fun n : Nat => E ∩ (lowerAt n).multiplicityBand lower upper
  have hband' : 0 < volume E := by
    simpa only [E, positive] using hband
  have hbandFinite' : volume E ≠ ∞ := by
    simpa only [E, positive] using hbandFinite
  have hactiveMono (n m : Nat) (hnm : n ≤ m) (u : ProjectionSpace) :
      (lowerAt n).activeAtPoint u ⊆ (lowerAt m).activeAtPoint u := by
    intro i hi
    have hiData :=
      (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI (dyadicFibreFloor n) u i).mp (by
          simpa only [lowerAt] using hi)
    have hiNext : i ∈
        (shadingAwareProjectedPhysicalLowerBucket
          Y active f hf X hX I hI (dyadicFibreFloor m)).activeAtPoint u := by
      apply (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI (dyadicFibreFloor m) u i).mpr
      exact ⟨hiData.1, hiData.2.1,
        (dyadicFibreFloor_antitone hnm).trans hiData.2.2⟩
    simpa only [lowerAt] using hiNext
  have hactivePositive (n : Nat) (u : ProjectionSpace) :
      (lowerAt n).activeAtPoint u ⊆ positive.activeAtPoint u := by
    simpa only [lowerAt, positive] using
      (activeAtPoint_lowerBucket_subset_positive
        Y active f hf X hX I hI (dyadicFibreFloor_pos n) u)
  have hkeptMono : Monotone kept := by
    intro n m hnm u hu
    rcases hu with ⟨huE, huN⟩
    have huEData := positive.mem_multiplicityBand.mp (by
      simpa only [E] using huE)
    have huNData := (lowerAt n).mem_multiplicityBand.mp huN
    refine ⟨huE, (lowerAt m).mem_multiplicityBand.mpr ?_⟩
    refine ⟨huNData.1, ?_, ?_⟩
    · exact huNData.2.1.trans
        (Finset.card_le_card (hactiveMono n m hnm u))
    · exact (Finset.card_le_card (hactivePositive m u)).trans huEData.2.2
  have hkeptUnion : (⋃ n : Nat, kept n) = E := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun _n => Set.inter_subset_left
    · intro u huE
      have huEData := positive.mem_multiplicityBand.mp (by
        simpa only [E] using huE)
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
      obtain ⟨n, hn⟩ :=
        ENNReal.exists_inv_two_pow_lt (ne_of_gt hpointFloor)
      have hactiveEq : (lowerAt n).activeAtPoint u =
          positive.activeAtPoint u := by
        ext i
        constructor
        · intro hi
          exact hactivePositive n u hi
        · intro hi
          have hiData := (mem_activeAtPoint_shadingAwareProjectedPhysical
            Y active f hf X hX I hI u i).mp hi
          have hiLower : i ∈
              (shadingAwareProjectedPhysicalLowerBucket
                Y active f hf X hX I hI (dyadicFibreFloor n)).activeAtPoint u := by
            apply (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
              Y active f hf X hX I hI (dyadicFibreFloor n) u i).mpr
            exact ⟨hiData.1, hiData.2.1,
              (le_of_lt hn).trans (hpointLower i hi)⟩
          simpa only [lowerAt] using hiLower
      apply Set.mem_iUnion.mpr
      refine ⟨n, huE, ?_⟩
      apply (lowerAt n).mem_multiplicityBand.mpr
      refine ⟨huEData.1, ?_, ?_⟩
      · rw [hactiveEq]
        exact huEData.2.1
      · rw [hactiveEq]
        exact huEData.2.2
  have hmeasureTendsto :
      Tendsto (fun n : Nat => volume (kept n)) atTop (𝓝 (volume E)) := by
    have h := tendsto_measure_iUnion_atTop
      (μ := (volume : Measure ProjectionSpace)) hkeptMono
    rw [hkeptUnion] at h
    simpa only [Function.comp_def] using h
  have hhalf : volume E / 2 < volume E := by
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    simpa only [one_mul, mul_comm] using
      ENNReal.mul_lt_mul_left hband'.ne' hbandFinite' ENNReal.one_lt_two
  obtain ⟨n, hn⟩ :=
    ((tendsto_order.1 hmeasureTendsto).1 _ hhalf).exists
  have hhalfSelected : volume E / 2 ≤
      volume ((lowerAt n).multiplicityBand lower upper) := by
    calc
      volume E / 2 ≤ volume (kept n) := le_of_lt hn
      _ ≤ volume ((lowerAt n).multiplicityBand lower upper) := by
        exact measure_mono Set.inter_subset_right
  have hretention : volume E ≤
      volume ((lowerAt n).multiplicityBand lower upper) * 2 :=
    (ENNReal.div_le_iff_le_mul (by norm_num) (by norm_num)).mp hhalfSelected
  refine ⟨n, dyadicFibreFloor_pos n, ?_⟩
  simpa only [E, positive, lowerAt, fibreLevelBinLoss, mul_comm] using hretention

#print axioms dyadicFibreFloor_pos
#print axioms dyadicFibreFloor_antitone
#print axioms exists_dyadic_fibreFloor_half_multiplicityBand

end

end Family8Family7QuantitativeFibreFloorSelectionV2
