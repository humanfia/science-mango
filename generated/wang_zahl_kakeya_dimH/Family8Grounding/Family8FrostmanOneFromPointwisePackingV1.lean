import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8FrostmanOneFromPointwisePackingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# `K_F(1)` from a genuine pointwise tube-packing bound

This file isolates the analytic and numerical consumer of the pointwise
packing theorem used at the endpoint `beta = 1`.

The geometric input is an explicit theorem parameter

`forall x, Y.pointMultiplicity x <= pointCap`.

It is not stored in a data structure, and the pointwise-to-average step is
proved by integrating the literal natural-valued multiplicity.  The two
unconditional bounds

`averageMultiplicity <= card` and
`averageMultiplicity <= pointCap`

are interpolated by a geometric mean.  The lower bound
`delta^2 / 2 <= volume(T)` then replaces `card` by the actual summed family
volume.  Only the resulting finite constant `(2 C)^(1/2)` is absorbed by an
explicit small-delta threshold.
-/

/-- A global natural-valued pointwise cap gives the same average
multiplicity cap.  This is the real measure-theoretic bridge, valid also when
the shaded union has zero volume. -/
theorem averageMultiplicity_le_natCap_of_pointwise_le
    {ι : Type} [Fintype ι] {F : ConvexFamily ι}
    (Y : Shading F) (pointCap : Nat)
    (hpoint : ∀ x, Y.pointMultiplicity x ≤ pointCap) :
    Y.averageMultiplicity ≤ (pointCap : ENNReal) := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  simpa only [nsmul_eq_mul] using
    (FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
      Y pointCap hpoint)

/-- The automatic pointwise cardinality bound gives the first side of the
interpolation. -/
theorem averageMultiplicity_le_indexCard
    {ι : Type} [Fintype ι] {F : ConvexFamily ι} (Y : Shading F) :
    Y.averageMultiplicity ≤ (Fintype.card ι : ENNReal) :=
  averageMultiplicity_le_natCap_of_pointwise_le Y (Fintype.card ι)
    fun x => Y.pointMultiplicity_le_card x

/-- Ordered-semiring geometric-mean interpolation in `ENNReal`, including
zero and infinity edge cases. -/
theorem le_geometricMean_of_le_left_of_le_right
    {x left right : ENNReal} (hleft : x ≤ left) (hright : x ≤ right) :
    x ≤ (left * right) ^ (1 / 2 : Real) := by
  apply (ENNReal.rpow_le_rpow_iff
    (x := x) (y := (left * right) ^ (1 / 2 : Real))
    (z := (2 : Real)) (by norm_num)).mp
  rw [← ENNReal.rpow_mul]
  norm_num
  rw [pow_two]
  exact mul_le_mul' hleft hright

/-- Summing the actual lower tube-volume bound converts cardinality to the
summed family volume without a nonempty-index side condition. -/
theorem indexCard_mul_half_delta_sq_le_actualFamilyVolume
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    (Fintype.card ι : ENNReal) * ((delta : ENNReal) ^ 2 / 2) ≤
      D.actualFamilyVolume := by
  unfold ActualTubeDatum.actualFamilyVolume familyVolume
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (Fintype.card ι : ENNReal) * ((delta : ENNReal) ^ 2 / 2) =
        ∑ _i : ι, (delta : ENNReal) ^ 2 / 2 := by simp
    _ ≤ ∑ i : ι, volume (D.family.tubes i).carrier := by
      exact Finset.sum_le_sum fun i _ =>
        (D.family.tubes i).half_sq_le_volume_of_le_half hdeltaHalf

/-- Cancel the positive finite tube-volume floor.  This is the exact form
needed before geometric-mean interpolation. -/
theorem indexCard_le_two_mul_delta_rpow_neg_two_mul_actualFamilyVolume
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    (Fintype.card ι : ENNReal) ≤
      2 * (delta : ENNReal) ^ (-2 : Real) * D.actualFamilyVolume := by
  let d : ENNReal := (delta : ENNReal)
  let tubeFloor : ENNReal := d ^ 2 / 2
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hfloor0 : tubeFloor ≠ 0 := by
    dsimp only [tubeFloor]
    exact ENNReal.div_ne_zero.mpr ⟨pow_ne_zero 2 hd0, by norm_num⟩
  have hfloorTop : tubeFloor ≠ ∞ := by
    dsimp only [tubeFloor]
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top hdTop) (by norm_num)
  have hcancel : d ^ (-2 : Real) * d ^ 2 = 1 := by
    rw [← ENNReal.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
    rw [← ENNReal.rpow_add (-2 : Real) (2 : Real) hd0 hdTop]
    norm_num
  apply (ENNReal.mul_le_mul_iff_left hfloor0 hfloorTop).mp
  calc
    (Fintype.card ι : ENNReal) * tubeFloor ≤ D.actualFamilyVolume := by
      simpa only [d, tubeFloor] using
        indexCard_mul_half_delta_sq_le_actualFamilyVolume D hdeltaHalf
    _ = (2 * d ^ (-2 : Real) * D.actualFamilyVolume) * tubeFloor := by
      symm
      dsimp only [tubeFloor]
      rw [div_eq_mul_inv]
      calc
        (2 * d ^ (-2 : Real) * D.actualFamilyVolume) *
            (d ^ 2 * (2 : ENNReal)⁻¹) =
          (2 * (2 : ENNReal)⁻¹) *
            (d ^ (-2 : Real) * d ^ 2) * D.actualFamilyVolume := by
              ac_rfl
        _ = D.actualFamilyVolume := by
          rw [hcancel,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          simp

/-- The raw geometric-mean estimate supplied by a pointwise
`C delta^(-2)` packing theorem. -/
theorem averageMultiplicity_le_pointwisePacking_geometricRHS
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (C : ENNReal) (pointCap : Nat)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hpoint : ∀ x, D.shading.pointMultiplicity x ≤ pointCap)
    (hpointCap : (pointCap : ENNReal) ≤
      C * (delta : ENNReal) ^ (-2 : Real)) :
    D.shading.averageMultiplicity ≤
      (2 * C) ^ (1 / 2 : Real) *
        (delta : ENNReal) ^ (-2 : Real) *
          D.actualFamilyVolume ^ (1 / 2 : Real) := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hmean : D.shading.averageMultiplicity ≤
      ((Fintype.card ι : ENNReal) * (pointCap : ENNReal)) ^
        (1 / 2 : Real) :=
    le_geometricMean_of_le_left_of_le_right
      (averageMultiplicity_le_indexCard D.shading)
      (averageMultiplicity_le_natCap_of_pointwise_le
        D.shading pointCap hpoint)
  have hcard :=
    indexCard_le_two_mul_delta_rpow_neg_two_mul_actualFamilyVolume
      D hdelta hdeltaHalf
  have hproduct :
      (Fintype.card ι : ENNReal) * (pointCap : ENNReal) ≤
        (2 * C) * d ^ (-4 : Real) * D.actualFamilyVolume := by
    calc
      (Fintype.card ι : ENNReal) * (pointCap : ENNReal) ≤
          (2 * d ^ (-2 : Real) * D.actualFamilyVolume) *
            (C * d ^ (-2 : Real)) :=
        mul_le_mul' hcard (by simpa only [d] using hpointCap)
      _ = (2 * C) *
          (d ^ (-2 : Real) * d ^ (-2 : Real)) *
            D.actualFamilyVolume := by ac_rfl
      _ = (2 * C) * d ^ (-4 : Real) * D.actualFamilyVolume := by
        rw [← ENNReal.rpow_add (-2 : Real) (-2 : Real) hd0 hdTop]
        norm_num
  have hrpow := ENNReal.rpow_le_rpow hproduct
    (show (0 : Real) ≤ 1 / 2 by norm_num)
  refine hmean.trans (hrpow.trans_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg,
    ENNReal.mul_rpow_of_nonneg]
  · rw [← ENNReal.rpow_mul]
    norm_num
    simp only [d]
  · norm_num
  · norm_num

/-- Explicit terminal scale which absorbs the sole finite interpolation
constant and also lies below the geometric tube-volume regime `delta≤1/2`. -/
def frostmanOnePointwisePackingThreshold
    (C : ENNReal) (epsilon : Real) : NNReal :=
  min
    (finiteConstantSmallDeltaThreshold
      ((2 * C) ^ (1 / 2 : Real)) epsilon)
    (2 : NNReal)⁻¹

theorem frostmanOnePointwisePackingThreshold_pos
    (C : ENNReal) (epsilon : Real) :
    0 < frostmanOnePointwisePackingThreshold C epsilon := by
  rw [frostmanOnePointwisePackingThreshold, lt_min_iff]
  exact ⟨finiteConstantSmallDeltaThreshold_pos _ _, by positivity⟩

theorem frostmanOnePointwisePackingThreshold_le_half
    (C : ENNReal) (epsilon : Real) :
    frostmanOnePointwisePackingThreshold C epsilon ≤ (2 : NNReal)⁻¹ :=
  min_le_right _ _

/-- Complete per-datum `K_F(1)` estimate from the actual pointwise packing
cap.  No Frostman conclusion is assumed in the input. -/
theorem averageMultiplicity_le_frostmanOneRHS_of_pointwisePacking
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (C : ENNReal) (pointCap : Nat)
    {epsilon : Real}
    (hdelta : 0 < delta)
    (hdeltaThreshold :
      delta ≤ frostmanOnePointwisePackingThreshold C epsilon)
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon)
    (hpoint : ∀ x, D.shading.pointMultiplicity x ≤ pointCap)
    (hpointCap : (pointCap : ENNReal) ≤
      C * (delta : ENNReal) ^ (-2 : Real)) :
    D.shading.averageMultiplicity ≤
      frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon 1 := by
  have hhalf : delta ≤ (2 : NNReal)⁻¹ :=
    hdeltaThreshold.trans
      (frostmanOnePointwisePackingThreshold_le_half C epsilon)
  have hraw := averageMultiplicity_le_pointwisePacking_geometricRHS
    D C pointCap hdelta hhalf hpoint hpointCap
  have hconstantTop : (2 * C) ^ (1 / 2 : Real) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top (by norm_num) hCtop
  have habsorb :
      (2 * C) ^ (1 / 2 : Real) ≤
        (delta : ENNReal) ^ (-epsilon) := by
    exact finiteConstant_le_delta_negativePower hconstantTop hepsilon hdelta
      (hdeltaThreshold.trans (min_le_left _ _))
  calc
    D.shading.averageMultiplicity ≤
        (2 * C) ^ (1 / 2 : Real) *
          (delta : ENNReal) ^ (-2 : Real) *
            D.actualFamilyVolume ^ (1 / 2 : Real) := hraw
    _ ≤ (delta : ENNReal) ^ (-epsilon) *
          (delta : ENNReal) ^ (-2 : Real) *
            D.actualFamilyVolume ^ (1 / 2 : Real) := by gcongr
    _ = frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon 1 := by
      unfold frostmanMultiplicityRHS
      norm_num

/-- A thin `FrostmanAtParameters 1` wrapper.  Its only extra input is the
actual pointwise packing theorem to be supplied by the geometric branch; the
pointwise-to-average and all numerical absorption are discharged here. -/
theorem frostmanAtParameters_one_of_pointwisePacking
    (C : ENNReal) {epsilon eta : Real}
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon)
    (hpacking :
      ∀ {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
        (D : ActualTubeDatum delta ι),
        D.IsAdmissible → FrostmanHypotheses D eta →
          ∃ pointCap : Nat,
            (∀ x, D.shading.pointMultiplicity x ≤ pointCap) ∧
            (pointCap : ENNReal) ≤
              C * (delta : ENNReal) ^ (-2 : Real)) :
    FrostmanAtParameters 1 epsilon eta
      (frostmanOnePointwisePackingThreshold C epsilon) := by
  intro delta ι _ _ D hD hdelta hF
  obtain ⟨pointCap, hpoint, hpointCap⟩ := hpacking D hD hF
  exact averageMultiplicity_le_frostmanOneRHS_of_pointwisePacking
    D C pointCap hD.delta_pos hdelta hCtop hepsilon hpoint hpointCap

#print axioms averageMultiplicity_le_natCap_of_pointwise_le
#print axioms averageMultiplicity_le_indexCard
#print axioms le_geometricMean_of_le_left_of_le_right
#print axioms indexCard_mul_half_delta_sq_le_actualFamilyVolume
#print axioms indexCard_le_two_mul_delta_rpow_neg_two_mul_actualFamilyVolume
#print axioms averageMultiplicity_le_pointwisePacking_geometricRHS
#print axioms averageMultiplicity_le_frostmanOneRHS_of_pointwisePacking
#print axioms frostmanAtParameters_one_of_pointwisePacking

end

end Family8FrostmanOneFromPointwisePackingV1
