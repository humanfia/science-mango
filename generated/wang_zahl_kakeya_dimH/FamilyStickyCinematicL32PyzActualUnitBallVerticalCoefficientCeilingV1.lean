import FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

noncomputable section

/-!
# A fixed coefficient ceiling from the actual normalized tube geometry

Unit-ball containment bounds all base coordinates by one.  The source's
fixed upper vertical chart gives `1/2 ≤ |direction 2|`, hence both graph
slopes have absolute value at most two.  Consequently the graph intercepts
have absolute value at most three and the reduced `(a,b,d)` L1 diameter is
at most `16`.  This produces the norm critical-score comparison ceiling
from actual geometry rather than a finite-family maximum.
-/

theorem abs_axis_direction_apply_le_one
    {radius : NNReal} (T : Tube radius) (i : Fin 3) :
    |T.axis.direction i| ≤ 1 := by
  have hi := PiLp.norm_apply_le T.axis.direction i
  simpa only [Real.norm_eq_abs, T.axis.norm_direction] using hi

theorem abs_axis_base_apply_le_one_of_carrier_subset_unitBall
    {radius : NNReal} (T : Tube radius)
    (hunit : T.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (i : Fin 3) : |T.axis.base i| ≤ 1 := by
  have hbaseMem := hunit
    (T.axis_subset_carrier T.axis.base_mem_carrier)
  have hbaseNorm : ‖T.axis.base‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hbaseMem
  have hi := PiLp.norm_apply_le T.axis.base i
  simpa only [Real.norm_eq_abs] using hi.trans hbaseNorm

theorem abs_projectedTubeGraphC_le_two_of_vertical_half
    {radius : NNReal} {T : Tube radius}
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    |projectedTubeGraphC T| ≤ 2 := by
  unfold projectedTubeGraphC
  rw [abs_div]
  have hden : 0 < |T.axis.direction 2| := by linarith
  apply (div_le_iff₀ hden).2
  have hnum := abs_axis_direction_apply_le_one T (0 : Fin 3)
  nlinarith

theorem abs_projectedTubeGraphD_le_two_of_vertical_half
    {radius : NNReal} {T : Tube radius}
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    |projectedTubeGraphD T| ≤ 2 := by
  unfold projectedTubeGraphD
  rw [abs_div]
  have hden : 0 < |T.axis.direction 2| := by linarith
  apply (div_le_iff₀ hden).2
  have hnum := abs_axis_direction_apply_le_one T (1 : Fin 3)
  nlinarith

theorem abs_projectedTubeGraphA_le_three_of_unitBall_vertical_half
    {radius : NNReal} {T : Tube radius}
    (hunit : T.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    |projectedTubeGraphA T| ≤ 3 := by
  have hbase0 :=
    abs_axis_base_apply_le_one_of_carrier_subset_unitBall T hunit (0 : Fin 3)
  have hbase2 :=
    abs_axis_base_apply_le_one_of_carrier_subset_unitBall T hunit (2 : Fin 3)
  have hc := abs_projectedTubeGraphC_le_two_of_vertical_half hvertical
  unfold projectedTubeGraphA
  calc
    |T.axis.base 0 - projectedTubeGraphC T * T.axis.base 2| ≤
        |T.axis.base 0| + |projectedTubeGraphC T * T.axis.base 2| := by
      simpa [sub_eq_add_neg, abs_neg] using
        (abs_add_le (T.axis.base 0)
          (-(projectedTubeGraphC T * T.axis.base 2)))
    _ = |T.axis.base 0| +
        |projectedTubeGraphC T| * |T.axis.base 2| := by rw [abs_mul]
    _ ≤ 3 := by nlinarith [abs_nonneg (projectedTubeGraphC T)]

theorem abs_projectedTubeGraphB_le_three_of_unitBall_vertical_half
    {radius : NNReal} {T : Tube radius}
    (hunit : T.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    |projectedTubeGraphB T| ≤ 3 := by
  have hbase1 :=
    abs_axis_base_apply_le_one_of_carrier_subset_unitBall T hunit (1 : Fin 3)
  have hbase2 :=
    abs_axis_base_apply_le_one_of_carrier_subset_unitBall T hunit (2 : Fin 3)
  have hd := abs_projectedTubeGraphD_le_two_of_vertical_half hvertical
  unfold projectedTubeGraphB
  calc
    |T.axis.base 1 - projectedTubeGraphD T * T.axis.base 2| ≤
        |T.axis.base 1| + |projectedTubeGraphD T * T.axis.base 2| := by
      simpa [sub_eq_add_neg, abs_neg] using
        (abs_add_le (T.axis.base 1)
          (-(projectedTubeGraphD T * T.axis.base 2)))
    _ = |T.axis.base 1| +
        |projectedTubeGraphD T| * |T.axis.base 2| := by rw [abs_mul]
    _ ≤ 3 := by nlinarith [abs_nonneg (projectedTubeGraphD T)]

theorem projectedTubePairCoefficientDistance_le_sixteen
    {radius : NNReal} (T U : Tube radius)
    (hTunit : T.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hUunit : U.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hTvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|)
    (hUvertical : (1 / 2 : Real) ≤ |U.axis.direction 2|) :
    projectedTubePairCoefficientDistance T U ≤ 16 := by
  have hTA := abs_projectedTubeGraphA_le_three_of_unitBall_vertical_half
    hTunit hTvertical
  have hUA := abs_projectedTubeGraphA_le_three_of_unitBall_vertical_half
    hUunit hUvertical
  have hTB := abs_projectedTubeGraphB_le_three_of_unitBall_vertical_half
    hTunit hTvertical
  have hUB := abs_projectedTubeGraphB_le_three_of_unitBall_vertical_half
    hUunit hUvertical
  have hTD := abs_projectedTubeGraphD_le_two_of_vertical_half hTvertical
  have hUD := abs_projectedTubeGraphD_le_two_of_vertical_half hUvertical
  have hA : |projectedTubeGraphA T - projectedTubeGraphA U| ≤ 6 := by
    calc
      _ ≤ |projectedTubeGraphA T| + |projectedTubeGraphA U| := by
        simpa [sub_eq_add_neg, abs_neg] using
          (abs_add_le (projectedTubeGraphA T) (-projectedTubeGraphA U))
      _ ≤ 6 := by linarith
  have hB : |projectedTubeGraphB T - projectedTubeGraphB U| ≤ 6 := by
    calc
      _ ≤ |projectedTubeGraphB T| + |projectedTubeGraphB U| := by
        simpa [sub_eq_add_neg, abs_neg] using
          (abs_add_le (projectedTubeGraphB T) (-projectedTubeGraphB U))
      _ ≤ 6 := by linarith
  have hD : |projectedTubeGraphD T - projectedTubeGraphD U| ≤ 4 := by
    calc
      _ ≤ |projectedTubeGraphD T| + |projectedTubeGraphD U| := by
        simpa [sub_eq_add_neg, abs_neg] using
          (abs_add_le (projectedTubeGraphD T) (-projectedTubeGraphD U))
      _ ≤ 4 := by linarith
  simp only [projectedTubePairCoefficientDistance, coefficientDistance,
    projectedTubePairDeltaA, projectedTubePairDeltaB,
    projectedTubePairDeltaD]
  linarith

/-- The actual ambient critical family inherits the fixed ceiling from its
indexed ambient source.  This is the exact `hfull` shape consumed by norm
critical-score retention. -/
theorem ambientCriticalFamily_full_coefficientCeiling_sixteen
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient active : Finset iota)
    (hunit : ∀ i, i ∈ ambient →
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hvertical : ∀ i, i ∈ ambient →
      (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction 2|)
    (testCenter : Tube radius)
    (htestCenter : testCenter ∈
      actualProjectedAmbientCriticalFamily fine ambient active) :
    ∀ T, T ∈ actualProjectedAmbientCriticalFamily fine ambient active →
      projectedTubePairCoefficientDistance T testCenter ≤ 16 := by
  have htestImage :=
    actualProjectedAmbientCriticalFamily_subset fine ambient active htestCenter
  obtain ⟨j, hj, rfl⟩ :=
    (mem_activeTubeImage_iff fine ambient testCenter).mp htestImage
  intro T hT
  have hTImage := actualProjectedAmbientCriticalFamily_subset fine ambient active hT
  obtain ⟨i, hi, rfl⟩ := (mem_activeTubeImage_iff fine ambient T).mp hTImage
  exact projectedTubePairCoefficientDistance_le_sixteen
    (fine.tubes i) (fine.tubes j) (hunit i hi) (hunit j hj)
    (hvertical i hi) (hvertical j hj)

end
end FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
