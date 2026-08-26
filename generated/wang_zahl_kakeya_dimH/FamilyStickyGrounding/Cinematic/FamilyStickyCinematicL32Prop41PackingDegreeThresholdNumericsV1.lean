import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
import FamilyStickyCinematicL32PyzCriticalBinUniformityV1
import FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41PackingDegreeThresholdNumericsV1

open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

/-!
# The missing packing-to-degree numerical threshold

The canonical high branch supplies `24 * logCount <= degreeLower`.  Therefore
the exact additional scalar comparison needed to feed the global-scale
packing producer is a comparison of twice the packing cap with that high
threshold.  A convenient sufficient half-sized form is also recorded below.

The final theorem gives a concrete assignment satisfying every scalar and
dyadic-label relation exposed by the current norm-first canonical payload
pipeline while violating the desired packing-to-degree inequality.  Thus the
comparison cannot follow from the presently available high-branch data.
-/

/-- Direct composition of the missing packing budget with the existing high
degree threshold. -/
theorem two_mul_packingCap_le_degreeLower_of_highThreshold
    {radius globalScale : Real} {logCount degreeLower : Nat}
    (hpacking :
      2 * projectedCoefficientPackingCap radius globalScale <=
        24 * logCount)
    (hhigh : 24 * logCount <= degreeLower) :
    2 * projectedCoefficientPackingCap radius globalScale <= degreeLower :=
  hpacking.trans hhigh

/-- A slightly easier-to-produce sufficient comparison: one packing cap must
fit into twelve copies of the logarithmic budget. -/
theorem two_mul_packingCap_le_degreeLower_of_cap_le_twelve_logCount
    {radius globalScale : Real} {logCount degreeLower : Nat}
    (hpacking :
      projectedCoefficientPackingCap radius globalScale <= 12 * logCount)
    (hhigh : 24 * logCount <= degreeLower) :
    2 * projectedCoefficientPackingCap radius globalScale <= degreeLower := by
  apply two_mul_packingCap_le_degreeLower_of_highThreshold
    (logCount := logCount)
  · calc
      2 * projectedCoefficientPackingCap radius globalScale <=
          2 * (12 * logCount) := Nat.mul_le_mul_left 2 hpacking
      _ = 24 * logCount := by omega
  · exact hhigh

/-- The scalar and label relations currently exported by the canonical
payload high branch do not force the packing-to-degree threshold.

Here `radius = 2^-10`, the norm and tangency labels are both zero,
`globalScale = 1`, the final label is eleven, and the ambient cardinality is
2048.  The uniform dyadic slack fits in `logCount = 22`, and the high degree
condition holds with degree lower endpoint 1024.  Nevertheless the explicit
three-coordinate packing cap is `6145^3 + 1`, far larger than that endpoint.
-/
theorem exists_currentHighLabelData_without_packingDegreeThreshold :
    exists radius globalScale : Real,
      exists normLabel tangencyLabel finalLabel : Int,
        exists ambientCard logCount : Nat,
          0 < radius /\ radius <= 16 /\
          normLabel ∈ Finset.Icc (dyadicCeilBucket radius)
            (dyadicCeilBucket 16) /\
          globalScale = dyadicCeilUpper normLabel /\
          0 < globalScale /\ radius <= globalScale /\ globalScale <= 32 /\
          tangencyLabel ∈ Finset.Icc (dyadicCeilBucket radius)
            (dyadicCeilBucket (36 * globalScale)) /\
          finalLabel ∈ Finset.Icc (dyadicCeilBucket 1)
            (dyadicCeilBucket (ambientCard : Real)) /\
          pyzCriticalBinUniformSlack radius <= logCount /\
          24 * logCount <= pyzE2DegreeLower finalLabel /\
          not (2 * projectedCoefficientPackingCap radius globalScale <=
            pyzE2DegreeLower finalLabel) := by
  have hradiusBucket : dyadicCeilBucket ((1024 : Real)⁻¹) = -10 := by
    rw [show (1024 : Real) = 2 ^ 10 by norm_num]
    unfold dyadicCeilBucket
    rw [Real.logb_inv, Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hbucketOne : dyadicCeilBucket 1 = 0 := by
    norm_num [dyadicCeilBucket, Real.logb]
  have hbucketSixteen : dyadicCeilBucket 16 = 4 := by
    rw [show (16 : Real) = 2 ^ 4 by norm_num]
    unfold dyadicCeilBucket
    rw [Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hbucket2048 : dyadicCeilBucket (2048 : Real) = 11 := by
    rw [show (2048 : Real) = 2 ^ 11 by norm_num]
    unfold dyadicCeilBucket
    rw [Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hbucket1152 : dyadicCeilBucket (1152 : Real) <= 11 := by
    rw [← hbucket2048]
    exact dyadicCeilBucket_mono (by norm_num) (by norm_num)
  have hslack : pyzCriticalBinUniformSlack ((1024 : Real)⁻¹) <= 22 := by
    unfold pyzCriticalBinUniformSlack
      continuumCriticalSingleDyadicBinFactor
    rw [hradiusBucket]
    have hInt :
        dyadicCeilBucket (1152 : Real) + 1 - (-10) <= (22 : Int) := by
      omega
    have hNat := Int.toNat_le_toNat hInt
    norm_num at hNat ⊢
    exact hNat
  have hdegree : pyzE2DegreeLower 11 = 1024 := by
    norm_num [pyzE2DegreeLower, dyadicCeilUpper]
  have hcap :
      projectedCoefficientPackingCap ((1024 : Real)⁻¹) 1 =
        232041498626 := by
    norm_num [projectedCoefficientPackingCap]
    decide
  have hscale : dyadicCeilUpper 0 = 1 := by
    norm_num [dyadicCeilUpper]
  have htangencyUpper : 0 <= dyadicCeilBucket (36 : Real) := by
    have hmono := dyadicCeilBucket_mono (r := (1 : Real)) (s := 36)
      (by norm_num) (by norm_num)
    simpa [hbucketOne] using hmono
  refine ⟨(1024 : Real)⁻¹, 1, 0, 0, 11, 2048, 22, ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rw [Finset.mem_Icc, hradiusBucket, hbucketSixteen]
    norm_num
  constructor
  · exact hscale.symm
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rw [Finset.mem_Icc, hradiusBucket]
    exact ⟨by norm_num, by simpa using htangencyUpper⟩
  constructor
  · simp [Finset.mem_Icc, hbucketOne, hbucket2048]
  constructor
  · exact hslack
  constructor
  · rw [hdegree]
    norm_num
  · rw [hcap, hdegree]
    norm_num

#print axioms two_mul_packingCap_le_degreeLower_of_highThreshold
#print axioms two_mul_packingCap_le_degreeLower_of_cap_le_twelve_logCount
#print axioms exists_currentHighLabelData_without_packingDegreeThreshold

end
end FamilyStickyCinematicL32Prop41PackingDegreeThresholdNumericsV1
