import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosCorollarySixBucketingNumericsV1

/-!
# Dyadic counting kernel for Marcus--Tardos Corollary 6

The source uses thresholds

`t_k = c √n log n + 2^k c n / √m`

and obtains the bucket estimate `m_k ≤ m / 4^k` by pruning the lists in
bucket `k` to length `t_k` and applying the uniform theorem.  This module
formalizes the remaining finite geometric-series summation, with the exact
factor `4`.  It does not assume or restate the uniform intersection-reverse
estimate.
-/

/-- A finite half-geometric sum is at most two. -/
theorem sum_half_pow_le_two (L : Nat) :
    (∑ k ∈ Finset.range L, ((1 / 2 : Real) ^ k)) ≤ 2 := by
  have hgeom := geom_sum_mul_neg (1 / 2 : Real) L
  have hgeom' :
      (∑ k ∈ Finset.range L, ((1 / 2 : Real) ^ k)) * (1 / 2) =
        1 - (1 / 2 : Real) ^ L := by
    norm_num at hgeom ⊢
    exact hgeom
  have hpow : 0 ≤ (1 / 2 : Real) ^ L := by positivity
  nlinarith

/-- The paper's bucket cap `4^k m_k ≤ m` implies the exact weighted sum
bound `Σ 2^(k+1)m_k ≤ 4m`.  This denominator-free hypothesis works also
when a bucket is empty. -/
theorem weighted_bucket_count_le_four
    (L : Nat) (bucketCount : Nat → Real) (m : Real)
    (hm : 0 ≤ m)
    (hcap : ∀ k < L,
      (4 : Real) ^ k * bucketCount k ≤ m) :
    (∑ k ∈ Finset.range L,
      (2 : Real) ^ (k + 1) * bucketCount k) ≤ 4 * m := by
  have hterm : ∀ k < L,
      (2 : Real) ^ (k + 1) * bucketCount k ≤
        2 * m * (1 / 2 : Real) ^ k := by
    intro k hk
    have hx : 0 < (2 : Real) ^ k := by positivity
    have hfour : (4 : Real) ^ k = ((2 : Real) ^ k) ^ 2 := by
      rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow, pow_two]
    have hxmk : (2 : Real) ^ k * bucketCount k ≤
        m / (2 : Real) ^ k := by
      apply (le_div_iff₀ hx).2
      calc
        (2 : Real) ^ k * bucketCount k * (2 : Real) ^ k =
            (4 : Real) ^ k * bucketCount k := by rw [hfour]; ring
        _ ≤ m := hcap k hk
    calc
      (2 : Real) ^ (k + 1) * bucketCount k =
          2 * ((2 : Real) ^ k * bucketCount k) := by
        rw [pow_succ]
        ring
      _ ≤ 2 * (m / (2 : Real) ^ k) := by nlinarith
      _ = 2 * m * (1 / 2 : Real) ^ k := by
        rw [one_div, inv_pow]
        ring
  calc
    (∑ k ∈ Finset.range L,
        (2 : Real) ^ (k + 1) * bucketCount k) ≤
        ∑ k ∈ Finset.range L,
          2 * m * (1 / 2 : Real) ^ k := by
      exact Finset.sum_le_sum fun k hk ↦ hterm k (Finset.mem_range.mp hk)
    _ = 2 * m *
        (∑ k ∈ Finset.range L, (1 / 2 : Real) ^ k) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * m * 2 := by
      exact mul_le_mul_of_nonneg_left (sum_half_pow_le_two L) (by positivity)
    _ = 4 * m := by ring

/-- Finite form of the complete Corollary 6 summation.  `baseline` is
`c√n log n`, `step` is `c n / √m`, and `bucketMass k` is the total original
length in bucket `k`. -/
theorem bucket_mass_sum_le_baseline_mul_add_four_step_mul
    (L : Nat) (bucketCount bucketMass : Nat → Real)
    (m baseline step : Real)
    (hm : 0 ≤ m) (hbaseline : 0 ≤ baseline) (hstep : 0 ≤ step)
    (hcountSum : (∑ k ∈ Finset.range L, bucketCount k) ≤ m)
    (hcap : ∀ k < L,
      (4 : Real) ^ k * bucketCount k ≤ m)
    (hmass : ∀ k < L,
      bucketMass k ≤ bucketCount k *
        (baseline + (2 : Real) ^ (k + 1) * step)) :
    (∑ k ∈ Finset.range L, bucketMass k) ≤
      baseline * m + 4 * step * m := by
  have hweighted := weighted_bucket_count_le_four L bucketCount m hm hcap
  calc
    (∑ k ∈ Finset.range L, bucketMass k) ≤
        ∑ k ∈ Finset.range L,
          bucketCount k *
            (baseline + (2 : Real) ^ (k + 1) * step) := by
      exact Finset.sum_le_sum fun k hk ↦ hmass k (Finset.mem_range.mp hk)
    _ = baseline * (∑ k ∈ Finset.range L, bucketCount k) +
        step * (∑ k ∈ Finset.range L,
          (2 : Real) ^ (k + 1) * bucketCount k) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        ring
      · apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ baseline * m + step * (4 * m) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcountSum hbaseline)
        (mul_le_mul_of_nonneg_left hweighted hstep)
    _ = baseline * m + 4 * step * m := by ring

#print axioms sum_half_pow_le_two
#print axioms weighted_bucket_count_le_four
#print axioms bucket_mass_sum_le_baseline_mul_add_four_step_mul

end FamilyStickyCinematicL32Prop41MarcusTardosCorollarySixBucketingNumericsV1
