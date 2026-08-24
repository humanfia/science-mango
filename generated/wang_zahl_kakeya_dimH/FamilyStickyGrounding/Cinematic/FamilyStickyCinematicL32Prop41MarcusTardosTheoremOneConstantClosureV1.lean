import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosQuadraticDichotomyV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneConstantClosureV1

open FamilyStickyCinematicL32Prop41MarcusTardosQuadraticDichotomyV1

/-!
# Constant bookkeeping after Marcus--Tardos Lemmas 3--5

This is only the numerical closure of Theorem 1.  The hypotheses named
`hmain`, `hweightSum`, `hreciprocal`, and `hweightedDepth` are exactly the
outputs still to be produced by the block/leader argument; no incidence
estimate is hidden here.
-/

/-- The three elementary paper weight bounds imply the product estimates
used in the two quadratic branches. -/
theorem paper_weight_product_bounds
    {k weightSum weightedDepth reciprocalSum : Real}
    (hk : 0 < k)
    (hreciprocal_nonneg : 0 ≤ reciprocalSum)
    (hweightSum : weightSum ≤ k)
    (hweightedDepth : weightedDepth ≤ 3 / k)
    (hreciprocal : reciprocalSum ≤ 4 * k) :
    weightSum * reciprocalSum ≤ 4 * k ^ 2 ∧
      weightedDepth * reciprocalSum ≤ 12 := by
  constructor
  · calc
      weightSum * reciprocalSum ≤ k * (4 * k) :=
        mul_le_mul hweightSum hreciprocal hreciprocal_nonneg hk.le
      _ = 4 * k ^ 2 := by ring
  · calc
      weightedDepth * reciprocalSum ≤ (3 / k) * (4 * k) :=
        mul_le_mul hweightedDepth hreciprocal hreciprocal_nonneg (by positivity)
      _ = 12 := by field_simp; norm_num

/-- Exact denominator-free consequences of the two constant-eight branches.
The constants are `64` and `384`; the latter is why the paper safely rounds
the square-root coefficient up to `21`. -/
theorem incidence_and_quadratic_dichotomy_bounds
    {n m d k p weightSum weightedDepth reciprocalSum : Real}
    (hn : 0 ≤ n) (hm : 0 < m) (hd : 0 ≤ d) (hk : 0 < k)
    (hp : 0 ≤ p)
    (hlower : d ^ 2 * m ^ 2 ≤ 2 * n * p)
    (hreciprocal_nonneg : 0 ≤ reciprocalSum)
    (hweightSum : weightSum ≤ k)
    (hweightedDepth : weightedDepth ≤ 3 / k)
    (hreciprocal : reciprocalSum ≤ 4 * k)
    (hbranch :
      p ≤ 8 * m ^ 2 * weightSum * reciprocalSum ∨
      p ^ 2 ≤ 8 * d ^ 2 * m ^ 3 * weightedDepth * reciprocalSum) :
    d ^ 2 ≤ 64 * n * k ^ 2 ∨
      d ^ 2 * m ≤ 384 * n ^ 2 := by
  obtain ⟨hWV, hUV⟩ := paper_weight_product_bounds hk hreciprocal_nonneg
    hweightSum hweightedDepth hreciprocal
  rcases hbranch with hfirst | hsecond
  · left
    have hpUpper : p ≤ 32 * m ^ 2 * k ^ 2 := by
      calc
        p ≤ 8 * m ^ 2 * (weightSum * reciprocalSum) := by
          simpa [mul_assoc] using hfirst
        _ ≤ 8 * m ^ 2 * (4 * k ^ 2) := by
          exact mul_le_mul_of_nonneg_left hWV (by positivity)
        _ = 32 * m ^ 2 * k ^ 2 := by ring
    have hfactor : m ^ 2 * d ^ 2 ≤ m ^ 2 * (64 * n * k ^ 2) := by
      calc
        m ^ 2 * d ^ 2 = d ^ 2 * m ^ 2 := by ring
        _ ≤ 2 * n * p := hlower
        _ ≤ 2 * n * (32 * m ^ 2 * k ^ 2) := by
          exact mul_le_mul_of_nonneg_left hpUpper (by positivity)
        _ = m ^ 2 * (64 * n * k ^ 2) := by ring
    exact le_of_mul_le_mul_left hfactor (sq_pos_of_pos hm)
  · right
    by_cases hd0 : d = 0
    · simp [hd0, hn]
    · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      have hpSqUpper : p ^ 2 ≤ 96 * d ^ 2 * m ^ 3 := by
        calc
          p ^ 2 ≤ 8 * d ^ 2 * m ^ 3 *
              (weightedDepth * reciprocalSum) := by
            simpa [mul_assoc] using hsecond
          _ ≤ 8 * d ^ 2 * m ^ 3 * 12 := by
            exact mul_le_mul_of_nonneg_left hUV (by positivity)
          _ = 96 * d ^ 2 * m ^ 3 := by ring
      have hlowerSq : (d ^ 2 * m ^ 2) ^ 2 ≤ (2 * n * p) ^ 2 := by
        exact (sq_le_sq₀ (by positivity) (by positivity)).2 hlower
      have hfactor : (d ^ 2 * m ^ 3) * (d ^ 2 * m) ≤
          (d ^ 2 * m ^ 3) * (384 * n ^ 2) := by
        calc
          (d ^ 2 * m ^ 3) * (d ^ 2 * m) =
              (d ^ 2 * m ^ 2) ^ 2 := by ring
          _ ≤ (2 * n * p) ^ 2 := hlowerSq
          _ = 4 * n ^ 2 * p ^ 2 := by ring
          _ ≤ 4 * n ^ 2 * (96 * d ^ 2 * m ^ 3) := by
            exact mul_le_mul_of_nonneg_left hpSqUpper (by positivity)
          _ = (d ^ 2 * m ^ 3) * (384 * n ^ 2) := by ring
      exact le_of_mul_le_mul_left hfactor (by positivity : 0 < d ^ 2 * m ^ 3)

/-- Direct closure from the paper's main quadratic inequality. -/
theorem main_inequality_implies_constant_bounds
    {n m d k p weightSum weightedDepth reciprocalSum : Real}
    (hn : 0 ≤ n) (hm : 0 < m) (hd : 0 ≤ d) (hk : 0 < k)
    (hp : 0 ≤ p) (hreciprocal_pos : 0 < reciprocalSum)
    (hlower : d ^ 2 * m ^ 2 ≤ 2 * n * p)
    (hweightSum : weightSum ≤ k)
    (hweightedDepth : weightedDepth ≤ 3 / k)
    (hreciprocal : reciprocalSum ≤ 4 * k)
    (hmain : -m * d ^ 2 * weightedDepth ≤
      p * weightSum - p ^ 2 / (4 * m ^ 2 * reciprocalSum)) :
    d ^ 2 ≤ 64 * n * k ^ 2 ∨
      d ^ 2 * m ≤ 384 * n ^ 2 := by
  exact incidence_and_quadratic_dichotomy_bounds hn hm hd hk hp hlower
    hreciprocal_pos.le hweightSum hweightedDepth hreciprocal
    (quadratic_dichotomy_eight hp hm hreciprocal_pos hmain)

#print axioms paper_weight_product_bounds
#print axioms incidence_and_quadratic_dichotomy_bounds
#print axioms main_inequality_implies_constant_bounds

end FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneConstantClosureV1
