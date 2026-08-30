import ArchonPhysics.LocalCollisionMarkContinuity

/-!
# Quantitative perturbation of ordered phase mismatch

Continuity of the ordered spectrum is enough for qualitative localization,
but a finite-volume block argument needs a radius that can be compared with
the actual boundary matrix.  This file records the corresponding explicit
estimate.  The totalized real square root is `1/2`-Hölder, and the all-index
Weyl theorem therefore gives, for an `n`-leg ordered mismatch,

`|mismatch A - mismatch B| <= n * sqrt ‖A - B‖op`.

No simplicity, spectral gap, positivity, or model-specific certificate is
used.  In particular the result remains valid for the totalized frequencies
of arbitrary Hermitian matrices.
-/

namespace ArchonPhysics.OrderedPhaseMismatchQuantitativePerturbation

open ArchonPhysics
open ArchonPhysics.MarkedEmpiricalResonanceTransfer
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSpectrumContinuity

noncomputable section

/-- The totalized real square root is globally `1/2`-Hölder with constant
one.  This formulation is also valid when either input is negative. -/
theorem abs_sqrt_sub_sqrt_le_sqrt_abs_sub (a b : Real) :
    |Real.sqrt a - Real.sqrt b| <= Real.sqrt |a - b| := by
  apply Real.abs_le_sqrt
  by_cases ha : 0 <= a
  · by_cases hb : 0 <= b
    · by_cases hab : a <= b
      · have hsqrt : Real.sqrt a <= Real.sqrt b :=
          Real.sqrt_le_sqrt hab
        have hmul : Real.sqrt a * Real.sqrt a <=
            Real.sqrt a * Real.sqrt b :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg a)
        rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
      · have hba : b <= a := le_of_not_ge hab
        have hsqrt : Real.sqrt b <= Real.sqrt a :=
          Real.sqrt_le_sqrt hba
        have hmul : Real.sqrt b * Real.sqrt b <=
            Real.sqrt b * Real.sqrt a :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg b)
        rw [abs_of_nonneg (sub_nonneg.mpr hba)]
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
    · have hb0 : b <= 0 := le_of_not_ge hb
      have hsqrtB : Real.sqrt b = 0 := Real.sqrt_eq_zero'.2 hb0
      have hba : b <= a := hb0.trans ha
      rw [hsqrtB, abs_of_nonneg (sub_nonneg.mpr hba)]
      nlinarith [Real.sq_sqrt ha]
  · have ha0 : a <= 0 := le_of_not_ge ha
    have hsqrtA : Real.sqrt a = 0 := Real.sqrt_eq_zero'.2 ha0
    by_cases hb : 0 <= b
    · have hab : a <= b := ha0.trans hb
      rw [hsqrtA, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
      nlinarith [Real.sq_sqrt hb]
    · have hb0 : b <= 0 := le_of_not_ge hb
      have hsqrtB : Real.sqrt b = 0 := Real.sqrt_eq_zero'.2 hb0
      simp [hsqrtA, hsqrtB]

/-- One ordered frequency changes by at most the square root of the operator
norm of the Hermitian perturbation. -/
theorem abs_orderedModeFrequency_sub_le_sqrt_clmNorm
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A B : HermitianMatrix iota) (k : Fin (Fintype.card iota)) :
    |orderedModeFrequency A k - orderedModeFrequency B k| <=
      Real.sqrt
        ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota)) (A.1 - B.1)‖ := by
  unfold orderedModeFrequency
  refine (abs_sqrt_sub_sqrt_le_sqrt_abs_sub _ _).trans ?_
  exact Real.sqrt_le_sqrt
    (abs_orderedEigenvalue_sub_le_clmNorm A.1 B.1 A.2 B.2 k)

/-- Explicit all-leg perturbation bound for a signed ordered phase mismatch.
The coefficient of every interaction sign has absolute value one. -/
theorem abs_orderedPhaseMismatch_sub_le_card_mul_sqrt_clmNorm
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {n : Nat} (A B : HermitianMatrix iota)
    (sign : Fin n -> InteractionSign)
    (modes : Fin n -> Fin (Fintype.card iota)) :
    |orderedPhaseMismatch A sign modes -
        orderedPhaseMismatch B sign modes| <=
      (n : Real) * Real.sqrt
        ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota)) (A.1 - B.1)‖ := by
  unfold orderedPhaseMismatch
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ r : Fin n,
        ((sign r).coefficient * orderedModeFrequency A (modes r) -
          (sign r).coefficient * orderedModeFrequency B (modes r))| <=
        ∑ _r : Fin n, Real.sqrt
          ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota))
            (A.1 - B.1)‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun r _hr => ?_)
      rw [← mul_sub, abs_mul]
      have hsign : |(sign r).coefficient| = 1 := by
        cases sign r <;> simp [InteractionSign.coefficient]
      rw [hsign, one_mul]
      exact abs_orderedModeFrequency_sub_le_sqrt_clmNorm A B (modes r)
    _ = (n : Real) * Real.sqrt
        ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota))
          (A.1 - B.1)‖ := by
      simp

/-- Margin form used by perturbative consumers: an operator-norm boundary
smaller than `(epsilon / n)^2` preserves an `epsilon` mismatch tolerance. -/
theorem abs_orderedPhaseMismatch_sub_lt_of_clmNorm_lt_sq
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {n : Nat} (hn : 0 < n) (A B : HermitianMatrix iota)
    (sign : Fin n -> InteractionSign)
    (modes : Fin n -> Fin (Fintype.card iota))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hboundary :
      ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota)) (A.1 - B.1)‖ <
        (epsilon / (n : Real)) ^ 2) :
    |orderedPhaseMismatch A sign modes -
        orderedPhaseMismatch B sign modes| < epsilon := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnormNonneg : 0 <=
      ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota)) (A.1 - B.1)‖ :=
    norm_nonneg _
  have hquotNonneg : 0 <= epsilon / (n : Real) :=
    div_nonneg hepsilon.le hnReal.le
  have hsqrt : Real.sqrt
      ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota)) (A.1 - B.1)‖ <
        epsilon / (n : Real) := by
    rw [Real.sqrt_lt hnormNonneg hquotNonneg]
    exact hboundary
  refine (abs_orderedPhaseMismatch_sub_le_card_mul_sqrt_clmNorm
    A B sign modes).trans_lt ?_
  calc
    (n : Real) * Real.sqrt
        ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := iota)) (A.1 - B.1)‖ <
        (n : Real) * (epsilon / (n : Real)) :=
      mul_lt_mul_of_pos_left hsqrt hnReal
    _ = epsilon := by field_simp

end

end ArchonPhysics.OrderedPhaseMismatchQuantitativePerturbation
