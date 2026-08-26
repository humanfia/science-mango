import ArchonPhysics.CoerciveCubicPotential

/-!
# The standard FPUT alpha-beta bond potential

This module records the standard single-bond FPUT alpha-beta potential

`V(x) = x²/2 + alpha*x³/3 + beta*x⁴/4`.

Besides its derivative, it proves a sharp quadratic lower bound in the
coercive parameter regime, identifies the potential exactly with the
amplitude-dependent specialization already used by
`CoerciveCubicPotential`, and gives its exact amplitude-rescaling law.
-/

namespace ArchonPhysics.AlphaBetaPotential

noncomputable section

/-- The standard FPUT alpha-beta bond potential. -/
def potential (alpha beta x : Real) : Real :=
  x ^ 2 / 2 + alpha * x ^ 3 / 3 + beta * x ^ 4 / 4

/-- The polynomial derivative of the FPUT alpha-beta bond potential. -/
def derivative (alpha beta x : Real) : Real :=
  x + alpha * x ^ 2 + beta * x ^ 3

/-- The displayed derivative is the derivative of `potential`. -/
theorem hasDerivAt_potential (alpha beta x : Real) :
    HasDerivAt (potential alpha beta) (derivative alpha beta x) x := by
  unfold potential derivative
  convert
    ((((hasDerivAt_id x).pow 2).div_const 2).add
      ((((hasDerivAt_id x).pow 3).const_mul alpha).div_const 3)).add
      ((((hasDerivAt_id x).pow 4).const_mul beta).div_const 4)
    using 1
  all_goals first
    | rfl
    | (simp [id]; ring)

/-- Formula for the `deriv` of the standard FPUT alpha-beta potential. -/
@[simp]
theorem deriv_potential (alpha beta x : Real) :
    deriv (potential alpha beta) x = derivative alpha beta x :=
  (hasDerivAt_potential alpha beta x).deriv

/-- Formula-level lock for the polynomial derivative. -/
theorem derivative_spec (alpha beta x : Real) :
    derivative alpha beta x = x + alpha * x ^ 2 + beta * x ^ 3 := rfl

/-- The potential is `x²` times a quadratic polynomial in the bond stretch. -/
theorem potential_factor (alpha beta x : Real) :
    potential alpha beta x =
      x ^ 2 * (1 / 2 + (alpha / 3) * x + (beta / 4) * x ^ 2) := by
  unfold potential
  ring

/-- The sharp quadratic coercivity constant obtained by completing the square. -/
def coercivityConstant (alpha beta : Real) : Real :=
  1 / 2 - alpha ^ 2 / (9 * beta)

/-- The coercive parameter inequality forces a positive quartic coefficient. -/
theorem beta_pos {alpha beta : Real} (hbeta : 2 * alpha ^ 2 / 9 < beta) :
    0 < beta := by
  have hthreshold : 0 ≤ 2 * alpha ^ 2 / 9 := by positivity
  exact lt_of_le_of_lt hthreshold hbeta

/-- Under `2*alpha²/9 < beta`, the quadratic coercivity constant is positive. -/
theorem coercivityConstant_pos {alpha beta : Real}
    (hbeta : 2 * alpha ^ 2 / 9 < beta) :
    0 < coercivityConstant alpha beta := by
  have hbetaPos : 0 < beta := beta_pos hbeta
  have hden : 0 < 9 * beta := mul_pos (by norm_num) hbetaPos
  have hfrac : alpha ^ 2 / (9 * beta) < 1 / 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith [hbeta]
  unfold coercivityConstant
  linarith

/-- Completing the square gives a uniform quadratic lower bound. -/
theorem potential_lower_bound {alpha beta : Real}
    (hbeta : 2 * alpha ^ 2 / 9 < beta) (x : Real) :
    coercivityConstant alpha beta * x ^ 2 ≤ potential alpha beta x := by
  have hbetaPos : 0 < beta := beta_pos hbeta
  have hbetaNe : beta ≠ 0 := ne_of_gt hbetaPos
  have hcomplete :
      alpha ^ 2 / (9 * beta) + (alpha / 3) * x + (beta / 4) * x ^ 2 =
        (beta / 4) * (x + 2 * alpha / (3 * beta)) ^ 2 := by
    field_simp [hbetaNe]
    ring
  have hsquare :
      0 ≤ alpha ^ 2 / (9 * beta) + (alpha / 3) * x + (beta / 4) * x ^ 2 := by
    rw [hcomplete]
    positivity
  have hquadratic :
      coercivityConstant alpha beta ≤
        1 / 2 + (alpha / 3) * x + (beta / 4) * x ^ 2 := by
    unfold coercivityConstant
    linarith
  rw [potential_factor]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hquadratic (sq_nonneg x))

/-- In the coercive parameter regime the potential is nonnegative. -/
theorem potential_nonneg {alpha beta : Real}
    (hbeta : 2 * alpha ^ 2 / 9 < beta) (x : Real) :
    0 ≤ potential alpha beta x := by
  calc
    0 ≤ coercivityConstant alpha beta * x ^ 2 :=
      mul_nonneg (le_of_lt (coercivityConstant_pos hbeta)) (sq_nonneg x)
    _ ≤ potential alpha beta x := potential_lower_bound hbeta x

/-- Away from the equilibrium stretch, the coercive potential is strictly positive. -/
theorem potential_pos {alpha beta x : Real}
    (hbeta : 2 * alpha ^ 2 / 9 < beta) (hx : x ≠ 0) :
    0 < potential alpha beta x := by
  have hxSq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  exact lt_of_lt_of_le
    (mul_pos (coercivityConstant_pos hbeta) hxSq)
    (potential_lower_bound hbeta x)

/--
The existing cubic-leading stabilized potential is exactly the specialization
`alpha = kappa*g`, `beta = beta0*g²` of the standard alpha-beta potential.
-/
theorem potential_eq_coerciveCubicPotential
    (kappa beta0 g x : Real) :
    potential (kappa * g) (beta0 * g ^ 2) x =
      CoerciveCubicPotential.potential kappa beta0 g x := by
  unfold potential CoerciveCubicPotential.potential
  ring

/-- The same exact specialization, oriented from the existing potential. -/
theorem coerciveCubicPotential_eq_potential
    (kappa beta0 g x : Real) :
    CoerciveCubicPotential.potential kappa beta0 g x =
      potential (kappa * g) (beta0 * g ^ 2) x :=
  (potential_eq_coerciveCubicPotential kappa beta0 g x).symm

/-- Rescaling the bond amplitude by `t` rescales and renormalizes the couplings exactly. -/
theorem potential_mul_rescale (alpha beta t x : Real) :
    potential alpha beta (t * x) =
      t ^ 2 * potential (alpha * t) (beta * t ^ 2) x := by
  unfold potential
  ring

/-- Exact square-root amplitude rescaling for a nonnegative scale. -/
theorem potential_sqrt_rescale_of_nonneg
    (alpha beta x : Real) {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    potential alpha beta (Real.sqrt epsilon * x) =
      epsilon * potential (alpha * Real.sqrt epsilon) (beta * epsilon) x := by
  simpa [Real.sq_sqrt hepsilon] using
    potential_mul_rescale alpha beta (Real.sqrt epsilon) x

/-- Exact square-root amplitude rescaling for a strictly positive scale. -/
theorem potential_sqrt_rescale_of_pos
    (alpha beta x : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    potential alpha beta (Real.sqrt epsilon * x) =
      epsilon * potential (alpha * Real.sqrt epsilon) (beta * epsilon) x :=
  potential_sqrt_rescale_of_nonneg alpha beta x (le_of_lt hepsilon)

/-- Formula-level lock for the potential and its coercivity constant. -/
theorem potential_spec (alpha beta x : Real) :
    potential alpha beta x =
        x ^ 2 / 2 + alpha * x ^ 3 / 3 + beta * x ^ 4 / 4 ∧
      coercivityConstant alpha beta = 1 / 2 - alpha ^ 2 / (9 * beta) := by
  exact ⟨rfl, rfl⟩

end

end ArchonPhysics.AlphaBetaPotential
