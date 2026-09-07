import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

namespace Family8SelfImprovementIterationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# Finite self-improvement iteration

This is the order-theoretic iteration used after a geometric one-step
self-improvement lemma has been proved.  It does not assert such a geometric
lemma.  Instead, `himprove` below is the theorem-level input that a later
Family 8 module must obtain from the Katz--Tao/Frostman argument.

The paper states that, for fixed target `beta`, a positive improvement
`nu gamma` exists when `gamma > beta`, and that it is monotone in `gamma`.
Pointwise positivity on the open interval is not by itself enough for finite
termination: a monotone increasing function may tend to zero at `beta` (for
example `(gamma - beta) / 2`).  The minimal quantitative input used by the
core theorem is therefore a positive uniform lower bound `step <= nu gamma`
on `(beta, 1]`.

The final iteration is not hidden inside a clamped geometric step.  The
geometric input gives `P (gamma - nu gamma)` literally.  If this exponent
overshoots `beta`, the separate hypothesis `htransport` transports the
stronger, lower-exponent property back up to the target exponent.  This is
the exponent monotonicity that an actual Katz--Tao or Frostman application
must prove.
-/

/-- The deterministic exponents used to count the iterations. -/
def clampedExponent (beta step : Real) (n : Nat) : Real :=
  max beta (1 - (n : Real) * step)

@[simp]
theorem clampedExponent_zero {beta step : Real} (hbeta : beta ≤ 1) :
    clampedExponent beta step 0 = 1 := by
  simp [clampedExponent, max_eq_right hbeta]

theorem beta_le_clampedExponent (beta step : Real) (n : Nat) :
    beta ≤ clampedExponent beta step n := by
  exact le_max_left _ _

theorem clampedExponent_le_one {beta step : Real} (n : Nat)
    (hbeta : beta ≤ 1) (hstep : 0 ≤ step) :
    clampedExponent beta step n ≤ 1 := by
  apply max_le hbeta
  have hmul : 0 ≤ (n : Real) * step :=
    mul_nonneg (Nat.cast_nonneg n) hstep
  linarith

theorem clampedExponent_succ {beta step : Real} (n : Nat)
    (hstep : 0 ≤ step) :
    clampedExponent beta step (n + 1) =
      max beta (clampedExponent beta step n - step) := by
  have hcast :
      1 - ((n + 1 : Nat) : Real) * step =
        (1 - (n : Real) * step) - step := by
    push_cast
    ring
  rw [clampedExponent, hcast, clampedExponent]
  by_cases h : beta ≤ 1 - (n : Real) * step
  · rw [max_eq_right h]
  · have hle : 1 - (n : Real) * step ≤ beta := le_of_not_ge h
    have hleft : (1 - (n : Real) * step) - step ≤ beta := by
      linarith
    have hright : beta - step ≤ beta := by
      linarith
    rw [max_eq_left hle, max_eq_left hleft, max_eq_left hright]

/-- A positive fixed decrement reaches the target after finitely many
clamped steps. -/
theorem exists_clampedExponent_eq_beta {beta step : Real}
    (hstep : 0 < step) :
    ∃ n : Nat, clampedExponent beta step n = beta := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 - beta) / step)
  have hmul : 1 - beta < (n : Real) * step := by
    exact (div_lt_iff₀ hstep).mp hn
  refine ⟨n, max_eq_left ?_⟩
  linarith

/-- Every exponent in the deterministic schedule inherits `P` from a
literal variable-size self-improvement, provided the latter has a positive
uniform lower bound. -/
theorem property_clampedExponent
    (P : Real → Prop) (nu : Real → Real) {beta step : Real}
    (hbeta : beta < 1) (hstep : 0 < step)
    (hbase : P 1)
    (htransport : ∀ ⦃lower upper : Real⦄, lower ≤ upper → P lower → P upper)
    (himprove : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      P gamma → P (gamma - nu gamma))
    (huniform : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      step ≤ nu gamma) :
    ∀ n : Nat, P (clampedExponent beta step n) := by
  intro n
  induction n with
  | zero =>
      rw [clampedExponent_zero hbeta.le]
      exact hbase
  | succ n ih =>
      rw [clampedExponent_succ n hstep.le]
      by_cases heq : clampedExponent beta step n = beta
      · have hstay :
            max beta (clampedExponent beta step n - step) = beta := by
          rw [heq]
          exact max_eq_left (by linarith)
        rw [hstay]
        simpa only [heq] using ih
      · have hlower : beta < clampedExponent beta step n :=
          lt_of_le_of_ne (beta_le_clampedExponent beta step n) (Ne.symm heq)
        have hupper : clampedExponent beta step n ≤ 1 :=
          clampedExponent_le_one n hbeta.le hstep.le
        have himproved :
            P (clampedExponent beta step n -
              nu (clampedExponent beta step n)) :=
          himprove (clampedExponent beta step n) hlower hupper ih
        apply htransport _ himproved
        have hlowerNu : step ≤ nu (clampedExponent beta step n) :=
          huniform (clampedExponent beta step n) hlower hupper
        exact (sub_le_sub_left hlowerNu _).trans (le_max_right _ _)

/-- Abstract finite bootstrap theorem with the exact minimal quantitative
supplement: `nu` has a positive uniform lower bound on `(beta, 1]`.

The last application of `himprove` may land below `beta`; `htransport`, not
the clamped schedule itself, is what proves `P beta` in that case. -/
theorem property_at_target_of_uniform_improvement
    (P : Real → Prop) (nu : Real → Real) {beta step : Real}
    (hbeta : beta < 1) (hstep : 0 < step)
    (hbase : P 1)
    (htransport : ∀ ⦃lower upper : Real⦄, lower ≤ upper → P lower → P upper)
    (himprove : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      P gamma → P (gamma - nu gamma))
    (huniform : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      step ≤ nu gamma) :
    P beta := by
  obtain ⟨n, hn⟩ := exists_clampedExponent_eq_beta hstep
  have hPn := property_clampedExponent P nu hbeta hstep hbase
    htransport himprove huniform n
  rw [hn] at hPn
  exact hPn

/-- Paper-shaped corollary when "monotone" means antitone in the ordinary
order on exponents.  Since every active exponent is at most `1`, positivity
at `1` gives the uniform lower bound `nu 1` automatically. -/
theorem property_at_target_of_antitone_improvement
    (P : Real → Prop) (nu : Real → Real) {beta : Real}
    (hbeta : beta < 1)
    (hbase : P 1)
    (htransport : ∀ ⦃lower upper : Real⦄, lower ≤ upper → P lower → P upper)
    (himprove : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      P gamma → P (gamma - nu gamma))
    (hpositive : ∀ gamma : Real, beta < gamma → gamma ≤ 1 → 0 < nu gamma)
    (hantitone : Antitone nu) :
    P beta := by
  apply property_at_target_of_uniform_improvement P nu hbeta
    (hpositive 1 hbeta le_rfl) hbase htransport himprove
  intro gamma _ hgamma
  exact hantitone hgamma

/-- Paper-shaped corollary when "monotone" has Lean's usual nondecreasing
meaning.  Positivity only for `gamma > beta` does not provide a uniform
step; the explicit endpoint condition `0 < nu beta` is the minimal closed-
interval supplement used here. -/
theorem property_at_target_of_monotone_improvement
    (P : Real → Prop) (nu : Real → Real) {beta : Real}
    (hbeta : beta < 1)
    (hbase : P 1)
    (htransport : ∀ ⦃lower upper : Real⦄, lower ≤ upper → P lower → P upper)
    (himprove : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      P gamma → P (gamma - nu gamma))
    (hmonotone : Monotone nu) (hpositiveAtBeta : 0 < nu beta) :
    P beta := by
  apply property_at_target_of_uniform_improvement P nu hbeta
    hpositiveAtBeta hbase htransport himprove
  intro gamma hgamma _
  exact hmonotone hgamma.le

#print axioms clampedExponent_zero
#print axioms beta_le_clampedExponent
#print axioms clampedExponent_le_one
#print axioms clampedExponent_succ
#print axioms exists_clampedExponent_eq_beta
#print axioms property_clampedExponent
#print axioms property_at_target_of_uniform_improvement
#print axioms property_at_target_of_antitone_improvement
#print axioms property_at_target_of_monotone_improvement

end

end Family8SelfImprovementIterationV1
