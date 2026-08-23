import Mathlib
import ArchonPhysics
import Physlib.ClassicalMechanics.HamiltonsEquations

/-! Exact algebraic energy rescaling for a finite nonlinear lattice. -/

namespace ArchonPhysics.Generated.HamiltonianScaling

noncomputable section

/-- Periodic lattice sites and real fields. -/
abbrev Site (N : ℕ) := ZMod N
abbrev Field (N : ℕ) := Site N → ℝ

/-- The periodic forward difference. -/
def forwardDifference {N : ℕ} (q : Field N) (i : Site N) : ℝ :=
  q (i + 1) - q i

/-- Finite nonlinear lattice Hamiltonian with positive site masses. -/
def hamiltonian {N : ℕ} [NeZero N] (mass q p : Field N) (lam : ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sum (fun i : Site N =>
    p i ^ 2 / (2 * mass i) + forwardDifference q i ^ 2 / 2 +
      lam / n * forwardDifference q i ^ n)

/-- Rescaling of a field by `sqrt ε`. -/
def rescaleField {N : ℕ} (ε : ℝ) (q : Field N) : Field N :=
  fun i => Real.sqrt ε * q i

/-- The effective nonlinear coupling after the energy rescaling. -/
def effectiveCoupling (lam ε : ℝ) (n : ℕ) : ℝ :=
  lam * Real.rpow ε (((n : ℝ) - 2) / 2)

/-- The finite-dimensional Hamiltonian rescaling and its coupling identity.

This is purely algebraic; it makes no assertion about a thermalization time. -/
theorem hamiltonian_scaling_physics_formalization_target
    {N : ℕ} [NeZero N] (mass q p : Field N) (lam ε : ℝ) (n : ℕ)
    (hmass : ∀ i, 0 < mass i) (hε : 0 < ε) (hn : 3 ≤ n) (hlam : lam ≠ 0) :
    hamiltonian mass (rescaleField ε q) (rescaleField ε p) lam n =
      ε * hamiltonian mass q p (effectiveCoupling lam ε n) n ∧
    (effectiveCoupling lam ε n)⁻¹ ^ 2 =
      lam⁻¹ ^ 2 * ε ^ (-((n - 2 : ℕ) : ℤ)) := by
  have hn2 : 2 ≤ n := by omega
  have hsub : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    norm_num [Nat.cast_sub hn2]
  let a : ℝ := ((n : ℝ) - 2) / 2
  have hsqrt_pow : Real.sqrt ε ^ n = ε * ε ^ a := by
    calc
      Real.sqrt ε ^ n = ε ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      _ = ε ^ ((1 : ℝ) + a) := by
        dsimp [a]
        congr 1
        ring
      _ = ε ^ (1 : ℝ) * ε ^ a := by
        exact Real.rpow_add hε (1 : ℝ) _
      _ = ε * ε ^ a := by
        rw [Real.rpow_one]
  have hrpow_inv_sq : (ε ^ a)⁻¹ ^ 2 = ε ^ (-((n - 2 : ℕ) : ℤ)) := by
    calc
      (ε ^ a)⁻¹ ^ 2 = (ε ^ (-a)) ^ 2 := by
            rw [Real.rpow_neg hε.le]
      _ = (ε ^ (-a)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (ε ^ (-a)) 2).symm
      _ = ε ^ ((-a) * 2) := by
        exact (Real.rpow_mul hε.le (-a) 2).symm
      _ = ε ^ (-((n - 2 : ℕ) : ℝ)) := by
        dsimp [a]
        congr 1
        rw [hsub]
        ring
      _ = ε ^ (-((n - 2 : ℕ) : ℤ)) := by
        exact Real.rpow_neg_natCast ε (n - 2)
  have heff : effectiveCoupling lam ε n = lam * ε ^ a := by
    rfl
  constructor
  · have hdiff : ∀ i : Site N,
        forwardDifference (rescaleField ε q) i = Real.sqrt ε * forwardDifference q i := by
      intro i
      simp only [forwardDifference, rescaleField]
      ring
    unfold hamiltonian
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hdiff i]
    change
      (Real.sqrt ε * p i) ^ 2 / (2 * mass i) +
          (Real.sqrt ε * forwardDifference q i) ^ 2 / 2 +
          lam / n * (Real.sqrt ε * forwardDifference q i) ^ n =
        ε * (p i ^ 2 / (2 * mass i) + forwardDifference q i ^ 2 / 2 +
          effectiveCoupling lam ε n / n * forwardDifference q i ^ n)
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hε.le, hsqrt_pow, heff]
    ring
  · rw [heff, mul_inv_rev, mul_pow, hrpow_inv_sq]
    ring

end

end ArchonPhysics.Generated.HamiltonianScaling
