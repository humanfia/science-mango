import ArchonPhysics.HamiltonianScaling

/-!
# Open-chain Hamiltonian and energy rescaling

The periodic-chain scaling theorem is already provided by
`HamiltonianScaling`.  This module proves the same algebraic identity for a
finite open chain.  The boundary changes the harmonic spectrum and collision
network, but it does not change the effective coupling obtained after the
energy-amplitude rescaling.
-/

namespace ArchonPhysics.OpenChainHamiltonianScaling

open ArchonPhysics.HamiltonianScaling

noncomputable section

/-- Nearest-neighbour difference on an open chain with `N + 1` sites and `N`
bonds. -/
def openForwardDifference {N : Nat} (q : Fin (N + 1) → Real)
    (i : Fin N) : Real :=
  q i.succ - q i.castSucc

/-- The finite open-chain Hamiltonian with a homogeneous degree-`n` bond
interaction. -/
def openLatticeHamiltonian {N : Nat} (mass : Fin (N + 1) → Real)
    (n : Nat) (lambda : Real)
    (p q : Fin (N + 1) → Real) : Real :=
  (∑ i, p i ^ 2 / (2 * mass i)) +
    ∑ i : Fin N,
      (openForwardDifference q i ^ 2 / 2 +
      (lambda / (n : Real)) * openForwardDifference q i ^ n)

/-- Pointwise amplitude rescaling on the open chain. -/
def rescaleOpenConfiguration {N : Nat} (epsilon : Real)
    (q : Fin (N + 1) → Real) : Fin (N + 1) → Real :=
  fun i => Real.sqrt epsilon * q i

/-- The open-chain difference operator is homogeneous under amplitude
rescaling. -/
theorem openForwardDifference_rescale {N : Nat} (epsilon : Real)
    (q : Fin (N + 1) → Real) (i : Fin N) :
    openForwardDifference (rescaleOpenConfiguration epsilon q) i =
      Real.sqrt epsilon * openForwardDifference q i := by
  simp only [openForwardDifference, rescaleOpenConfiguration]
  ring

/-- Extracting a positive energy scale gives exactly the same effective
coupling as for the periodic chain. -/
theorem openLatticeHamiltonian_rescale {N : Nat}
    (mass : Fin (N + 1) → Real) (n : Nat) (_hn : 3 ≤ n)
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (p q : Fin (N + 1) → Real) :
    openLatticeHamiltonian mass n lambda
        (rescaleOpenConfiguration epsilon p)
        (rescaleOpenConfiguration epsilon q) =
      epsilon * openLatticeHamiltonian mass n
        (effectiveCoupling lambda epsilon n) p q := by
  have hsqrt_sq : Real.sqrt epsilon ^ 2 = epsilon :=
    Real.sq_sqrt (le_of_lt hepsilon)
  have hsqrt_pow : Real.sqrt epsilon ^ n =
      epsilon * Real.rpow epsilon (((n : Real) - 2) / 2) := by
    calc
      Real.sqrt epsilon ^ n = (Real.rpow epsilon (1 / 2)) ^ n :=
        congrArg (fun x : Real => x ^ n) (Real.sqrt_eq_rpow epsilon)
      _ = (Real.rpow epsilon (1 / 2)) ^ (n : Real) :=
        (Real.rpow_natCast _ n).symm
      _ = Real.rpow epsilon ((1 / 2) * (n : Real)) :=
        (Real.rpow_mul (le_of_lt hepsilon) _ _).symm
      _ = Real.rpow epsilon (1 + (((n : Real) - 2) / 2)) := by
        congr 1
        ring
      _ = Real.rpow epsilon 1 *
          Real.rpow epsilon (((n : Real) - 2) / 2) :=
        Real.rpow_add hepsilon _ _
      _ = epsilon * Real.rpow epsilon (((n : Real) - 2) / 2) := by
        norm_num
  unfold openLatticeHamiltonian
  rw [mul_add]
  apply congrArg₂ (fun x y : Real => x + y)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    change (Real.sqrt epsilon * p i) ^ 2 / (2 * mass i) =
      epsilon * (p i ^ 2 / (2 * mass i))
    rw [mul_pow, hsqrt_sq]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [openForwardDifference_rescale]
    simp only [mul_pow]
    rw [hsqrt_sq, hsqrt_pow]
    unfold effectiveCoupling
    ring

/-- For a cubic-leading interaction, the shared open/periodic effective
coupling is `lambda * sqrt epsilon`. -/
theorem effectiveCoupling_cubic (lambda epsilon : Real) :
    effectiveCoupling lambda epsilon 3 = lambda * Real.sqrt epsilon := by
  unfold effectiveCoupling
  norm_num [Real.sqrt_eq_rpow]

/-- The inverse-square cubic kinetic scale is
`lambda⁻² * epsilon⁻¹`. -/
theorem effectiveCoupling_cubic_inv_sq
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (hlambda : lambda ≠ 0) :
    (effectiveCoupling lambda epsilon 3)⁻¹ ^ 2 =
      lambda⁻¹ ^ 2 * epsilon⁻¹ := by
  simpa using
    (effectiveCoupling_inv_sq lambda epsilon 3 (by norm_num)
      hepsilon hlambda)

end

end ArchonPhysics.OpenChainHamiltonianScaling
