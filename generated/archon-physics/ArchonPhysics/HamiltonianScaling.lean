import Mathlib
import ArchonPhysics.Lattice
import Physlib.ClassicalMechanics.HamiltonsEquations

/-!
# Finite polynomial lattice Hamiltonian and energy rescaling

This module records the finite-dimensional algebra behind the rescaling in
Wang--Fu--Zhang--Zhao, arXiv:1903.09502v2, p. 1, eq. (1).  It makes no claim
about microscopic thermalization or a kinetic time scale.
-/

namespace ArchonPhysics.HamiltonianScaling

noncomputable section

/-- The Physlib Hamilton-equation residual vanishes along the phase-space path. -/
def SatisfiesHamiltonEquations {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace Real X] [CompleteSpace X] (H : Time → X → X → Real)
    (p q : Time → X) : Prop :=
  ClassicalMechanics.hamiltonEqOp H p q = 0

/-- The coupling after extracting a positive energy scale. -/
def effectiveCoupling (lambda epsilon : Real) (n : Nat) : Real :=
  lambda * Real.rpow epsilon (((n : Real) - 2) / 2)

/-- The finite periodic-chain Hamiltonian with degree-`n` nearest-neighbour interaction. -/
def latticeHamiltonian {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (n : Nat) (lambda : Real) (p q : Lattice.Configuration N) : Real :=
  ∑ i : Lattice.Site N, (p i ^ 2 / (2 * m.mass i) +
    Lattice.forwardDifference q i ^ 2 / 2 +
      (lambda / (n : Real)) * Lattice.forwardDifference q i ^ n)

/-- Pointwise multiplication of a configuration by the square root of the energy scale. -/
def rescaleConfiguration {N : Nat} (epsilon : Real)
    (q : Lattice.Configuration N) : Lattice.Configuration N :=
  fun i => Real.sqrt epsilon * q i

/-- Formula-level specification of the Hamiltonian, rescaling, and coupling. -/
theorem rescalingData_spec {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (n : Nat) (lambda epsilon : Real) (p q : Lattice.Configuration N) :
    latticeHamiltonian m n lambda p q =
        (∑ i : Lattice.Site N,
          (p i ^ 2 / (2 * m.mass i) + Lattice.forwardDifference (N := N) q i ^ 2 / 2 +
            (lambda / (n : Real)) * Lattice.forwardDifference (N := N) q i ^ n)) ∧
      (∀ i : Lattice.Site N,
        rescaleConfiguration (N := N) epsilon q i = Real.sqrt epsilon * q i) ∧
      effectiveCoupling lambda epsilon n =
        lambda * Real.rpow epsilon (((n : Real) - 2) / 2) := by
  exact ⟨rfl, fun _ => rfl, rfl⟩

/-- Rescaling the phase-space configuration factors out the positive energy scale. -/
theorem latticeHamiltonian_rescale {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (n : Nat) (_hn : 3 ≤ n) (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (p q : Lattice.Configuration N) :
    latticeHamiltonian m n lambda (rescaleConfiguration epsilon p)
        (rescaleConfiguration epsilon q) =
      epsilon * latticeHamiltonian m n (effectiveCoupling lambda epsilon n) p q := by
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
      _ = Real.rpow epsilon 1 * Real.rpow epsilon (((n : Real) - 2) / 2) :=
        Real.rpow_add hepsilon _ _
      _ = epsilon * Real.rpow epsilon (((n : Real) - 2) / 2) := by
        norm_num
  have hdiff (r : Lattice.Configuration N) (i : Lattice.Site N) :
      Lattice.forwardDifference (rescaleConfiguration epsilon r) i =
        Real.sqrt epsilon * Lattice.forwardDifference r i := by
    simp only [Lattice.forwardDifference, rescaleConfiguration]
    ring
  unfold latticeHamiltonian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (Real.sqrt epsilon * p i) ^ 2 / (2 * m.mass i) +
      Lattice.forwardDifference (rescaleConfiguration epsilon q) i ^ 2 / 2 +
      (lambda / (n : Real)) * Lattice.forwardDifference (rescaleConfiguration epsilon q) i ^ n =
    epsilon * (p i ^ 2 / (2 * m.mass i) + Lattice.forwardDifference q i ^ 2 / 2 +
      (effectiveCoupling lambda epsilon n / (n : Real)) * Lattice.forwardDifference q i ^ n)
  rw [hdiff q i]
  simp only [mul_pow]
  rw [hsqrt_sq, hsqrt_pow]
  unfold effectiveCoupling
  ring

/-- The inverse-square effective-coupling law; this is algebraic only. -/
theorem effectiveCoupling_inv_sq (lambda epsilon : Real) (n : Nat) (hn : 3 ≤ n)
    (hepsilon : 0 < epsilon) (_hlambda : lambda ≠ 0) :
    (effectiveCoupling lambda epsilon n)⁻¹ ^ 2 =
      lambda⁻¹ ^ 2 * epsilon ^ (-((n - 2 : Nat) : Int)) := by
  have hn2 : 2 ≤ n := by omega
  have hcast : (((n : Real) - 2) / 2) * 2 = ((n - 2 : Nat) : Real) := by
    rw [Nat.cast_sub hn2]
    ring
  have hpow :
      (Real.rpow epsilon (((n : Real) - 2) / 2)) ^ 2 = epsilon ^ (n - 2) := by
    calc
      (Real.rpow epsilon (((n : Real) - 2) / 2)) ^ 2 =
          (Real.rpow epsilon (((n : Real) - 2) / 2)) ^ (2 : Real) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow epsilon ((((n : Real) - 2) / 2) * 2) :=
        (Real.rpow_mul (le_of_lt hepsilon) _ _).symm
      _ = Real.rpow epsilon ((n - 2 : Nat) : Real) := by rw [hcast]
      _ = epsilon ^ (n - 2) := Real.rpow_natCast epsilon (n - 2)
  have hinv : (Real.rpow epsilon (((n : Real) - 2) / 2))⁻¹ ^ 2 =
      epsilon ^ (-((n - 2 : Nat) : Int)) := by
    calc
      (Real.rpow epsilon (((n : Real) - 2) / 2))⁻¹ ^ 2 =
          ((Real.rpow epsilon (((n : Real) - 2) / 2)) ^ 2)⁻¹ := by
        rw [inv_pow]
      _ = (epsilon ^ (n - 2))⁻¹ := by rw [hpow]
      _ = epsilon ^ (-((n - 2 : Nat) : Int)) := by
        simpa only [zpow_natCast] using (zpow_neg epsilon ((n - 2 : Nat) : Int)).symm
  unfold effectiveCoupling
  calc
    (lambda * Real.rpow epsilon (((n : Real) - 2) / 2))⁻¹ ^ 2 =
        ((Real.rpow epsilon (((n : Real) - 2) / 2))⁻¹ * lambda⁻¹) ^ 2 := by
      rw [mul_inv_rev]
    _ = (Real.rpow epsilon (((n : Real) - 2) / 2))⁻¹ ^ 2 * lambda⁻¹ ^ 2 := by
      rw [mul_pow]
    _ = lambda⁻¹ ^ 2 * epsilon ^ (-((n - 2 : Nat) : Int)) := by
      rw [hinv]
      ring

/-- The adapter unfolds to the admitted Physlib Hamilton-equation operator. -/
theorem satisfiesHamiltonEquations_iff {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace Real X] [CompleteSpace X] (H : Time → X → X → Real)
    (p q : Time → X) :
    SatisfiesHamiltonEquations H p q ↔ ClassicalMechanics.hamiltonEqOp H p q = 0 := by
  rfl

end

end ArchonPhysics.HamiltonianScaling
