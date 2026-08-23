import Mathlib

/-!
# Finite periodic lattice with positive masses

This module formalizes the finite one-dimensional periodic lattice used in
Wang--Fu--Zhang--Zhao, arXiv:1903.09502v2, p. 1, eq. (1), and p. 2,
eqs. (2)--(3).  It contains only deterministic positive mass data and the
formula-level mass actions needed for the finite Hamiltonian; it asserts no
random-mass law or thermalization conclusion.  See also
`references/Thermal_physics_README.md`, Sections 2.1, 3, and 8--9.
-/

namespace ArchonPhysics.Lattice

/-- The sites of a finite periodic chain of length `N`. -/
abbrev Site (N : Nat) : Type := ZMod N

/-- Real-valued configurations on the periodic sites. -/
abbrev Configuration (N : Nat) : Type := Site N → Real

/-- The locked concrete realization of sites and configurations. -/
theorem siteConfiguration_spec (N : Nat) :
    Site N = ZMod N ∧ Configuration N = (Site N → Real) := by
  exact ⟨rfl, rfl⟩

/-- The periodic forward nearest-neighbour difference. -/
def forwardDifference {N : Nat} (q : Configuration N) : Configuration N :=
  fun i => q (i + 1) - q i

/-- Pointwise expansion of the periodic forward difference. -/
theorem forwardDifference_apply {N : Nat} (q : Configuration N) (i : Site N) :
    forwardDifference q i = q (i + 1) - q i := rfl

/-- Forward differences telescope around a nonempty periodic chain. -/
theorem sum_forwardDifference {N : Nat} [NeZero N] (q : Configuration N) :
    ∑ i, forwardDifference q i = 0 := by
  have hshift : (∑ i : Site N, q (i + 1)) = ∑ i : Site N, q i := by
    exact Fintype.sum_equiv (Equiv.addRight 1) (fun i => q (i + 1)) q (fun _ => rfl)
  change (∑ i : Site N, (q (i + 1) - q i)) = 0
  rw [Finset.sum_sub_distrib, hshift, sub_self]

/-- A deterministic, pointwise strictly positive mass realization. -/
structure PositiveMassConfig (N : Nat) where
  /-- The mass at each periodic site. -/
  mass : Configuration N
  /-- Every site has strictly positive mass. -/
  mass_pos : ∀ i : Site N, 0 < mass i

noncomputable section

/-- Pointwise multiplication by the mass profile. -/
def massAction {N : Nat} (m : PositiveMassConfig N) (p : Configuration N) :
    Configuration N := fun i => m.mass i * p i

/-- Pointwise multiplication by the inverse mass profile. -/
def inverseMassAction {N : Nat} (m : PositiveMassConfig N) (p : Configuration N) :
    Configuration N := fun i => (m.mass i)⁻¹ * p i

/-- Pointwise multiplication by the square root of the mass profile. -/
def sqrtMassAction {N : Nat} (m : PositiveMassConfig N) (p : Configuration N) :
    Configuration N := fun i => Real.sqrt (m.mass i) * p i

/-- Pointwise multiplication by the inverse square root of the mass profile. -/
def inverseSqrtMassAction {N : Nat} (m : PositiveMassConfig N) (p : Configuration N) :
    Configuration N := fun i => (Real.sqrt (m.mass i))⁻¹ * p i

/-- The finite kinetic energy `∑ᵢ pᵢ²/(2mᵢ)`. -/
def kineticEnergy {N : Nat} [NeZero N] (m : PositiveMassConfig N)
    (p : Configuration N) : Real :=
  ∑ i, p i ^ 2 / (2 * m.mass i)

/-- Formula-level expansion of the mass actions and kinetic energy. -/
theorem massAlgebra_spec {N : Nat} [NeZero N] (m : PositiveMassConfig N) :
    (∀ (p : Configuration N) (i : Site N), massAction m p i = m.mass i * p i) ∧
      (∀ (p : Configuration N) (i : Site N), inverseMassAction m p i = (m.mass i)⁻¹ * p i) ∧
      (∀ (p : Configuration N) (i : Site N), sqrtMassAction m p i = Real.sqrt (m.mass i) * p i) ∧
      (∀ (p : Configuration N) (i : Site N),
        inverseSqrtMassAction m p i = (Real.sqrt (m.mass i))⁻¹ * p i) ∧
      (∀ p : Configuration N, kineticEnergy m p = ∑ i, p i ^ 2 / (2 * m.mass i)) := by
  exact ⟨(fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl),
    (fun _ => rfl)⟩

/-- Kinetic energy is nonnegative for a pointwise strictly positive mass profile. -/
theorem kineticEnergy_nonneg {N : Nat} [NeZero N] (m : PositiveMassConfig N)
    (p : Configuration N) : 0 ≤ kineticEnergy m p := by
  unfold kineticEnergy
  refine Finset.sum_nonneg ?_
  intro i _
  exact div_nonneg (sq_nonneg (p i))
    (le_of_lt (mul_pos (by norm_num) (m.mass_pos i)))

end

end ArchonPhysics.Lattice
