import ArchonPhysics.PhyslibFPUTCanonicalQuadraticKernel
import ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure

/-!
# Closure calculus for finite quadratic FPUT energy expressions

This module packages finite sums of products of modal actions as explicit
quadratic kernels on the positive-frequency energy profile.
-/

namespace ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticKernel
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

/-- A scalar function of the positive modal-energy profile is represented by
a finite quadratic kernel. -/
def IsPositiveEnergyQuadratic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (field : PositiveEnergyProfile m → Real) : Prop :=
  ∃ kernel : PositiveFrequencyMode m → PositiveFrequencyMode m → Real,
    ∀ energy,
      field energy =
        ∑ i : PositiveFrequencyMode m, ∑ j : PositiveFrequencyMode m,
          kernel i j * energy i * energy j

theorem isPositiveEnergyQuadratic_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    IsPositiveEnergyQuadratic m (fun _ ↦ 0) := by
  refine ⟨fun _ _ ↦ 0, ?_⟩
  intro energy
  simp

theorem IsPositiveEnergyQuadratic.add
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {left right : PositiveEnergyProfile m → Real}
    (hleft : IsPositiveEnergyQuadratic m left)
    (hright : IsPositiveEnergyQuadratic m right) :
    IsPositiveEnergyQuadratic m (fun energy ↦ left energy + right energy) := by
  rcases hleft with ⟨leftKernel, hleft⟩
  rcases hright with ⟨rightKernel, hright⟩
  refine ⟨fun i j ↦ leftKernel i j + rightKernel i j, ?_⟩
  intro energy
  change left energy + right energy = _
  rw [hleft energy, hright energy]
  simp only [add_mul, Finset.sum_add_distrib]

theorem IsPositiveEnergyQuadratic.neg
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {field : PositiveEnergyProfile m → Real}
    (hfield : IsPositiveEnergyQuadratic m field) :
    IsPositiveEnergyQuadratic m (fun energy ↦ -field energy) := by
  rcases hfield with ⟨kernel, hkernel⟩
  refine ⟨fun i j ↦ -kernel i j, ?_⟩
  intro energy
  change -field energy = _
  rw [hkernel energy]
  simp only [neg_mul, Finset.sum_neg_distrib]

theorem IsPositiveEnergyQuadratic.sub
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {left right : PositiveEnergyProfile m → Real}
    (hleft : IsPositiveEnergyQuadratic m left)
    (hright : IsPositiveEnergyQuadratic m right) :
    IsPositiveEnergyQuadratic m (fun energy ↦ left energy - right energy) := by
  simpa only [sub_eq_add_neg] using hleft.add hright.neg

theorem IsPositiveEnergyQuadratic.const_mul
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {field : PositiveEnergyProfile m → Real}
    (constant : Real) (hfield : IsPositiveEnergyQuadratic m field) :
    IsPositiveEnergyQuadratic m (fun energy ↦ constant * field energy) := by
  rcases hfield with ⟨kernel, hkernel⟩
  refine ⟨fun i j ↦ constant * kernel i j, ?_⟩
  intro energy
  change constant * field energy = _
  rw [hkernel energy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem isPositiveEnergyQuadratic_sum
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {index : Type*} [Fintype index]
    (field : index → PositiveEnergyProfile m → Real)
    (hfield : ∀ a, IsPositiveEnergyQuadratic m (field a)) :
    IsPositiveEnergyQuadratic m (fun energy ↦ ∑ a, field a energy) := by
  classical
  choose kernel hkernel using hfield
  refine ⟨fun i j ↦ ∑ a, kernel a i j, ?_⟩
  intro energy
  change (∑ a, field a energy) = _
  simp_rw [hkernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  symm
  rw [Finset.sum_mul, Finset.sum_mul]

theorem isPositiveEnergyQuadratic_finsetSum
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {index : Type*} [Finite index]
    (set : Finset index)
    (field : index → PositiveEnergyProfile m → Real)
    (hfield : ∀ a ∈ set, IsPositiveEnergyQuadratic m (field a)) :
    IsPositiveEnergyQuadratic m
      (fun energy ↦ ∑ a ∈ set, field a energy) := by
  classical
  let _ := Fintype.ofFinite index
  let restricted : index → PositiveEnergyProfile m → Real :=
    fun a energy ↦ if a ∈ set then field a energy else 0
  have hrestricted : ∀ a, IsPositiveEnergyQuadratic m (restricted a) := by
    intro a
    by_cases ha : a ∈ set
    · simpa [restricted, ha] using hfield a ha
    · simpa [restricted, ha] using isPositiveEnergyQuadratic_zero m
  have hsum := isPositiveEnergyQuadratic_sum restricted hrestricted
  simpa [restricted] using hsum

theorem isPositiveEnergyQuadratic_modeActionProduct
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (first second : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) first *
      modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) second) := by
  refine ⟨extendedModeActionProductKernel m first second, ?_⟩
  exact fun energy ↦
    modeAction_mul_modeAction_eq_quadraticSum m energy first second

/-- The signed three-wave bracket is exactly quadratic in the complete
positive-frequency energy profile. -/
theorem isPositiveEnergyQuadratic_quadraticSignedCollisionFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      quadraticSignedCollisionFlux term
        (modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m))
        observed) := by
  unfold quadraticSignedCollisionFlux signedThreeWaveCollisionFlux
  simpa only [mul_assoc] using
    ((isPositiveEnergyQuadratic_modeActionProduct
      m (term.1 0) (term.1 1)).add
    ((isPositiveEnergyQuadratic_modeActionProduct
      m observed (term.1 1)).const_mul
        (quadraticInputInteractionSign term 0).coefficient)).add
      ((isPositiveEnergyQuadratic_modeActionProduct
        m observed (term.1 0)).const_mul
          (quadraticInputInteractionSign term 1).coefficient)

end

end ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
