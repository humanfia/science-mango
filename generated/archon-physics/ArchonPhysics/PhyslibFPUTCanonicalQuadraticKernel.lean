import ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
import ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure

/-!
# Explicit finite quadratic kernels for the canonical FPUT Haar collision

This module removes the abstract linear-algebra part of the quadratic-kernel
obligation.  Modal actions of the zero-extended positive-frequency energy
profile are finite linear forms in the positive-frequency coordinates, so
every product of two modal actions has a canonical finite quadratic kernel.
-/

namespace ArchonPhysics.PhyslibFPUTCanonicalQuadraticKernel

open ArchonPhysics
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

noncomputable section

/-- Coefficient of one positive-frequency energy coordinate in the action of
an arbitrary full modal site.  It is zero on the translation sector. -/
def extendedModeActionCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (site : Lattice.Site N)
    (input : PositiveFrequencyMode m) : Real :=
  if h : 0 < modeFrequency m site then
    if input = ⟨site, h⟩ then 1 / modeFrequency m site else 0
  else 0

theorem modeAction_extendPositiveEnergyProfile_eq_sum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m) (site : Lattice.Site N) :
    modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) site =
      ∑ input : PositiveFrequencyMode m,
        extendedModeActionCoefficient m site input * energy input := by
  classical
  by_cases h : 0 < modeFrequency m site
  · simp [modeAction, extendPositiveEnergyProfile,
      extendedModeActionCoefficient, h, div_eq_mul_inv, mul_comm]
  · have hnonpos : ¬ 0 < modeFrequency m site := h
    simp [modeAction, extendPositiveEnergyProfile,
      extendedModeActionCoefficient, hnonpos]

/-- Kernel of the product of the actions in two arbitrary full modal sites. -/
def extendedModeActionProductKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (first second : Lattice.Site N) :
    PositiveFrequencyMode m → PositiveFrequencyMode m → Real :=
  fun i j ↦
    extendedModeActionCoefficient m first i *
      extendedModeActionCoefficient m second j

theorem modeAction_mul_modeAction_eq_quadraticSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m)
    (first second : Lattice.Site N) :
    modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) first *
        modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) second =
      ∑ i : PositiveFrequencyMode m, ∑ j : PositiveFrequencyMode m,
        extendedModeActionProductKernel m first second i j *
          energy i * energy j := by
  rw [modeAction_extendPositiveEnergyProfile_eq_sum,
    modeAction_extendPositiveEnergyProfile_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold extendedModeActionProductKernel
  ring

end

end ArchonPhysics.PhyslibFPUTCanonicalQuadraticKernel
