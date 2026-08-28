import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
import ArchonPhysics.FourWaveCollisionAlgebra

/-!
# Collision cancellation on trivial equal-mass FPUT pairings

The direct four-wave resonance shell consists of the two pairings
`(k₂,k₃)=(k₀,k₁)` and `(k₂,k₃)=(k₁,k₀)`.  Although their finite-time
resonance weight is large, their detailed-balance collision flux vanishes
identically for every action profile.  Thus they do not generate kinetic
redistribution; the nontrivial collision geometry is the Umklapp sector.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTTrivialPairingCollisionCancellation

open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.FourWaveCollisionAlgebra
open ArchonPhysics.Lattice

noncomputable section

theorem fourWaveInverseActionMismatch_pairing_left
    (n₀ n₁ : Real) :
    fourWaveInverseActionMismatch n₀ n₁ n₀ n₁ = 0 := by
  unfold fourWaveInverseActionMismatch
  ring

theorem fourWaveInverseActionMismatch_pairing_right
    (n₀ n₁ : Real) :
    fourWaveInverseActionMismatch n₀ n₁ n₁ n₀ = 0 := by
  unfold fourWaveInverseActionMismatch
  ring

theorem fourWaveCollisionFlux_pairing_left
    (n₀ n₁ : Real) :
    fourWaveCollisionFlux n₀ n₁ n₀ n₁ = 0 := by
  unfold fourWaveCollisionFlux
  rw [fourWaveInverseActionMismatch_pairing_left]
  ring

theorem fourWaveCollisionFlux_pairing_right
    (n₀ n₁ : Real) :
    fourWaveCollisionFlux n₀ n₁ n₁ n₀ = 0 := by
  unfold fourWaveCollisionFlux
  rw [fourWaveInverseActionMismatch_pairing_right]
  ring

/-- Collision flux after eliminating the fourth momentum on the fixed-output
finite shell. -/
def reducedTwoToTwoCollisionFlux
    {N : Nat} (action : Site N → Real) (k₀ k₁ k₂ : Site N) : Real :=
  fourWaveCollisionFlux
    (action k₀) (action k₁) (action k₂)
      (action (k₀ + k₁ - k₂))

@[simp] theorem reducedTwoToTwoCollisionFlux_pairing_left
    {N : Nat} (action : Site N → Real) (k₀ k₁ : Site N) :
    reducedTwoToTwoCollisionFlux action k₀ k₁ k₀ = 0 := by
  unfold reducedTwoToTwoCollisionFlux
  rw [show k₀ + k₁ - k₀ = k₁ by abel]
  exact fourWaveCollisionFlux_pairing_left _ _

@[simp] theorem reducedTwoToTwoCollisionFlux_pairing_right
    {N : Nat} (action : Site N → Real) (k₀ k₁ : Site N) :
    reducedTwoToTwoCollisionFlux action k₀ k₁ k₁ = 0 := by
  unfold reducedTwoToTwoCollisionFlux
  rw [show k₀ + k₁ - k₁ = k₀ by abel]
  exact fourWaveCollisionFlux_pairing_right _ _

/-- Any supplied resonance rate, including the exact finite-time FGR rate,
is annihilated by a direct pairing collision. -/
theorem rate_mul_reducedTwoToTwoCollisionFlux_pairing_left
    {N : Nat} (rate : Real) (action : Site N → Real)
    (k₀ k₁ : Site N) :
    rate * reducedTwoToTwoCollisionFlux action k₀ k₁ k₀ = 0 := by
  simp

theorem rate_mul_reducedTwoToTwoCollisionFlux_pairing_right
    {N : Nat} (rate : Real) (action : Site N → Real)
    (k₀ k₁ : Site N) :
    rate * reducedTwoToTwoCollisionFlux action k₀ k₁ k₁ = 0 := by
  simp

end

end ArchonPhysics.EqualMassPeriodicFPUTTrivialPairingCollisionCancellation
