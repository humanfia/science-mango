import ArchonPhysics.PhyslibInitialModalReference

/-!
# Consumer: physical initial data determine the free Picard reference

This consumer exposes the exact finite-volume bridge from physical Physlib
initial position and canonical momentum to the radial and torus-phase
parameters used by the quadratic first-Picard reference orbit.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibInitialModalReference

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibInitialModalReference
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Physical initial position is matched on every mode, including the
zero-frequency translation mode. -/
theorem problem_free_reference_position_matches_physlib_initial_data
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N) :
    freeWeightedConfiguration
        (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m) 0
        (physlibInitialReferencePhase m q₀ p₀) =
      physlibInitialModalPosition m q₀ := by
  exact freeWeightedConfiguration_physlibInitialReference_zero m q₀ p₀

/-- Positive-frequency momentum and complex amplitude are simultaneously
matched by the same, data-determined radial/phase parameters. -/
theorem problem_free_reference_momentum_and_amplitude_match_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N) (k : Lattice.Site N)
    (hfrequency : 0 < modeFrequency m k) :
    freeReferenceInitialModalMomentum
        (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m)
        (physlibInitialReferencePhase m q₀ p₀) k =
        physlibInitialModalMomentum m p₀ k ∧
      complexModeAmplitude (modeFrequency m k)
          (freeWeightedConfiguration
            (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m) 0
            (physlibInitialReferencePhase m q₀ p₀) k)
          (freeReferenceInitialModalMomentum
            (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m)
            (physlibInitialReferencePhase m q₀ p₀) k) =
        complexModeAmplitude (modeFrequency m k)
          (physlibInitialModalPosition m q₀ k)
          (physlibInitialModalMomentum m p₀ k) := by
  exact ⟨
    freeReferenceInitialModalMomentum_physlibInitialReference_of_pos
      m q₀ p₀ k hfrequency,
    complexModeAmplitude_physlibInitialReference_zero_of_pos
      m q₀ p₀ k hfrequency⟩

/-- The only extra condition needed for all-mode momentum matching is zero
canonical translation momentum on every zero-frequency mode. -/
theorem problem_free_reference_all_mode_momentum_matches
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N)
    (hzero : ∀ k, modeFrequency m k = 0 →
      physlibInitialModalMomentum m p₀ k = 0) :
    (fun k => freeReferenceInitialModalMomentum
        (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m)
        (physlibInitialReferencePhase m q₀ p₀) k) =
      physlibInitialModalMomentum m p₀ := by
  exact freeReferenceInitialModalMomentum_physlibInitialReference
    m q₀ p₀ hzero

#print axioms problem_free_reference_position_matches_physlib_initial_data
#print axioms problem_free_reference_momentum_and_amplitude_match_of_pos
#print axioms problem_free_reference_all_mode_momentum_matches

end

end ArchonPhysicsConsumers.Thermalization.PhyslibInitialModalReference
