import ArchonPhysics.FrozenInteractionTensorExtensiveLowerBound

/-!
# Extensive lower bound for frozen collision mass

The extensive tensor-square lower bound is combined with the uniform
frequency ceiling.  Consequently the unnormalized physical collision mass
is bounded below by a fixed positive constant times the number of sites.
-/

namespace ArchonPhysics.FrozenCollisionMassExtensiveLowerBound

open ArchonPhysics
open ArchonPhysics.FrozenCollisionMassQuantitativeLowerBound
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.FrozenInteractionTensorExtensiveLowerBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

noncomputable section

/-- Per-site lower constant inherited by the physically frequency-normalized
positive collision weight. -/
def iidCollisionWeightDensityLower : Real :=
  ((2 * Real.sqrt 5)⁻¹) ^ 3 * (125 / 36)

theorem iidCollisionWeightDensityLower_pos :
    0 < iidCollisionWeightDensityLower := by
  unfold iidCollisionWeightDensityLower
  positivity

/-- The unnormalized positive collision mass is extensive. -/
theorem iid_collisionWeight_extensive_lower
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (hN : 3 ≤ N)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega))) :
    iidCollisionWeightDensityLower * (N : Real) ≤
      positiveOrderedTotalInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have htensor :
      (125 / 36 : Real) * (N : Real) ≤
        ∑ modes : Fin 3 → Lattice.Site N,
          (interactionTensor m 3 modes) ^ 2 := by
    simpa [m] using iid_tensorSquare_extensive_lower ensemble omega hN
  have hfrequency : ∀ k, modeFrequency m k ≤ Real.sqrt 5 := by
    intro k
    have hk := iid_orderedModeFrequency_harmonic_le_sqrt_five
      ensemble omega (orderedIndexEquiv.symm k)
    rw [orderedModeFrequency_harmonicHermitian_eq] at hk
    simpa [m] using hk
  have htransfer :=
    constant_mul_tensorSquareSum_le_positiveOrderedTotalInteractionWeight
      m hsimple (Real.sqrt 5) (by positivity) hfrequency
  have hconstantNonneg : 0 ≤ ((2 * Real.sqrt 5)⁻¹) ^ 3 := by
    positivity
  calc
    iidCollisionWeightDensityLower * (N : Real) =
        ((2 * Real.sqrt 5)⁻¹) ^ 3 *
          ((125 / 36 : Real) * (N : Real)) := by
      unfold iidCollisionWeightDensityLower
      ring
    _ ≤ ((2 * Real.sqrt 5)⁻¹) ^ 3 *
          (∑ modes : Fin 3 → Lattice.Site N,
            (interactionTensor m 3 modes) ^ 2) :=
      mul_le_mul_of_nonneg_left htensor hconstantNonneg
    _ ≤ positiveOrderedTotalInteractionWeight m := htransfer

/-- Bundled finite-measure version of the extensive lower bound. -/
theorem iid_collisionWeight_extensive_lower_toNNReal_le_mass
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (hN : 3 ≤ N)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega)))
    (sign : Fin 3 → InteractionSign) :
    Real.toNNReal (iidCollisionWeightDensityLower * (N : Real)) ≤
      (positiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign).mass := by
  rw [positiveWeightedMismatchFiniteMeasure_mass_eq_toNNReal]
  exact Real.toNNReal_mono
    (iid_collisionWeight_extensive_lower ensemble omega hN hsimple)

end

end ArchonPhysics.FrozenCollisionMassExtensiveLowerBound
