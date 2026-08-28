import ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound

/-!
# Consumer: explicit finite-volume observed-child acoustic bound

This consumer exposes the deterministic positive-frequency floor, the
resulting inverse-frequency moment bound, and the fully explicit q-level
off-resonant inverse-time estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector

noncomputable section

/-- Consumer endpoint for the explicit positive-mode spectral floor. -/
theorem problem_modeFrequencySq_ge_explicit_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper : Real) (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (mode : Lattice.Site N) (hmodeFrequency : 0 < modeFrequency m mode) :
    (4 * mUpper * (N : Real) ^ 3)⁻¹ ≤ modeFrequencySq m mode :=
  modeFrequencySq_ge_explicit_of_pos
    m mUpper hmUpper hmassUpper mode hmodeFrequency

/-- Consumer endpoint for the complete acoustic inverse moment. -/
theorem problem_observedChildAcousticInverseMoment_le_explicit_sqrt
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper : Real) (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (observed : Lattice.Site N) :
    FreeFPUTQLevelOffResonantVolumeBound.observedChildAcousticInverseMoment
        m observed ≤
      Real.sqrt (4 * mUpper * (N : Real) ^ 3) :=
  observedChildAcousticInverseMoment_le_explicit_sqrt
    m mUpper hmUpper hmassUpper observed

/-- Consumer endpoint for the fully explicit inverse-time q-level correction. -/
theorem problem_abs_qLevelOffResonantCorrectionSum_le_explicit_acoustic_floor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling mUpper : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    {time : Real} (hTime : 0 < time) :
    |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 *
          Real.sqrt (4 * mUpper * (N : Real) ^ 3) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed) / time :=
  abs_qLevelOffResonantCorrectionSum_le_explicit_acoustic_floor_over_time
    m kappa energy observed energyBound ceiling mUpper hsimple
    hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency
    hmUpper hmassUpper hTime

#print axioms problem_modeFrequencySq_ge_explicit_of_pos
#print axioms problem_observedChildAcousticInverseMoment_le_explicit_sqrt
#print axioms
  problem_abs_qLevelOffResonantCorrectionSum_le_explicit_acoustic_floor

end

end ArchonPhysicsConsumers.Thermalization
