import ArchonPhysics.FreeFPUTA0DirectCubicBridge

/-!
# Consumer: the free `A0` character and direct cubic `A2` component

This consumer checks the one-character positive-frequency initial amplitude,
its explicit zero-frequency boundary, and the exact identification of the
Physlib direct cubic second-Picard component with the independent cubic
oscillatory family.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTA0DirectCubicBridge

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibInitialModalReference

open scoped Interval

noncomputable section

/-- A positive-frequency free initial mode is one finite phase character. -/
theorem positive_mode_a0_single_character_contract
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N)
    (hfrequency : 0 < frequency observed) :
    canonicalFreeComplexInitialAmplitude radius frequency phase observed =
      finitePhaseCorrection
        (freeInitialPhaseCoefficient radius frequency observed)
        (freeInitialPhaseCharge observed) phase :=
  canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
    radius frequency phase observed hfrequency

/-- The same one-character formula is fixed by actual Physlib initial data. -/
theorem physlib_a0_single_character_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N)
    (observed : Lattice.Site N)
    (hfrequency : 0 < modeFrequency m observed) :
    complexModeAmplitude (modeFrequency m observed)
        (physlibInitialModalPosition m q₀ observed)
        (physlibInitialModalMomentum m p₀ observed) =
      finitePhaseCorrection
        (freeInitialPhaseCoefficient
          (physlibInitialReferenceRadius m q₀ p₀)
          (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (physlibInitialReferencePhase m q₀ p₀) :=
  physlibInitialComplexAmplitude_eq_phaseFamily_of_pos
    m q₀ p₀ observed hfrequency

/-- Zero frequency is outside the physical complex-amplitude coordinate: its
totalized free amplitude and its formal one-term family both vanish. -/
theorem zero_mode_a0_boundary_contract
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N)
    (hzero : frequency observed = 0) :
    canonicalFreeComplexInitialAmplitude radius frequency phase observed = 0 ∧
      finitePhaseCorrection
        (freeInitialPhaseCoefficient radius frequency observed)
        (freeInitialPhaseCharge observed) phase = 0 :=
  ⟨canonicalFreeComplexInitialAmplitude_eq_zero_of_frequency_eq_zero
      radius frequency phase observed hzero,
    freeInitialPhaseFamily_eq_zero_of_frequency_eq_zero
      radius frequency phase observed hzero⟩

/-- Pointwise thin bridge from the P3 direct cubic source to the independent
cubic phase-expansion integrand. -/
theorem p3_direct_cubic_source_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibFreeCubicSecondPicardRotatedSource
        m beta observed radius phase time =
      physicalFreeCubicPicardIntegrand
        beta m observed radius (modeFrequency m) time phase :=
  physlibFreeCubicSecondPicardRotatedSource_eq_physicalIntegrand
    m beta observed radius phase time

/-- The integrated P3 direct cubic `A2` component is the exact finite
oscillatory character family. -/
theorem p3_direct_cubic_a2_oscillatory_family_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibFreeCubicSecondPicardCoefficient
        m beta observed radius phase time =
      finiteHaarOscillatorySum
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (modeFrequency m observed) beta)
          m observed radius)
        cubicPhaseCharge (cubicPhaseMismatch (modeFrequency m) observed)
        time phase :=
  physlibFreeCubicSecondPicardCoefficient_eq_oscillatoryFamily
    m beta observed radius phase time

#check FreeInitialPhaseTerm
#check freeInitialPhaseCharge
#check freeInitialPhaseCoefficient
#check physlibFreeCubicSecondPicardCoefficient

#print axioms positive_mode_a0_single_character_contract
#print axioms physlib_a0_single_character_contract
#print axioms zero_mode_a0_boundary_contract
#print axioms p3_direct_cubic_source_contract
#print axioms p3_direct_cubic_a2_oscillatory_family_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTA0DirectCubicBridge
