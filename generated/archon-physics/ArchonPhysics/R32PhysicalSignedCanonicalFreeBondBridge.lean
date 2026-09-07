import ArchonPhysics.R32CanonicalPhysicalFreeBondIdentificationV2
import ArchonPhysics.R32CanonicalExactFreeBridgeV3

/-!
# Physical signed Haar field as the canonical zero-coupling bond

The concentration carrier advances phases with the opposite time sign from
the physical harmonic flow.  The physical wrapper has already inserted that
time reversal.  This file records the resulting exact pointwise identity with
one component of the actual canonical `g = 0` global-flow bond vector.
-/

namespace ArchonPhysics.R32PhysicalSignedCanonicalFreeBondBridge

open ArchonPhysics

noncomputable section

/-- The raw-mass-only spelling used by the measurable physical signed field
is exactly the mass component of the canonical mass/phase sample. -/
theorem rawCanonicalFrozenMass_eq_canonicalMass
    {N : Nat} [NeZero N] (sample : RandomEnsemble.SampleSpace) :
    ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final.rawCanonicalFrozenMass
        (N := N) sample.1 =
      ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy.canonicalMass
        (N := N) sample := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  rfl

/-- The generic sampled-flow readout is definitionally the canonical
mass--phase trajectory position.  Keeping this fact separate makes clear
that the final bond theorem concerns the actual global flow rather than an
auxiliary explicit free solution. -/
theorem sampledCanonicalFreeFlowPosition_eq_canonicalFlowPosition
    {N : Nat} [NeZero N]
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : RandomEnsemble.SampleSpace) (time : Real) :
    ArchonPhysics.GlobalRandomMassModalObservable.sampledFlowPosition
        (ArchonPhysics.RandomMassPhaseLateWindowObservable.canonicalPhaseInitialSample
          (N := N) kappa beta 0 (1 / 4))
        (ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow.canonicalRandomMassPhaseGlobalFlow
          N kappa beta 0 hbeta)
        (sample, time) =
      ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy.canonicalFlowPosition
        (N := N)
        kappa beta 0 hbeta (1 / 4) (sample, time) := by
  rfl

/-- Exact physical-sign identification with one component of the actual
canonical zero-coupling global-flow bond vector.  The physical signed wrapper
already evaluates the concentration carrier at `-time`, so the displayed
global-flow time is `time`, not `-time`. -/
theorem physicalSignedHaarBondField_eq_sampledCanonicalFreeBond
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : ArchonPhysics.OrderedSingleModeProjector.SimpleOrderedSpectrum
      (ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian
        (ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final.rawCanonicalFrozenMass
          (N := N) sample.1)))
    (time : Real) (bond : Lattice.Site N) :
    ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final.physicalSignedHaarBondField
        (ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final.rawCanonicalFrozenMass
          (N := N) sample.1) bond
        (ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final.orderedPhaseBlockFromSequence
          (N := N) sample.2) time =
      ArchonPhysics.R32DiluteNonlinearStability.bondVector
        (ArchonPhysics.GlobalRandomMassModalObservable.sampledFlowPosition
          (ArchonPhysics.RandomMassPhaseLateWindowObservable.canonicalPhaseInitialSample
            (N := N) kappa beta 0 (1 / 4))
          (ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow.canonicalRandomMassPhaseGlobalFlow
            N kappa beta 0 hbeta)
          (sample, time)) bond := by
  rw [ArchonPhysics.R32PhysicalSignedCanonicalFreeBondBridge.rawCanonicalFrozenMass_eq_canonicalMass
    sample] at hsimple
  change _ = ArchonPhysics.R32DiluteNonlinearStability.bondVector
      (ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy.canonicalFlowPosition
        (N := N) kappa beta 0 hbeta (1 / 4) (sample, time)) bond
  exact (ArchonPhysics.R32CanonicalPhysicalFreeBondIdentificationV2.canonicalFreeFlowBond_eq_physicalSignedHaar
    (N := N) hN kappa beta hbeta sample hsimple time bond).symm

/-- The free path used by the exact-minus-free stability bridge has exactly
the same physical bond component as the V3 physical signed Haar field. -/
theorem canonicalExactFreePhysicalPositionPathBond_eq_physicalSignedHaar
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : ArchonPhysics.OrderedSingleModeProjector.SimpleOrderedSpectrum
      (ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian
        (ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final.rawCanonicalFrozenMass
          (N := N) sample.1)))
    (time : Real) (bond : Lattice.Site N) :
    ArchonPhysics.R32DiluteNonlinearStability.bondVector
        (ArchonPhysics.R32CanonicalExactFreeBridgeV3.canonicalPhysicalPositionPath
          (N := N) kappa beta 0 hbeta (1 / 4) sample time) bond =
      ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final.physicalSignedHaarBondField
        (ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final.rawCanonicalFrozenMass
          (N := N) sample.1) bond
        (ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final.orderedPhaseBlockFromSequence
          (N := N) sample.2) time := by
  rw [ArchonPhysics.R32PhysicalSignedCanonicalFreeBondBridge.rawCanonicalFrozenMass_eq_canonicalMass
    sample] at hsimple
  change ArchonPhysics.R32DiluteNonlinearStability.bondVector
      (ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy.canonicalFlowPosition
        (N := N) kappa beta 0 hbeta (1 / 4) (sample, time)) bond = _
  exact (ArchonPhysics.R32CanonicalPhysicalFreeBondIdentificationV2.canonicalFreeFlowBond_eq_physicalSignedHaar
    (N := N) hN kappa beta hbeta sample hsimple time bond)

#print axioms rawCanonicalFrozenMass_eq_canonicalMass
#print axioms sampledCanonicalFreeFlowPosition_eq_canonicalFlowPosition
#print axioms physicalSignedHaarBondField_eq_sampledCanonicalFreeBond
#print axioms canonicalExactFreePhysicalPositionPathBond_eq_physicalSignedHaar

end

end ArchonPhysics.R32PhysicalSignedCanonicalFreeBondBridge
