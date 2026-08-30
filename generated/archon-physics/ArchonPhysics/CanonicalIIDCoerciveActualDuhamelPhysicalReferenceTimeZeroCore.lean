import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPrimitiveSourceIntegrability
import ArchonPhysics.PhyslibInitialModalReference

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPhysicalReferenceTimeZeroCore

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPrimitiveSourceIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibInitialModalReference
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- A useful missing leaf: one measurable canonical signed potential source
is integrable at every fixed time under the existing deterministic envelope. -/
theorem integrable_canonicalSignedPotentialChannelRotatedSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    ((measurable_canonicalSignedPotentialChannelRotatedSource (N := N)
      flowKappa flowBeta flowG hflowBeta a sourceKappa sourceBeta sourceG
        entry).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (canonicalSignedPotentialChannelSourceEnvelope N
      sourceKappa sourceBeta sourceG
      (canonicalWeightedCoordinateEnvelope N
        flowKappa flowBeta flowG hflowBeta))
  filter_upwards [canonicalSignedPotentialChannelSourceBounds_ae_allTime
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hentry] with omega hbound
  exact hbound time

def canonicalPhyslibInitialReferenceRadius
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample) : Lattice.Site N -> Real :=
  physlibInitialReferenceRadius (canonicalMass (N := N) omega)
    (canonicalFlowPosition (N := N)
      flowKappa flowBeta flowG hflowBeta a (omega, 0))
    (canonicalFlowMomentum (N := N)
      flowKappa flowBeta flowG hflowBeta a (omega, 0))

def canonicalPhyslibInitialReferencePhase
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample) :
    UnitAddTorus (Lattice.Site N) :=
  physlibInitialReferencePhase (canonicalMass (N := N) omega)
    (canonicalFlowPosition (N := N)
      flowKappa flowBeta flowG hflowBeta a (omega, 0))
    (canonicalFlowMomentum (N := N)
      flowKappa flowBeta flowG hflowBeta a (omega, 0))

theorem physlibFreeQuadraticRotatedSource_reference_zero_eq_actual_constant
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q0 p0 : HilbertConfiguration N) :
    physlibFreeQuadraticRotatedSource m kappa g observed
        (physlibInitialReferenceRadius m q0 p0)
        (physlibInitialReferencePhase m q0 p0) 0 =
      physlibQuadraticRotatedSource m kappa g observed (fun _ => q0) 0 := by
  unfold physlibFreeQuadraticRotatedSource freeQuadraticPicardIntegrand
    physlibQuadraticCoupling physlibQuadraticRotatedSource
    PhyslibHamiltonDuhamel.physlibModeRotatedSource
    PhyslibHamiltonDuhamel.physlibModeTensorForce tensorNonlinearForce
    forcedModeSource
  rw [freeQuadraticTensorSource_eq_complex_tensorContraction,
    freeWeightedConfiguration_physlibInitialReference_zero]
  simp [physlibInitialModalPosition]
  rw [show massWeightedPosition m (realReparametrize (fun _ => q0)) 0 =
      sqrtMassTransform m q0 by rfl]
  ring

theorem canonicalQuadraticFreeFirstPicardSource_zero_eq_actual
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N) :
    canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalPhyslibInitialReferenceRadius (N := N)
          flowKappa flowBeta flowG hflowBeta a)
        (canonicalPhyslibInitialReferencePhase (N := N)
          flowKappa flowBeta flowG hflowBeta a)
        entry .freeFirstPicard (omega, 0) =
      canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1 entry (omega, 0) := by
  rcases entry with ⟨sign, k⟩
  unfold canonicalQuadraticDuhamelHistorySource
    actualFiniteQuadraticHistorySource
    canonicalPhyslibInitialReferenceRadius
    canonicalPhyslibInitialReferencePhase
    canonicalSignedPotentialChannelRotatedSource
  rw [canonicalOrderedUnitQuadraticRotatedSource_eq_orientation_mul_physlib
    flowKappa flowBeta flowG hflowBeta a omega hsimple k 0]
  have hfree := physlibFreeQuadraticRotatedSource_reference_zero_eq_actual_constant
    (canonicalMass (N := N) omega) 1 1 (orderedPhyslibModeIndex k)
    (canonicalFlowPosition (N := N)
      flowKappa flowBeta flowG hflowBeta a (omega, 0))
    (canonicalFlowMomentum (N := N)
      flowKappa flowBeta flowG hflowBeta a (omega, 0))
  have hpath :
      physlibQuadraticRotatedSource (canonicalMass (N := N) omega) 1 1
          (orderedPhyslibModeIndex k)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega) 0 =
        physlibQuadraticRotatedSource (canonicalMass (N := N) omega) 1 1
          (orderedPhyslibModeIndex k)
          (fun _ => canonicalFlowPosition (N := N)
            flowKappa flowBeta flowG hflowBeta a (omega, 0)) 0 := by
    unfold physlibQuadraticRotatedSource
      PhyslibHamiltonDuhamel.physlibModeRotatedSource
      PhyslibHamiltonDuhamel.physlibModeTensorForce
    rw [realReparametrize_canonicalPhyslibPositionPath]
    rfl
  rw [hfree, ← hpath]
  cases sign <;> simp [phaseSignActComplex]

end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPhysicalReferenceTimeZeroCore
