import ArchonPhysics.PhaseRenormalization
import ArchonPhysics.PhyslibFPUTModalObservableFlowLipschitz

/-!
# Lipschitz interaction-picture modal amplitudes along the FPUT flow

The exact endpoint used by the FPUT second-Picard comparison is not the raw
complex mode amplitude but its fixed-time interaction-picture rotation.
Multiplication by `exp (I * omega * t)` is an isometry of `Complex`, so this
additional physical coordinate change leaves the full-state Lipschitz
constant unchanged.
-/

namespace ArchonPhysics.PhyslibFPUTInteractionPictureModalFlowLipschitz

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTModalObservableFlowLipschitz
open ArchonPhysics.ReducedModeTransform

noncomputable section

variable {N : Nat} [NeZero N]

/-- A fixed phase rotation is an isometry of the complex amplitude plane. -/
theorem phaseRenormalize_isometry (theta : Real) :
    Isometry (phaseRenormalize theta) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_eq_norm, dist_eq_norm]
  unfold phaseRenormalize
  rw [← mul_sub, norm_mul, norm_phaseFactor, one_mul]

/-- A fixed phase rotation is therefore `1`-Lipschitz. -/
theorem phaseRenormalize_lipschitzWith_one (theta : Real) :
    LipschitzWith 1 (phaseRenormalize theta) :=
  (phaseRenormalize_isometry theta).lipschitz

/-- Exact selected interaction-picture amplitude after one canonical
Hamiltonian block. -/
def canonicalFixedMassInteractionPictureAmplitudeAfter
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) : ParametricPhaseSpace N → Complex :=
  fun x ↦ phaseRenormalize (modeFrequency m observed * t)
    (canonicalFixedMassSelectedModeAmplitudeAfter shell m observed t x)

/-- The interaction-picture observable has the exact physical formula:
evolve by the canonical Hamiltonian flow, read the mass-weighted selected
mode, and rotate it by `exp (I * omega * t)`. -/
@[simp] theorem canonicalFixedMassInteractionPictureAmplitudeAfter_apply
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) (x : ParametricPhaseSpace N) :
    canonicalFixedMassInteractionPictureAmplitudeAfter
        shell m observed t x =
      phaseRenormalize (modeFrequency m observed * t)
        (complexModeAmplitude (modeFrequency m observed)
          (modalCoordinates m
            (sqrtMassTransform m
              (canonicalRandomMassGlobalFlow shell (x, t)).2.1) observed)
          (modalCoordinates m
            (inverseSqrtMassTransform m
              (canonicalRandomMassGlobalFlow shell (x, t)).2.2) observed)) := by
  rw [canonicalFixedMassInteractionPictureAmplitudeAfter,
    canonicalFixedMassSelectedModeAmplitudeAfter_apply]

/-- Phase renormalization does not alter the endpoint squared amplitude. -/
@[simp] theorem normSq_canonicalFixedMassInteractionPictureAmplitudeAfter
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) (x : ParametricPhaseSpace N) :
    Complex.normSq
        (canonicalFixedMassInteractionPictureAmplitudeAfter
          shell m observed t x) =
      Complex.normSq
        (canonicalFixedMassSelectedModeAmplitudeAfter
          shell m observed t x) := by
  simp [canonicalFixedMassInteractionPictureAmplitudeAfter]

/-- This is the `actualBlock_lipschitz` witness for a physical full-state
endpoint certificate in interaction-picture coordinates.  Its constant is
identical to the raw-amplitude constant because the final phase has unit
norm. -/
theorem canonicalFixedMassInteractionPictureAmplitudeAfter_lipschitz
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) :
    LipschitzWith
      (canonicalFixedMassSelectedModeAmplitudeAfterAmplification
        shell m observed t)
      (canonicalFixedMassInteractionPictureAmplitudeAfter
        shell m observed t) := by
  change LipschitzWith
    (canonicalFixedMassSelectedModeAmplitudeAfterAmplification
      shell m observed t)
    (phaseRenormalize (modeFrequency m observed * t) ∘
      canonicalFixedMassSelectedModeAmplitudeAfter shell m observed t)
  simpa only [one_mul] using
    (phaseRenormalize_lipschitzWith_one
      (modeFrequency m observed * t)).comp
      (canonicalFixedMassSelectedModeAmplitudeAfter_lipschitz
        shell m observed t)

end

end ArchonPhysics.PhyslibFPUTInteractionPictureModalFlowLipschitz
