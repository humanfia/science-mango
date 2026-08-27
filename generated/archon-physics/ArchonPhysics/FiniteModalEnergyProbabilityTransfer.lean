import ArchonPhysics.FiniteModalEnergyL1Stability
import ArchonPhysics.MicroscopicErrorProbabilityUpgrade

/-!
# Probability transfer from modal-state RMS error to modal-energy error

This module connects the deterministic finite-mode `L2`-to-`L1` stability
estimate to the convergence-in-probability interface used by F3.  The mode
count may vary with the family index.  On a supplied high-probability event,
uniform RMS amplitude bounds and an `O(g)` RMS state error imply an `O(g)`
mean modal-energy error.  With a positive extensive reference-energy floor,
the same data imply an `O(g)` normalized-spectrum error.

The state comparison estimate and the good-event probability remain explicit
inputs.  In particular, this module does not prove closeness of the exact LJ
flow to a retained FPUT or kinetic trajectory.
-/

namespace ArchonPhysics.FiniteModalEnergyProbabilityTransfer

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.FiniteModalEnergyL1Stability
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.MicroscopicErrorProbabilityUpgrade
open ArchonPhysics.ThermalizationTransfer

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]

/-- RMS distance of two varying finite-mode amplitude families.  The successor
index guarantees a nonempty mode space without an additional family of type
class assumptions. -/
def indexedAmplitudeRMSDistance
    (size : Nat → Nat)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (j : Nat) (omega : Omega) : Real :=
  amplitudeRMSDistance (a j omega) (b j omega)

/-- Mean absolute modal-energy error for a varying finite-mode family. -/
def indexedPerModeEnergyError
    (size : Nat → Nat)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (j : Nat) (omega : Omega) : Real :=
  perModeModalEnergyL1Distance (a j omega) (b j omega)

/-- Normalized modal-energy-profile error for a varying finite-mode family. -/
def indexedNormalizedEnergyError
    (size : Nat → Nat)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (j : Nat) (omega : Omega) : Real :=
  normalizedModalEnergyL1Distance (a j omega) (b j omega)

/-- Transparent stochastic data for transferring an RMS state comparison to
a mean modal-energy comparison. -/
structure ModalStateGoodEventCertificate
    (probability : Measure Omega)
    (size : Nat → Nat) (coupling : Nat → Real)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient : Real) where
  goodEvent : Nat → Set Omega
  goodEvent_measurable : ∀ j, MeasurableSet (goodEvent j)
  coupling_nonneg : ∀ j, 0 ≤ coupling j
  amplitudeCeilingA_nonneg : 0 ≤ amplitudeCeilingA
  amplitudeCeilingB_nonneg : 0 ≤ amplitudeCeilingB
  errorCoefficient_nonneg : 0 ≤ errorCoefficient
  amplitudeA_le_on_good : ∀ j omega, omega ∈ goodEvent j →
    amplitudeRMSNorm (a j omega) ≤ amplitudeCeilingA
  amplitudeB_le_on_good : ∀ j omega, omega ∈ goodEvent j →
    amplitudeRMSNorm (b j omega) ≤ amplitudeCeilingB
  stateError_le_on_good : ∀ j omega, omega ∈ goodEvent j →
    indexedAmplitudeRMSDistance size a b j omega ≤
      errorCoefficient * coupling j
  perModeEnergyError_measurable : ∀ j,
    Measurable (indexedPerModeEnergyError size a b j)
  good_compl_probability_zero :
    Tendsto (fun j ↦ probability (goodEvent j)ᶜ) atTop (nhds 0)

/-- The deterministic energy-error budget supplied by a state certificate on
its good event. -/
theorem ModalStateGoodEventCertificate.perModeEnergyError_le_on_good
    (probability : Measure Omega)
    (size : Nat → Nat) (coupling : Nat → Real)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient : Real)
    (certificate : ModalStateGoodEventCertificate probability size coupling
      a b amplitudeCeilingA amplitudeCeilingB errorCoefficient)
    (j : Nat) (omega : Omega) (homega : omega ∈ certificate.goodEvent j) :
    indexedPerModeEnergyError size a b j omega ≤
      (amplitudeCeilingA + amplitudeCeilingB) *
        errorCoefficient * coupling j := by
  exact perModeModalEnergyL1Distance_le_of_rms_error
    (a j omega) (b j omega)
      amplitudeCeilingA amplitudeCeilingB errorCoefficient (coupling j)
      certificate.amplitudeCeilingA_nonneg
      certificate.amplitudeCeilingB_nonneg
      certificate.errorCoefficient_nonneg (certificate.coupling_nonneg j)
      (certificate.amplitudeA_le_on_good j omega homega)
      (certificate.amplitudeB_le_on_good j omega homega)
      (certificate.stateError_le_on_good j omega homega)

/-- Vanishing coupling and bad-event probability promote the mean modal-energy
error to the exact bundled project convergence-in-probability interface. -/
theorem ModalStateGoodEventCertificate.perModeEnergy_convergesInProbability
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (size : Nat → Nat) (coupling : Nat → Real)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient : Real)
    (certificate : ModalStateGoodEventCertificate probability size coupling
      a b amplitudeCeilingA amplitudeCeilingB errorCoefficient)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    ConvergesInProbabilityTo probability
      (fun j omega ↦ ENNReal.ofReal
        (indexedPerModeEnergyError size a b j omega)) 0 := by
  let coefficient :=
    (amplitudeCeilingA + amplitudeCeilingB) * errorCoefficient
  apply convergesInProbabilityTo_zero_of_goodEvent_budget
    probability
      (fun j omega ↦ ENNReal.ofReal
        (indexedPerModeEnergyError size a b j omega))
      (fun j ↦ ENNReal.measurable_ofReal.comp
        (certificate.perModeEnergyError_measurable j))
      certificate.goodEvent
      (fun j ↦ ENNReal.ofReal (coefficient * coupling j))
      (fun j ↦ probability (certificate.goodEvent j)ᶜ)
  · intro j omega homega
    apply ENNReal.ofReal_le_ofReal
    simpa only [coefficient, mul_assoc] using
      certificate.perModeEnergyError_le_on_good probability size coupling
        a b amplitudeCeilingA amplitudeCeilingB errorCoefficient
        j omega homega
  · have hscale : Tendsto (fun j ↦ coefficient * coupling j)
        atTop (nhds (coefficient * 0)) :=
      tendsto_const_nhds.mul hcoupling
    simpa using ENNReal.tendsto_ofReal hscale
  · intro j
    exact le_rfl
  · exact certificate.good_compl_probability_zero

/-- Additional positive-energy data needed to normalize the modal spectrum. -/
structure NormalizedEnergyGoodEventData
    (size : Nat → Nat)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (goodEvent : Nat → Set Omega)
    (energyDensityFloor : Real) where
  energyDensityFloor_pos : 0 < energyDensityFloor
  referenceEnergyFloor_on_good : ∀ j omega, omega ∈ goodEvent j →
    ((Fintype.card (Fin (size j + 1)) : Nat) : Real) *
        energyDensityFloor ≤
      totalWeight (modalEnergySpectrum (a j omega))
  comparisonEnergy_pos_on_good : ∀ j omega, omega ∈ goodEvent j →
    0 < totalWeight (modalEnergySpectrum (b j omega))
  normalizedEnergyError_measurable : ∀ j,
    Measurable (indexedNormalizedEnergyError size a b j)

/-- On the same good event, an extensive reference-energy floor upgrades the
mean energy estimate to a normalized-spectrum estimate. -/
theorem normalizedEnergyError_le_on_good
    (probability : Measure Omega)
    (size : Nat → Nat) (coupling : Nat → Real)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient
      energyDensityFloor : Real)
    (certificate : ModalStateGoodEventCertificate probability size coupling
      a b amplitudeCeilingA amplitudeCeilingB errorCoefficient)
    (energyData : NormalizedEnergyGoodEventData size a b
      certificate.goodEvent energyDensityFloor)
    (j : Nat) (omega : Omega) (homega : omega ∈ certificate.goodEvent j) :
    indexedNormalizedEnergyError size a b j omega ≤
      (2 / energyDensityFloor) *
        ((amplitudeCeilingA + amplitudeCeilingB) *
          errorCoefficient * coupling j) := by
  exact normalizedModalEnergyL1Distance_le_of_rms_error
    (a j omega) (b j omega) energyDensityFloor
      amplitudeCeilingA amplitudeCeilingB errorCoefficient (coupling j)
      energyData.energyDensityFloor_pos
      certificate.amplitudeCeilingA_nonneg
      certificate.amplitudeCeilingB_nonneg
      certificate.errorCoefficient_nonneg (certificate.coupling_nonneg j)
      (energyData.referenceEnergyFloor_on_good j omega homega)
      (energyData.comparisonEnergy_pos_on_good j omega homega)
      (certificate.amplitudeA_le_on_good j omega homega)
      (certificate.amplitudeB_le_on_good j omega homega)
      (certificate.stateError_le_on_good j omega homega)

/-- Bundled convergence in probability of the normalized energy spectrum. -/
theorem normalizedEnergy_convergesInProbability
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (size : Nat → Nat) (coupling : Nat → Real)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient
      energyDensityFloor : Real)
    (certificate : ModalStateGoodEventCertificate probability size coupling
      a b amplitudeCeilingA amplitudeCeilingB errorCoefficient)
    (energyData : NormalizedEnergyGoodEventData size a b
      certificate.goodEvent energyDensityFloor)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    ConvergesInProbabilityTo probability
      (fun j omega ↦ ENNReal.ofReal
        (indexedNormalizedEnergyError size a b j omega)) 0 := by
  let coefficient := (2 / energyDensityFloor) *
    ((amplitudeCeilingA + amplitudeCeilingB) * errorCoefficient)
  apply convergesInProbabilityTo_zero_of_goodEvent_budget
    probability
      (fun j omega ↦ ENNReal.ofReal
        (indexedNormalizedEnergyError size a b j omega))
      (fun j ↦ ENNReal.measurable_ofReal.comp
        (energyData.normalizedEnergyError_measurable j))
      certificate.goodEvent
      (fun j ↦ ENNReal.ofReal (coefficient * coupling j))
      (fun j ↦ probability (certificate.goodEvent j)ᶜ)
  · intro j omega homega
    apply ENNReal.ofReal_le_ofReal
    have hbound := normalizedEnergyError_le_on_good
      probability size coupling a b amplitudeCeilingA amplitudeCeilingB
        errorCoefficient energyDensityFloor certificate energyData
        j omega homega
    simpa only [coefficient, mul_assoc] using hbound
  · have hscale : Tendsto (fun j ↦ coefficient * coupling j)
        atTop (nhds (coefficient * 0)) :=
      tendsto_const_nhds.mul hcoupling
    simpa using ENNReal.tendsto_ofReal hscale
  · intro j
    exact le_rfl
  · exact certificate.good_compl_probability_zero

end

end ArchonPhysics.FiniteModalEnergyProbabilityTransfer
