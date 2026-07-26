import Mathlib.Data.NNReal.Defs
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0519

open Dimension

/-!
# Photon emitted in a transition of a hypothetical one-electron atom

The supplied diagram has five bound levels, labelled by principal quantum
numbers `n = 1, ..., 5`, and gives wavelengths for the four transitions ending
at the ground level `n = 1`.  The atom also has a measured ground-state
ionization energy of `17.50 eV`.

Lengths and energies below are unit-independent Physlib quantities.  Real
numbers are used only for readouts in named units and for the whole-nanometre
answer displayed by the multiple-choice problem.
-/

/-! ## Unit-independent quantities and named-unit readouts -/

/-- A unit-independent, nonnegative physical quantity with length dimension. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length as a real number of nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.nanometers}).val : ℝ)

/--
Read a physical energy as a real number of electron volts.  The quotient is
dimensionless: both numerator and denominator are first represented in SI,
and the denominator is Physlib's unit-independent one-electron-volt energy.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.electronVolt UnitChoices.SI).val

/--
The standard product `h c`, read in electron-volt nanometres.  Physlib supplies
the reduced Planck constant in joule-seconds and the speed of light in metres
per second; `2π` converts `ℏ` to `h`, and `10^9` converts metres to nanometres.
-/
def planckTimesLightInElectronVoltNanometers : ℝ :=
  (2 * Real.pi * (Constants.ℏ : ℝ)) *
      (DimSpeed.speedOfLight UnitChoices.SI).val * (10 : ℝ) ^ 9 /
    (DimEnergy.electronVolt UnitChoices.SI).val

/-! ## Atomic levels, transition observables, and figure vocabulary -/

/-- The five principal-quantum-number labels printed on the supplied diagram. -/
inductive AtomicLevel where
  | n1
  | n2
  | n3
  | n4
  | n5
  deriving DecidableEq, Fintype, Repr

namespace AtomicLevel

/-- The principal quantum number represented by an atomic-level label. -/
def principalQuantumNumber : AtomicLevel → ℕ
  | .n1 => 1
  | .n2 => 2
  | .n3 => 3
  | .n4 => 4
  | .n5 => 5

end AtomicLevel

/--
The physically meaningful content read from an atomic energy-level diagram.
The optional wavelength label is itself a physical length, rather than an
untyped scalar attached to an arrow.
-/
structure AtomicEnergyLevelDiagram where
  levelLineShown : AtomicLevel → Bool
  downwardArrowShown : AtomicLevel → AtomicLevel → Bool
  wavelengthLabel : AtomicLevel → AtomicLevel → Option LengthQuantity

/--
Independent quantities of the hypothetical atom and its emission experiment.
The `n = 4` to `n = 2` wavelength is an observable field; it is not defined to
be the recorded answer.  The laws below constrain all downward transitions.
-/
structure OneElectronAtomExperiment where
  boundElectronCount : ℕ
  levelEnergy : AtomicLevel → DimEnergy
  continuumThreshold : DimEnergy
  groundStateIonizationEnergy : DimEnergy
  emittedPhotonWavelength : AtomicLevel → AtomicLevel → LengthQuantity
  diagram : AtomicEnergyLevelDiagram

/-! ## Scenario, source measurements, and governing laws -/

/-- The qualitative one-electron, ground-state, and bound-level scenario. -/
structure MatchesOneElectronAtomScenario
    (experiment : OneElectronAtomExperiment) : Prop where
  oneBoundElectron : experiment.boundElectronCount = 1
  n1IsGroundState : ∀ level : AtomicLevel,
    energyInElectronVolts (experiment.levelEnergy .n1) ≤
      energyInElectronVolts (experiment.levelEnergy level)
  fiveShownLevelsAreBound : ∀ level : AtomicLevel,
    energyInElectronVolts (experiment.levelEnergy level) <
      energyInElectronVolts experiment.continuumThreshold

/--
Primary-image readout.  It records all five horizontal level lines, the four
downward arrows ending at `n = 1`, and their wavelength labels.  In particular,
the requested `n = 4` to `n = 2` arrow and wavelength are not shown in the
figure and therefore do not occur here as measured answer data.
-/
structure MatchesSuppliedEnergyLevelDiagram
    (experiment : OneElectronAtomExperiment) : Prop where
  allFiveLevelLinesShown : ∀ level : AtomicLevel,
    experiment.diagram.levelLineShown level = true
  n5ToN1Arrow : experiment.diagram.downwardArrowShown .n5 .n1 = true
  n4ToN1Arrow : experiment.diagram.downwardArrowShown .n4 .n1 = true
  n3ToN1Arrow : experiment.diagram.downwardArrowShown .n3 .n1 = true
  n2ToN1Arrow : experiment.diagram.downwardArrowShown .n2 .n1 = true
  noN4ToN2Arrow : experiment.diagram.downwardArrowShown .n4 .n2 = false
  n5ToN1Label : experiment.diagram.wavelengthLabel .n5 .n1 =
    some (experiment.emittedPhotonWavelength .n5 .n1)
  n4ToN1Label : experiment.diagram.wavelengthLabel .n4 .n1 =
    some (experiment.emittedPhotonWavelength .n4 .n1)
  n3ToN1Label : experiment.diagram.wavelengthLabel .n3 .n1 =
    some (experiment.emittedPhotonWavelength .n3 .n1)
  n2ToN1Label : experiment.diagram.wavelengthLabel .n2 .n1 =
    some (experiment.emittedPhotonWavelength .n2 .n1)
  noN4ToN2Label : experiment.diagram.wavelengthLabel .n4 .n2 = none
  n5ToN1Nanometers :
    lengthInNanometers (experiment.emittedPhotonWavelength .n5 .n1) = 73.86
  n4ToN1Nanometers :
    lengthInNanometers (experiment.emittedPhotonWavelength .n4 .n1) = 75.63
  n3ToN1Nanometers :
    lengthInNanometers (experiment.emittedPhotonWavelength .n3 .n1) = 79.76
  n2ToN1Nanometers :
    lengthInNanometers (experiment.emittedPhotonWavelength .n2 .n1) = 94.54

/-- The independently observed `17.50 eV` ground-state ionization energy. -/
structure MatchesIonizationEnergyMeasurement
    (experiment : OneElectronAtomExperiment) : Prop where
  ionizationEnergyElectronVolts :
    energyInElectronVolts experiment.groundStateIonizationEnergy = 17.50

/-- Strict ordering and positivity conditions for the physical spectrum. -/
structure HasPhysicalAtomicSpectrum
    (experiment : OneElectronAtomExperiment) : Prop where
  n1BelowN2 :
    energyInElectronVolts (experiment.levelEnergy .n1) <
      energyInElectronVolts (experiment.levelEnergy .n2)
  n2BelowN3 :
    energyInElectronVolts (experiment.levelEnergy .n2) <
      energyInElectronVolts (experiment.levelEnergy .n3)
  n3BelowN4 :
    energyInElectronVolts (experiment.levelEnergy .n3) <
      energyInElectronVolts (experiment.levelEnergy .n4)
  n4BelowN5 :
    energyInElectronVolts (experiment.levelEnergy .n4) <
      energyInElectronVolts (experiment.levelEnergy .n5)
  n5BelowContinuum :
    energyInElectronVolts (experiment.levelEnergy .n5) <
      energyInElectronVolts experiment.continuumThreshold
  positiveIonizationEnergy :
    0 < energyInElectronVolts experiment.groundStateIonizationEnergy
  positiveDownwardWavelength : ∀ upper lower : AtomicLevel,
    lower.principalQuantumNumber < upper.principalQuantumNumber →
      0 < lengthInNanometers
        (experiment.emittedPhotonWavelength upper lower)

/--
The two governing relations used by the calculation:

* ionization energy is the gap from the `n = 1` level to the continuum;
* every downward emitted photon obeys `ΔE λ = h c`, here expressed in
  electron volts and nanometres.

The transition law is uniform in the two levels and contains no special value
for the requested `n = 4` to `n = 2` wavelength.
-/
structure SatisfiesAtomicPhotonLaws
    (experiment : OneElectronAtomExperiment) : Prop where
  groundStateIonizationGap :
    energyInElectronVolts experiment.groundStateIonizationEnergy =
      energyInElectronVolts experiment.continuumThreshold -
        energyInElectronVolts (experiment.levelEnergy .n1)
  photonEnergyWavelengthLaw : ∀ upper lower : AtomicLevel,
    lower.principalQuantumNumber < upper.principalQuantumNumber →
      (energyInElectronVolts (experiment.levelEnergy upper) -
          energyInElectronVolts (experiment.levelEnergy lower)) *
          lengthInNanometers
            (experiment.emittedPhotonWavelength upper lower) =
        planckTimesLightInElectronVoltNanometers

/-! ## Current target -/

/--
A physical wavelength rounds to the displayed whole number of nanometres when
its nanometre readout lies in the corresponding half-open unit interval.
-/
def RoundsToNearestWholeNanometer
    (wavelength : LengthQuantity) (displayedNanometers : ℕ) : Prop :=
  (displayedNanometers : ℝ) - 1 / 2 ≤ lengthInNanometers wavelength ∧
    lengthInNanometers wavelength < (displayedNanometers : ℝ) + 1 / 2

/--
The photon emitted in the `n = 4` to `n = 2` transition has wavelength
approximately `378 nm`, i.e. answer choice D at the displayed precision.

Blueprint label: `thm:physics:phyx_mini_0519:target`.
-/
theorem emittedPhotonWavelengthN4ToN2_roundsTo378Nanometers
    (experiment : OneElectronAtomExperiment)
    (scenario : MatchesOneElectronAtomScenario experiment)
    (figureData : MatchesSuppliedEnergyLevelDiagram experiment)
    (ionizationData : MatchesIonizationEnergyMeasurement experiment)
    (physicalSpectrum : HasPhysicalAtomicSpectrum experiment)
    (laws : SatisfiesAtomicPhotonLaws experiment) :
    RoundsToNearestWholeNanometer
      (experiment.emittedPhotonWavelength .n4 .n2) 378 := by
  have h₄₁ := laws.photonEnergyWavelengthLaw .n4 .n1 (by decide)
  have h₂₁ := laws.photonEnergyWavelengthLaw .n2 .n1 (by decide)
  have h₄₂ := laws.photonEnergyWavelengthLaw .n4 .n2 (by decide)
  rw [figureData.n4ToN1Nanometers] at h₄₁
  rw [figureData.n2ToN1Nanometers] at h₂₁
  have hgap :
      0 <
        energyInElectronVolts (experiment.levelEnergy .n4) -
          energyInElectronVolts (experiment.levelEnergy .n2) := by
    exact sub_pos.mpr (physicalSpectrum.n2BelowN3.trans physicalSpectrum.n3BelowN4)
  have hscaled :
      35750301 *
          (energyInElectronVolts (experiment.levelEnergy .n4) -
            energyInElectronVolts (experiment.levelEnergy .n2)) =
        94550 * planckTimesLightInElectronVoltNanometers := by
    norm_num at h₄₁ h₂₁
    nlinarith
  have hproduct :
      (energyInElectronVolts (experiment.levelEnergy .n4) -
          energyInElectronVolts (experiment.levelEnergy .n2)) *
        (lengthInNanometers (experiment.emittedPhotonWavelength .n4 .n2) -
          (35750301 / 94550 : ℝ)) = 0 := by
    nlinarith [h₄₂, hscaled]
  have hwavelength :
      lengthInNanometers (experiment.emittedPhotonWavelength .n4 .n2) =
        (35750301 / 94550 : ℝ) := by
    rcases mul_eq_zero.mp hproduct with hzero | hzero
    · exact (hgap.ne' hzero).elim
    · linarith
  unfold RoundsToNearestWholeNanometer
  rw [hwavelength]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0519
