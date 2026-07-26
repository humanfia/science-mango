import Mathlib
import Physlib.Thermodynamics.IdealGas.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Basic

/-!
# Free expansion of an ideal gas into an equal evacuated compartment

The figure shows an insulated box split into two equal compartments.  Initially,
`n` moles of ideal gas occupy one compartment of volume `V` at temperature `T`,
while the other compartment is evacuated.  Breaking the partition gives the gas
the total volume `2V` without changing its internal energy or temperature.

This file keeps dimensionful quantities tagged with Physlib's `WithDim`.  Mole
counts are real-valued readouts in the chosen mole unit because Physlib's current
`Dimension` type has no amount-of-substance base dimension.

The assumptions are separated by role: `IdealGasEntropyParameters` supplies the
constitutive entropy model, while `FreeExpansionSetup` records the source and
figure readouts together with the first law and the zero-heat/zero-work process
conditions.  There are no previous-part results.  The answer `n R log 2` occurs
only as the conclusion of `entropyChange_eq_nR_log_two`.
-/

namespace PhyXMini0475

open Dimension

noncomputable section

/-- The physical dimension of volume, namely length cubed. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of energy. -/
def energyDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of thermodynamic entropy, energy per temperature. -/
def entropyDimension : Dimension := energyDimension * Θ𝓭⁻¹

/-- A volume readout in one fixed, consistent system of units. -/
abbrev Volume := WithDim volumeDimension ℝ

/-- An internal-energy, heat, or work readout in one fixed system of units. -/
abbrev Energy := WithDim energyDimension ℝ

/-- A thermodynamic-entropy readout in one fixed system of units. -/
abbrev ThermodynamicEntropy := WithDim entropyDimension ℝ

/--
The molar gas constant as an entropy-per-mole quantity.  Since a mole count is
represented by its scalar readout, this carries the entropy dimension.
-/
abbrev MolarGasConstant := WithDim entropyDimension ℝ

/--
The state variables used by Physlib's monophase ideal-gas entropy function.
`amountMoles` is the numerical amount of substance measured in moles.
-/
structure IdealGasState where
  /-- Internal energy of the gas. -/
  internalEnergy : Energy
  /-- Volume occupied by the gas. -/
  occupiedVolume : Volume
  /-- Absolute temperature displayed in the figure. -/
  temperature : Temperature
  /-- Amount-of-substance readout in moles. -/
  amountMoles : ℝ
  internalEnergy_pos : 0 < internalEnergy.val
  occupiedVolume_pos : 0 < occupiedVolume.val
  temperature_pos : 0 < temperature.val
  amountMoles_pos : 0 < amountMoles

/--
Parameters of Physlib's monophase ideal-gas entropy model.  The reference
quantities fix the entropy convention and cancel from the entropy difference.
-/
structure IdealGasEntropyParameters where
  /-- Dimensionless constant multiplying the internal-energy logarithm. -/
  heatCapacityCoefficient : ℝ
  /-- Universal molar gas constant `R` in the chosen unit system. -/
  molarGasConstant : MolarGasConstant
  /-- Reference molar entropy `s₀`. -/
  referenceMolarEntropy : ThermodynamicEntropy
  /-- Positive reference internal energy `U₀`. -/
  referenceInternalEnergy : Energy
  /-- Positive reference volume `V₀`. -/
  referenceVolume : Volume
  /-- Positive reference amount `N₀`, measured in moles. -/
  referenceMoles : ℝ
  heatCapacityCoefficient_nonneg : 0 ≤ heatCapacityCoefficient
  molarGasConstant_pos : 0 < molarGasConstant.val
  referenceInternalEnergy_pos : 0 < referenceInternalEnergy.val
  referenceVolume_pos : 0 < referenceVolume.val
  referenceMoles_pos : 0 < referenceMoles

/--
The entropy of a state, obtained from Physlib's `entropy` function and tagged
with its physical entropy dimension.
-/
def idealGasEntropy
    (parameters : IdealGasEntropyParameters) (state : IdealGasState) :
    ThermodynamicEntropy :=
  ⟨entropy
    parameters.heatCapacityCoefficient
    parameters.molarGasConstant.val
    parameters.referenceMolarEntropy.val
    parameters.referenceInternalEnergy.val
    parameters.referenceVolume.val
    parameters.referenceMoles
    state.internalEnergy.val
    state.occupiedVolume.val
    state.amountMoles⟩

/-- Entropy change between two ideal-gas equilibrium states. -/
def entropyChange
    (parameters : IdealGasEntropyParameters)
    (initialState finalState : IdealGasState) : ThermodynamicEntropy :=
  idealGasEntropy parameters finalState - idealGasEntropy parameters initialState

/--
Physical and figure-derived data for the free expansion.  The first-law field
is a governing law; insulation and expansion into vacuum set heat and work to
zero.  The remaining equalities transcribe the labels `V`, `V`, `2V`, `T`, and
the conserved `n` moles shown or implied by the figure.
-/
structure FreeExpansionSetup where
  initialState : IdealGasState
  finalState : IdealGasState
  /-- Volume `V` of the initially filled compartment. -/
  filledCompartmentVolume : Volume
  /-- Volume `V` of the initially evacuated compartment. -/
  evacuatedCompartmentVolume : Volume
  /-- Figure temperature `T`. -/
  figureTemperature : Temperature
  /-- The problem's amount-of-substance readout `n`, in moles. -/
  nMoles : ℝ
  /-- Initial amount in the evacuated compartment (zero). -/
  initialVacuumMoles : ℝ
  /-- Heat transferred to the gas during the process. -/
  heatTransferred : Energy
  /-- Work done by the gas during the process. -/
  workDoneByGas : Energy
  filledCompartmentVolume_pos : 0 < filledCompartmentVolume.val
  equalCompartmentVolumes : evacuatedCompartmentVolume = filledCompartmentVolume
  initialGasOccupiesOneCompartment :
    initialState.occupiedVolume = filledCompartmentVolume
  finalGasFillsBothCompartments :
    finalState.occupiedVolume =
      filledCompartmentVolume + evacuatedCompartmentVolume
  initialFigureTemperature : initialState.temperature = figureTemperature
  finalFigureTemperature : finalState.temperature = figureTemperature
  initialGasAmount : initialState.amountMoles = nMoles
  finalGasAmount : finalState.amountMoles = nMoles
  evacuatedInitially : initialVacuumMoles = 0
  thermallyInsulated : heatTransferred = 0
  expansionIntoVacuum : workDoneByGas = 0
  /-- First law with the convention `ΔU = Q - W`. -/
  firstLaw :
    finalState.internalEnergy =
      initialState.internalEnergy + heatTransferred - workDoneByGas

/-- An insulated free expansion into vacuum conserves internal energy. -/
lemma internalEnergy_conserved (setup : FreeExpansionSetup) :
    setup.finalState.internalEnergy = setup.initialState.internalEnergy := by
  simpa [setup.thermallyInsulated, setup.expansionIntoVacuum] using setup.firstLaw

/-- Breaking the partition makes the final volume twice the initial volume. -/
lemma finalVolume_eq_two_mul_initialVolume (setup : FreeExpansionSetup) :
    setup.finalState.occupiedVolume.val =
      2 * setup.initialState.occupiedVolume.val := by
  rw [setup.finalGasFillsBothCompartments, setup.equalCompartmentVolumes,
    ← setup.initialGasOccupiesOneCompartment]
  simp only [WithDim.val_add]
  ring

/--
For the equal-compartment free expansion in the figure, the entropy change is
`n R log 2` (answer B).
-/
theorem entropyChange_eq_nR_log_two
    (parameters : IdealGasEntropyParameters) (setup : FreeExpansionSetup) :
    entropyChange parameters setup.initialState setup.finalState =
      ⟨setup.nMoles * parameters.molarGasConstant.val * Real.log 2⟩ := by
  have initialVolume_ne : setup.initialState.occupiedVolume.val ≠ 0 :=
    ne_of_gt setup.initialState.occupiedVolume_pos
  have referenceVolume_ne : parameters.referenceVolume.val ≠ 0 :=
    ne_of_gt parameters.referenceVolume_pos
  have log_finalVolume :
      Real.log
          ((2 * setup.initialState.occupiedVolume.val) /
            parameters.referenceVolume.val) =
        Real.log 2 +
          Real.log
            (setup.initialState.occupiedVolume.val /
              parameters.referenceVolume.val) := by
    calc
      Real.log
          ((2 * setup.initialState.occupiedVolume.val) /
            parameters.referenceVolume.val) =
          Real.log
            (2 *
              (setup.initialState.occupiedVolume.val /
                parameters.referenceVolume.val)) := by
            congr 1
            ring
      _ =
          Real.log 2 +
            Real.log
              (setup.initialState.occupiedVolume.val /
                parameters.referenceVolume.val) :=
        Real.log_mul (by norm_num) (div_ne_zero initialVolume_ne referenceVolume_ne)
  apply WithDim.ext
  simp only [entropyChange, idealGasEntropy, WithDim.val_sub]
  rw [internalEnergy_conserved setup, finalVolume_eq_two_mul_initialVolume setup,
    setup.finalGasAmount, setup.initialGasAmount]
  unfold entropy
  rw [log_finalVolume]
  ring

end

end PhyXMini0475
