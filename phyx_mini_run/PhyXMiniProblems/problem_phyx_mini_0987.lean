import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0987

open Dimension

/-!
# Maximum capacitor charge after switching an ideal `L-C` circuit

The primary raster shows a battery `ℰ`, ammeter `A`, switch `S₁`, resistor
`R`, a `2.0 mH` inductor, switch `S₂`, and a `5.0 μF` capacitor.  While
`S₁` is closed and `S₂` is open, the battery and resistor establish a steady
inductor current of `3.50 A`.  The simultaneous opening of `S₁` and closing
of `S₂` disconnects the source and closes an ideal inductor-capacitor loop.

Physical quantities are represented by unit-independent Physlib
`Dimensionful` values.  Real numbers occur only at coherent-SI readout
boundaries and in literal figure or answer-choice data.

Assumption/target split:

* governing laws: the long-time source circuit obeys its steady Ohm relation,
  inductor current is continuous at the switching instant, and the isolated
  ideal `L-C` loop conserves magnetic plus electric energy and reaches a
  zero-current transfer state;
* previous-part results: none;
* figure/data readouts: the complete component topology and labels,
  `L = 2.0 mH`, `C = 5.0 μF`, the `3.50 A` ammeter reading, source polarity,
  and the simultaneous `S₁`/`S₂` switching protocol;
* current target conclusions: a maximum capacitor-charge magnitude of
  `0.350 mC` and agreement with answer choice B.

Neither the requested charge value nor its answer label is a setup field or
a premise of the governing-law structures.
-/

/-! ## Dimensions, dimensionful quantities, and named SI readouts -/

/-- Energy has physical dimension `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric current is charge per unit time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electric potential difference is energy per unit charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Electrical resistance is potential difference divided by current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Inductance is energy divided by current squared. -/
def inductanceDimension : Dimension :=
  energyDimension * electricCurrentDimension⁻¹ * electricCurrentDimension⁻¹

/-- Capacitance is charge divided by potential difference. -/
def capacitanceDimension : Dimension :=
  C𝓭 * electricPotentialDimension⁻¹

/-- A nonnegative, unit-independent voltage magnitude. -/
abbrev VoltageMagnitude : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev CurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent inductance. -/
abbrev InductanceMagnitude : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A nonnegative, unit-independent capacitance. -/
abbrev CapacitanceMagnitude : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitude : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeMagnitude : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a voltage magnitude in volts. -/
def voltageInVolts (voltage : VoltageMagnitude) : ℝ :=
  nonnegativeSIReadout voltage

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : CurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read an inductance in henries. -/
def inductanceInHenries (inductance : InductanceMagnitude) : ℝ :=
  nonnegativeSIReadout inductance

/-- Read an inductance in millihenries. -/
def inductanceInMillihenries (inductance : InductanceMagnitude) : ℝ :=
  1000 * inductanceInHenries inductance

/-- Read a capacitance in farads. -/
def capacitanceInFarads (capacitance : CapacitanceMagnitude) : ℝ :=
  nonnegativeSIReadout capacitance

/-- Read a capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceMagnitude) : ℝ :=
  (10 : ℝ) ^ 6 * capacitanceInFarads capacitance

/-- Read a charge magnitude in coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitude) : ℝ :=
  nonnegativeSIReadout charge

/-- Read a charge magnitude in millicoulombs. -/
def chargeInMillicoulombs (charge : ChargeMagnitude) : ℝ :=
  1000 * chargeInCoulombs charge

/-! ## Primary-figure labels and circuit topology -/

/-- The two ideal switches labelled in the raster. -/
inductive SwitchLabel where
  | S1
  | S2
  deriving DecidableEq, Fintype, Repr

/-- Open and closed states of an ideal switch. -/
inductive SwitchState where
  | openCircuit
  | closedCircuit
  deriving DecidableEq, Repr

/-- Every electrical component explicitly visible in image `987.png`. -/
inductive CircuitComponent where
  | battery
  | ammeter
  | switchS1
  | inductor
  | switchS2
  | capacitor
  | resistor
  deriving DecidableEq, Fintype, Repr

/-- Named junctions sufficient to preserve the topology in the supplied raster. -/
inductive CircuitNode where
  | sourceUpper
  | afterAmmeter
  | inductorUpper
  | capacitorUpper
  | commonReturn
  | sourceLower
  deriving DecidableEq, Fintype, Repr

/-- The two operating configurations described in the problem. -/
inductive CircuitConfiguration where
  | sourceResistorInductorSeries
  | isolatedInductorCapacitorLoop
  deriving DecidableEq, Repr

/-- Endpoints of each component in the primary circuit drawing. -/
def expectedEndpoints : CircuitComponent → CircuitNode × CircuitNode
  | .battery => (.sourceLower, .sourceUpper)
  | .ammeter => (.sourceUpper, .afterAmmeter)
  | .switchS1 => (.afterAmmeter, .inductorUpper)
  | .inductor => (.inductorUpper, .commonReturn)
  | .switchS2 => (.inductorUpper, .capacitorUpper)
  | .capacitor => (.capacitorUpper, .commonReturn)
  | .resistor => (.commonReturn, .sourceLower)

/-- Literal text printed beside each component in the primary raster. -/
def expectedComponentLabel : CircuitComponent → String
  | .battery => "ℰ"
  | .ammeter => "A"
  | .switchS1 => "S₁"
  | .inductor => "2.0 mH"
  | .switchS2 => "S₂"
  | .capacitor => "5.0 μF"
  | .resistor => "R"

/-- Presentation and scalar-label data transcribed from image `987.png`. -/
structure SwitchedLCFigure where
  componentShown : CircuitComponent → Bool
  endpoints : CircuitComponent → CircuitNode × CircuitNode
  printedLabel : CircuitComponent → String
  switchDrawnOpen : SwitchLabel → Bool
  positiveSourceTerminalShownAtUpper : Bool
  printedInductanceInMillihenries : ℝ
  printedCapacitanceInMicrofarads : ℝ

/-! ## Independent circuit setup and supplied scenario -/

/-!
The physical quantities are independent fields.  In particular, the charge
history is not defined from an answer number, and no maximum-charge value is
stored in the setup.
-/
structure SwitchedLCCircuit where
  unitSystem : UnitChoices
  sourceEmf : VoltageMagnitude
  seriesResistance : ResistanceMagnitude
  inductance : InductanceMagnitude
  capacitance : CapacitanceMagnitude
  steadyCurrentBeforeSwitch : CurrentMagnitude
  switchingInstant : TimeMagnitude
  currentDuringLC : TimeMagnitude → CurrentMagnitude
  capacitorChargeDuringLC : TimeMagnitude → ChargeMagnitude
  switchStateBefore : SwitchLabel → SwitchState
  switchStateAfter : SwitchLabel → SwitchState
  configurationBefore : CircuitConfiguration
  configurationAfter : CircuitConfiguration
  switchesChangeSimultaneously : Bool
  ammeterReadingInAmperes : ℝ
  figure : SwitchedLCFigure

/-- Literal topology, labels, polarity, and numerical labels in the raster. -/
structure MatchesPrimaryFigureAndReadouts
    (setup : SwitchedLCCircuit) : Prop where
  usesSIReferenceSystem : setup.unitSystem = UnitChoices.SI
  everyComponentShown : ∀ component,
    setup.figure.componentShown component = true
  componentTopology : ∀ component,
    setup.figure.endpoints component = expectedEndpoints component
  componentLabels : ∀ component,
    setup.figure.printedLabel component = expectedComponentLabel component
  bothSwitchesDrawnOpen : ∀ switch,
    setup.figure.switchDrawnOpen switch = true
  positiveSourceTerminalShown :
    setup.figure.positiveSourceTerminalShownAtUpper = true
  printedInductorLabel :
    setup.figure.printedInductanceInMillihenries = 2
  physicalInductanceMatchesFigure :
    inductanceInMillihenries setup.inductance =
      setup.figure.printedInductanceInMillihenries
  printedCapacitorLabel :
    setup.figure.printedCapacitanceInMicrofarads = 5
  physicalCapacitanceMatchesFigure :
    capacitanceInMicrofarads setup.capacitance =
      setup.figure.printedCapacitanceInMicrofarads
  ammeterReadsThreePointFiveAmperes :
    setup.ammeterReadingInAmperes = 7 / 2
  ammeterMeasuresSteadyInductorCurrent :
    currentInAmperes setup.steadyCurrentBeforeSwitch =
      setup.ammeterReadingInAmperes

/-- Switch states before and after the simultaneous reconfiguration. -/
structure MatchesSimultaneousSwitchingProtocol
    (setup : SwitchedLCCircuit) : Prop where
  s1ClosedBefore : setup.switchStateBefore .S1 = .closedCircuit
  s2OpenBefore : setup.switchStateBefore .S2 = .openCircuit
  sourceCircuitBefore :
    setup.configurationBefore = .sourceResistorInductorSeries
  s1OpenAfter : setup.switchStateAfter .S1 = .openCircuit
  s2ClosedAfter : setup.switchStateAfter .S2 = .closedCircuit
  isolatedLCLoopAfter :
    setup.configurationAfter = .isolatedInductorCapacitorLoop
  switchingIsSimultaneous : setup.switchesChangeSimultaneously = true

/-- Positivity conditions selecting the nondegenerate physical circuit. -/
structure HasPositiveCircuitParameters
    (setup : SwitchedLCCircuit) : Prop where
  sourceEmfPositive : 0 < voltageInVolts setup.sourceEmf
  resistancePositive : 0 < resistanceInOhms setup.seriesResistance
  inductancePositive : 0 < inductanceInHenries setup.inductance
  capacitancePositive : 0 < capacitanceInFarads setup.capacitance
  initialCurrentPositive :
    0 < currentInAmperes setup.steadyCurrentBeforeSwitch

/-! ## Governing laws for the steady source circuit and ideal `L-C` exchange -/

/-- Magnetic energy of the inductor, expressed in coherent-SI joules. -/
def inductorEnergyInJoules
    (setup : SwitchedLCCircuit) (current : CurrentMagnitude) : ℝ :=
  (1 / 2 : ℝ) * inductanceInHenries setup.inductance *
    currentInAmperes current ^ 2

/-- Electric energy of the capacitor, expressed in coherent-SI joules. -/
def capacitorEnergyInJoules
    (setup : SwitchedLCCircuit) (charge : ChargeMagnitude) : ℝ :=
  (1 / 2 : ℝ) * chargeInCoulombs charge ^ 2 /
    capacitanceInFarads setup.capacitance

/-- Total magnetic plus electric energy at a time in the isolated loop. -/
def totalLCEnergyInJoules
    (setup : SwitchedLCCircuit) (time : TimeMagnitude) : ℝ :=
  inductorEnergyInJoules setup (setup.currentDuringLC time) +
    capacitorEnergyInJoules setup (setup.capacitorChargeDuringLC time)

/-!
The local abstraction below records the standard ideal-circuit laws needed by
the solution.  The zero-current transfer state is qualitative LC dynamics; it
does not state the charge at that state or that it is a maximum.
-/
structure SatisfiesIdealSwitchedLCLaws
    (setup : SwitchedLCCircuit) : Prop where
  steadySourceOhmRelation :
    voltageInVolts setup.sourceEmf =
      resistanceInOhms setup.seriesResistance *
        currentInAmperes setup.steadyCurrentBeforeSwitch
  inductorCurrentIsContinuous :
    currentInAmperes (setup.currentDuringLC setup.switchingInstant) =
      currentInAmperes setup.steadyCurrentBeforeSwitch
  capacitorInitiallyUncharged :
    chargeInCoulombs
      (setup.capacitorChargeDuringLC setup.switchingInstant) = 0
  losslessEnergyConservation : ∀ time,
    totalLCEnergyInJoules setup time =
      totalLCEnergyInJoules setup setup.switchingInstant
  reachesCompleteMagneticToElectricTransfer :
    ∃ time,
      currentInAmperes (setup.currentDuringLC time) = 0

/-! ## Derived peak charge and answer choice -/

/-- A time realizes the maximum charge magnitude over the modeled LC history. -/
def IsMaximumCapacitorChargeAt
    (setup : SwitchedLCCircuit) (peakTime : TimeMagnitude) : Prop :=
  ∀ time,
    chargeInCoulombs (setup.capacitorChargeDuringLC time) ≤
      chargeInCoulombs (setup.capacitorChargeDuringLC peakTime)

/-- Energy conservation bounds the square of every capacitor charge. -/
lemma capacitor_charge_squared_le_initial_magnetic_scale
    (setup : SwitchedLCCircuit)
    (hPositive : HasPositiveCircuitParameters setup)
    (hLaws : SatisfiesIdealSwitchedLCLaws setup) (time : TimeMagnitude) :
    chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 ≤
      inductanceInHenries setup.inductance *
        capacitanceInFarads setup.capacitance *
        currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := by
  have hEnergy := hLaws.losslessEnergyConservation time
  simp [totalLCEnergyInJoules, inductorEnergyInJoules,
    capacitorEnergyInJoules, hLaws.inductorCurrentIsContinuous,
    hLaws.capacitorInitiallyUncharged] at hEnergy
  norm_num at hEnergy
  have hMagneticNonnegative :
      0 ≤ inductanceInHenries setup.inductance *
        currentInAmperes (setup.currentDuringLC time) ^ 2 :=
    mul_nonneg (le_of_lt hPositive.inductancePositive) (sq_nonneg _)
  have hScaledEnergy :
      inductanceInHenries setup.inductance *
          currentInAmperes (setup.currentDuringLC time) ^ 2 +
        chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 /
          capacitanceInFarads setup.capacitance =
        inductanceInHenries setup.inductance *
          currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := by
    linear_combination 2 * hEnergy
  have hDividedBound :
      chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 /
          capacitanceInFarads setup.capacitance ≤
        inductanceInHenries setup.inductance *
          currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := by
    calc
      chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 /
          capacitanceInFarads setup.capacitance ≤
          inductanceInHenries setup.inductance *
              currentInAmperes (setup.currentDuringLC time) ^ 2 +
            chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 /
              capacitanceInFarads setup.capacitance :=
        le_add_of_nonneg_left hMagneticNonnegative
      _ = inductanceInHenries setup.inductance *
          currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := hScaledEnergy
  have hBound := (div_le_iff₀ hPositive.capacitancePositive).mp hDividedBound
  simpa [mul_assoc, mul_comm, mul_left_comm] using hBound

/-- At a zero-current transfer state, the charge obeys `Q = I₀ √(LC)`. -/
lemma charge_at_zero_current_eq_initialCurrent_mul_sqrt_inductance_capacitance
    (setup : SwitchedLCCircuit)
    (hPositive : HasPositiveCircuitParameters setup)
    (hLaws : SatisfiesIdealSwitchedLCLaws setup)
    (time : TimeMagnitude)
    (hZeroCurrent : currentInAmperes (setup.currentDuringLC time) = 0) :
    chargeInCoulombs (setup.capacitorChargeDuringLC time) =
      currentInAmperes setup.steadyCurrentBeforeSwitch *
        Real.sqrt
          (inductanceInHenries setup.inductance *
            capacitanceInFarads setup.capacitance) := by
  have hEnergy := hLaws.losslessEnergyConservation time
  simp [totalLCEnergyInJoules, inductorEnergyInJoules,
    capacitorEnergyInJoules, hLaws.inductorCurrentIsContinuous,
    hLaws.capacitorInitiallyUncharged, hZeroCurrent] at hEnergy
  norm_num at hEnergy
  have hDividedEquality :
      chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 /
          capacitanceInFarads setup.capacitance =
        inductanceInHenries setup.inductance *
          currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := by
    linear_combination 2 * hEnergy
  have hSquare := (div_eq_iff (ne_of_gt hPositive.capacitancePositive)).mp
    hDividedEquality
  have hProductNonnegative :
      0 ≤ inductanceInHenries setup.inductance *
        capacitanceInFarads setup.capacitance :=
    mul_nonneg (le_of_lt hPositive.inductancePositive)
      (le_of_lt hPositive.capacitancePositive)
  have hSquareRoot :=
    Real.sq_sqrt hProductNonnegative
  have hChargeNonnegative :
      0 ≤ chargeInCoulombs (setup.capacitorChargeDuringLC time) := by
    exact NNReal.coe_nonneg _
  have hRightNonnegative :
      0 ≤ currentInAmperes setup.steadyCurrentBeforeSwitch *
        Real.sqrt
          (inductanceInHenries setup.inductance *
            capacitanceInFarads setup.capacitance) :=
    mul_nonneg (le_of_lt hPositive.initialCurrentPositive) (Real.sqrt_nonneg _)
  have hSameSquare :
      chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 =
        (currentInAmperes setup.steadyCurrentBeforeSwitch *
          Real.sqrt
            (inductanceInHenries setup.inductance *
              capacitanceInFarads setup.capacitance)) ^ 2 := by
    calc
      chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 =
          inductanceInHenries setup.inductance *
            currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 *
            capacitanceInFarads setup.capacitance := hSquare
      _ = currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 *
          (inductanceInHenries setup.inductance *
            capacitanceInFarads setup.capacitance) := by ring
      _ = currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 *
          Real.sqrt
            (inductanceInHenries setup.inductance *
              capacitanceInFarads setup.capacitance) ^ 2 := by
            rw [hSquareRoot]
      _ = (currentInAmperes setup.steadyCurrentBeforeSwitch *
          Real.sqrt
            (inductanceInHenries setup.inductance *
              capacitanceInFarads setup.capacitance)) ^ 2 := by ring
  have hFactor :
      (chargeInCoulombs (setup.capacitorChargeDuringLC time) -
          currentInAmperes setup.steadyCurrentBeforeSwitch *
            Real.sqrt
              (inductanceInHenries setup.inductance *
                capacitanceInFarads setup.capacitance)) *
        (chargeInCoulombs (setup.capacitorChargeDuringLC time) +
          currentInAmperes setup.steadyCurrentBeforeSwitch *
            Real.sqrt
              (inductanceInHenries setup.inductance *
                capacitanceInFarads setup.capacitance)) = 0 := by
    calc
      _ = chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 -
          (currentInAmperes setup.steadyCurrentBeforeSwitch *
            Real.sqrt
              (inductanceInHenries setup.inductance *
                capacitanceInFarads setup.capacitance)) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hSameSquare
  rcases mul_eq_zero.mp hFactor with hDifference | hSum
  · exact sub_eq_zero.mp hDifference
  · linarith

/-- The ideal exchange reaches a maximum whose value is `I₀ √(LC)`. -/
lemma exists_maximum_capacitor_charge_formula
    (setup : SwitchedLCCircuit)
    (hPositive : HasPositiveCircuitParameters setup)
    (hLaws : SatisfiesIdealSwitchedLCLaws setup) :
    ∃ peakTime,
      IsMaximumCapacitorChargeAt setup peakTime ∧
      chargeInCoulombs (setup.capacitorChargeDuringLC peakTime) =
        currentInAmperes setup.steadyCurrentBeforeSwitch *
          Real.sqrt
            (inductanceInHenries setup.inductance *
              capacitanceInFarads setup.capacitance) := by
  rcases hLaws.reachesCompleteMagneticToElectricTransfer with
    ⟨peakTime, hZeroCurrent⟩
  have hPeakFormula :=
    charge_at_zero_current_eq_initialCurrent_mul_sqrt_inductance_capacitance
      setup hPositive hLaws peakTime hZeroCurrent
  refine ⟨peakTime, ?_, hPeakFormula⟩
  intro time
  have hBound :=
    capacitor_charge_squared_le_initial_magnetic_scale
      setup hPositive hLaws time
  have hProductNonnegative :
      0 ≤ inductanceInHenries setup.inductance *
        capacitanceInFarads setup.capacitance :=
    mul_nonneg (le_of_lt hPositive.inductancePositive)
      (le_of_lt hPositive.capacitancePositive)
  have hSquareRoot := Real.sq_sqrt hProductNonnegative
  have hPeakSquare :
      chargeInCoulombs (setup.capacitorChargeDuringLC peakTime) ^ 2 =
        inductanceInHenries setup.inductance *
          capacitanceInFarads setup.capacitance *
          currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := by
    calc
      chargeInCoulombs (setup.capacitorChargeDuringLC peakTime) ^ 2 =
          (currentInAmperes setup.steadyCurrentBeforeSwitch *
            Real.sqrt
              (inductanceInHenries setup.inductance *
                capacitanceInFarads setup.capacitance)) ^ 2 := by
            rw [hPeakFormula]
      _ = currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 *
          Real.sqrt
            (inductanceInHenries setup.inductance *
              capacitanceInFarads setup.capacitance) ^ 2 := by ring
      _ = currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 *
          (inductanceInHenries setup.inductance *
            capacitanceInFarads setup.capacitance) := by rw [hSquareRoot]
      _ = inductanceInHenries setup.inductance *
          capacitanceInFarads setup.capacitance *
          currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := by ring
  have hChargeNonnegative :
      0 ≤ chargeInCoulombs (setup.capacitorChargeDuringLC time) := by
    exact NNReal.coe_nonneg _
  have hPeakNonnegative :
      0 ≤ chargeInCoulombs (setup.capacitorChargeDuringLC peakTime) := by
    exact NNReal.coe_nonneg _
  have hSquareBound :
      chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 ≤
        chargeInCoulombs (setup.capacitorChargeDuringLC peakTime) ^ 2 := by
    calc
      chargeInCoulombs (setup.capacitorChargeDuringLC time) ^ 2 ≤
          inductanceInHenries setup.inductance *
            capacitanceInFarads setup.capacitance *
            currentInAmperes setup.steadyCurrentBeforeSwitch ^ 2 := hBound
      _ = chargeInCoulombs (setup.capacitorChargeDuringLC peakTime) ^ 2 :=
        hPeakSquare.symm
  nlinarith only [hSquareBound, hChargeNonnegative, hPeakNonnegative]

/-!
Substitution of `I₀ = 3.50 A`, `L = 2.0 mH`, and `C = 5.0 μF` gives
`Q_max = 3.50 * √(0.002 * 0.000005) C = 0.350 mC`.
-/
lemma maximum_capacitor_charge_is_three_tenths_and_five_hundredths_mC
    (setup : SwitchedLCCircuit)
    (hData : MatchesPrimaryFigureAndReadouts setup)
    (hPositive : HasPositiveCircuitParameters setup)
    (hLaws : SatisfiesIdealSwitchedLCLaws setup) :
    ∃ peakTime,
      IsMaximumCapacitorChargeAt setup peakTime ∧
      chargeInMillicoulombs
        (setup.capacitorChargeDuringLC peakTime) = (7 / 20 : ℝ) := by
  rcases exists_maximum_capacitor_charge_formula setup hPositive hLaws with
    ⟨peakTime, hMaximum, hPeakFormula⟩
  have hInductance :
      inductanceInHenries setup.inductance = (1 / 500 : ℝ) := by
    have h := hData.physicalInductanceMatchesFigure
    rw [hData.printedInductorLabel] at h
    norm_num [inductanceInMillihenries] at h ⊢
    linarith
  have hCapacitance :
      capacitanceInFarads setup.capacitance = (1 / 200000 : ℝ) := by
    have h := hData.physicalCapacitanceMatchesFigure
    rw [hData.printedCapacitorLabel] at h
    norm_num [capacitanceInMicrofarads] at h ⊢
    linarith
  have hCurrent :
      currentInAmperes setup.steadyCurrentBeforeSwitch = (7 / 2 : ℝ) := by
    calc
      currentInAmperes setup.steadyCurrentBeforeSwitch =
          setup.ammeterReadingInAmperes :=
        hData.ammeterMeasuresSteadyInductorCurrent
      _ = 7 / 2 := hData.ammeterReadsThreePointFiveAmperes
  have hSquareRoot :
      Real.sqrt ((1 / 500 : ℝ) * (1 / 200000 : ℝ)) = (1 / 10000 : ℝ) := by
    have hSquare := Real.sq_sqrt
      (show 0 ≤ (1 / 500 : ℝ) * (1 / 200000 : ℝ) by norm_num)
    have hNonnegative :=
      Real.sqrt_nonneg ((1 / 500 : ℝ) * (1 / 200000 : ℝ))
    norm_num at hSquare ⊢
  refine ⟨peakTime, hMaximum, ?_⟩
  simp only [chargeInMillicoulombs]
  rw [hPeakFormula, hCurrent, hInductance, hCapacitance, hSquareRoot]
  norm_num

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Charge in millicoulombs printed beside each answer label. -/
def answerChargeInMillicoulombs : AnswerChoice → ℝ
  | .A => 7 / 200
  | .B => 7 / 20
  | .C => 7 / 100
  | .D => 7 / 4

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed choice agrees with an independently derived maximum charge. -/
def AnswerMatchesMaximumCapacitorCharge
    (setup : SwitchedLCCircuit) (choice : AnswerChoice) : Prop :=
  ∃ peakTime,
    IsMaximumCapacitorChargeAt setup peakTime ∧
    chargeInMillicoulombs (setup.capacitorChargeDuringLC peakTime) =
      answerChargeInMillicoulombs choice

/--
The maximum capacitor charge is `0.350 mC`; hence choice B, the recorded
dataset answer, matches the ideal switched-LC model.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0987:target`.
-/
theorem maximum_capacitor_charge_and_answer
    (setup : SwitchedLCCircuit)
    (hFigure : MatchesPrimaryFigureAndReadouts setup)
    (hSwitching : MatchesSimultaneousSwitchingProtocol setup)
    (hPositive : HasPositiveCircuitParameters setup)
    (hLaws : SatisfiesIdealSwitchedLCLaws setup) :
    (∃ peakTime,
      IsMaximumCapacitorChargeAt setup peakTime ∧
      chargeInMillicoulombs
        (setup.capacitorChargeDuringLC peakTime) = (7 / 20 : ℝ)) ∧
    AnswerMatchesMaximumCapacitorCharge setup .B ∧
    recordedDatasetAnswer = .B := by
  rcases
      maximum_capacitor_charge_is_three_tenths_and_five_hundredths_mC
        setup hFigure hPositive hLaws with
    ⟨peakTime, hMaximum, hCharge⟩
  refine ⟨⟨peakTime, hMaximum, hCharge⟩, ?_, rfl⟩
  refine ⟨peakTime, hMaximum, ?_⟩
  simpa [answerChargeInMillicoulombs] using hCharge

end PhyXMiniProblems.ProblemPhyXMini0987
