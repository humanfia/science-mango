import Mathlib
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0612

open Dimension

/-!
# Minimum stopping resistance in a photoelectric circuit

The primary raster shows an illuminated cathode on the left, an anode and
ammeter on the right, a variable resistor `R`, a `1.00 kΩ` resistor, two
oppositely oriented `15.0 V` sources, and switch positions `a` and `b`.
The prose returns the switch to `a`, reduces the wavelength to `65.0 nm`, and
reports an increased photocurrent.

The word “returned” makes this excerpt dependent on an earlier part of the
problem, but the supplied chapter contains no earlier numerical result.  The
needed `5.09 eV` material work-function result is therefore represented by a
separate, explicit previous-part hypothesis.  It is not built into the setup,
the circuit laws, or the definition of a stopping resistance.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Electric potential has the dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current has the dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electric resistance has the dimension potential divided by current. -/
def electricResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Action, the dimensional role of Planck's constant, is energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative magnitude of electric potential. -/
abbrev ElectricPotentialMagnitude : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative magnitude of electric current. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative physical resistance. -/
abbrev ElectricResistanceQuantity : Type :=
  Dimensionful (WithDim electricResistanceDimension NNReal)

/-- A nonnegative magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A nonnegative physical quantity with the dimension of action. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Coherent-SI scalar component of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Wavelength readout in metres. -/
def wavelengthInMetres (wavelength : WavelengthQuantity) : ℝ :=
  nonnegativeSIReadout wavelength

/-- Electric-potential magnitude readout in volts. -/
def potentialInVolts (potential : ElectricPotentialMagnitude) : ℝ :=
  nonnegativeSIReadout potential

/-- Electric-current magnitude readout in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Electric-resistance readout in ohms. -/
def resistanceInOhms (resistance : ElectricResistanceQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-- Electric-resistance readout in kilohms. -/
def resistanceInKiloOhms (resistance : ElectricResistanceQuantity) : ℝ :=
  resistanceInOhms resistance / 1000

/-- Electric-charge magnitude readout in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Speed readout in metres per second. -/
def speedInMetresPerSecond (speed : SpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Planck-constant readout in joule-seconds. -/
def planckConstantInJouleSeconds (constant : PlanckConstantQuantity) : ℝ :=
  nonnegativeSIReadout constant

/-- Energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Physlib-grounded physical constants and displayed unit scales -/

/-- Physlib's exact elementary-charge magnitude, expressed in coulombs. -/
def physlibElementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-- Physlib's speed of light, expressed in metres per second. -/
def physlibSpeedOfLightInMetresPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-!
Physlib supplies the reduced Planck constant `ℏ` as a positive scalar in
joule-seconds.  The ordinary Planck constant used by the photon-energy law is
`h = 2πℏ`.
-/
def physlibPlanckConstantInJouleSeconds : ℝ :=
  2 * Real.pi * (Constants.ℏ : ℝ)

/-- One nanometre expressed in metres. -/
def nanometreInMetres : ℝ :=
  (10 : ℝ) ^ (-9 : ℤ)

/-! ## Labels and geometry read from the primary circuit raster -/

/-- The two labeled switch positions. -/
inductive SwitchPosition where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- The upper and lower `15.0 V` cells in the figure. -/
inductive FigureBattery where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Left and right sides of the circuit drawing. -/
inductive CircuitSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Cathode and anode of the photoelectric tube. -/
inductive Electrode where
  | cathode
  | anode
  deriving DecidableEq, Fintype, Repr

/-- Signs printed under the electrodes in the `V_AC` annotation. -/
inductive PotentialSign where
  | negative
  | positive
  deriving DecidableEq, Repr

/-- The two current arrows labeled in the diagram. -/
inductive FigureCurrent where
  | resistorCurrentI
  | photocurrenti
  deriving DecidableEq, Fintype, Repr

/-- Directions of the current arrows on the page. -/
inductive FigureArrowDirection where
  | rightward
  | upward
  deriving DecidableEq, Repr

/-!
Typed presentation data from image 612.  Physical component values remain
dimensionful; the Booleans record literal schematic labels and symbols.
-/
structure PhotoelectricCircuitFigure where
  switchPositionShown : SwitchPosition
  switchLabelShown : SwitchPosition → Bool
  batteryPotential : FigureBattery → ElectricPotentialMagnitude
  batteryPositiveTerminal : FigureBattery → CircuitSide
  fixedResistor : ElectricResistanceQuantity
  variableResistorRShown : Bool
  ammeterAShown : Bool
  incidentWavelengthSymbolShown : Bool
  workFunctionSymbolShown : Bool
  emittedElectronShown : Bool
  emittedElectronVelocityShown : Bool
  electrodeSide : Electrode → CircuitSide
  electrodePotentialSign : Electrode → PotentialSign
  currentArrowDirection : FigureCurrent → FigureArrowDirection

/-! ## Experiment, scenario data, and previous-part interface -/

/-!
The experiment carries independent physical quantities and response maps.
In particular, neither a stopping-resistance value nor an answer label is a
field.  `photocurrentAt` represents the ammeter magnitude for a switch
position, wavelength, and candidate setting of the variable resistor `R`.
-/
structure PhotoelectricCircuitExperiment where
  materialWorkFunction : DimEnergy
  earlierIncidentWavelength : WavelengthQuantity
  newIncidentWavelength : WavelengthQuantity
  resistanceAtObservedIncrease : ElectricResistanceQuantity
  sourcePotentialAtA : ElectricPotentialMagnitude
  fixedSeriesResistance : ElectricResistanceQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  speedOfLight : SpeedQuantity
  planckConstant : PlanckConstantQuantity
  photonEnergyAt : WavelengthQuantity → DimEnergy
  maximumPhotoelectronKineticEnergyAt : WavelengthQuantity → DimEnergy
  retardingPotentialAt : SwitchPosition →
    ElectricResistanceQuantity → ElectricPotentialMagnitude
  photocurrentAt : SwitchPosition → WavelengthQuantity →
    ElectricResistanceQuantity → ElectricCurrentMagnitude
  figure : PhotoelectricCircuitFigure

/-!
Literal component values, polarities, labels, and arrow directions visible in
the primary image.  The opposite battery polarities here follow the raster,
not the auxiliary caption's claim that the sources are simply in series.
-/
structure MatchesPrimaryCircuitFigure
    (setup : PhotoelectricCircuitExperiment) : Prop where
  switchShownAtA : setup.figure.switchPositionShown = .a
  bothSwitchLabelsShown : ∀ position,
    setup.figure.switchLabelShown position = true
  bothBatteryLabelsAreFifteenVolts : ∀ battery,
    potentialInVolts (setup.figure.batteryPotential battery) = 15
  upperBatteryPositiveOnLeft :
    setup.figure.batteryPositiveTerminal .upper = .left
  lowerBatteryPositiveOnRight :
    setup.figure.batteryPositiveTerminal .lower = .right
  fixedResistorLabel :
    resistanceInOhms setup.figure.fixedResistor = 1000
  figureFixedResistorIsCircuitComponent :
    setup.fixedSeriesResistance = setup.figure.fixedResistor
  sourceAtAIsLowerBattery :
    setup.sourcePotentialAtA = setup.figure.batteryPotential .lower
  variableResistorLabel : setup.figure.variableResistorRShown = true
  ammeterLabel : setup.figure.ammeterAShown = true
  wavelengthLabel : setup.figure.incidentWavelengthSymbolShown = true
  workFunctionLabel : setup.figure.workFunctionSymbolShown = true
  electronSymbol : setup.figure.emittedElectronShown = true
  velocityArrow : setup.figure.emittedElectronVelocityShown = true
  cathodeOnLeft : setup.figure.electrodeSide .cathode = .left
  anodeOnRight : setup.figure.electrodeSide .anode = .right
  cathodeSign : setup.figure.electrodePotentialSign .cathode = .negative
  anodeSign : setup.figure.electrodePotentialSign .anode = .positive
  resistorCurrentPointsRight :
    setup.figure.currentArrowDirection .resistorCurrentI = .rightward
  photocurrentPointsUp :
    setup.figure.currentArrowDirection .photocurrenti = .upward

/-!
The prose readouts and observation at switch position `a`.  The comparison of
the two ammeter readouts records the stated current increase but prescribes no
stopping resistance.
-/
structure MatchesProblemScenario
    (setup : PhotoelectricCircuitExperiment) : Prop where
  newWavelengthReadout :
    wavelengthInMetres setup.newIncidentWavelength = 65 * nanometreInMetres
  wavelengthWasReduced :
    wavelengthInMetres setup.newIncidentWavelength <
      wavelengthInMetres setup.earlierIncidentWavelength
  photocurrentIncreased :
    currentInAmperes
        (setup.photocurrentAt .a setup.earlierIncidentWavelength
          setup.resistanceAtObservedIncrease) <
      currentInAmperes
        (setup.photocurrentAt .a setup.newIncidentWavelength
          setup.resistanceAtObservedIncrease)

/-!
The prior part's material calibration, kept separate because its value is not
printed in the supplied excerpt.  This is a work-function result, not the
current question's stopping-resistance result.
-/
structure UsesPreviousPartWorkFunctionResult
    (setup : PhotoelectricCircuitExperiment) : Prop where
  workFunctionReadout :
    energyInJoules setup.materialWorkFunction /
        physlibElementaryChargeInCoulombs = 5.09

/-! ## Constant calibrations, sign conditions, and uniform governing laws -/

/-- The experiment uses the standard Physlib constants. -/
structure UsesStandardPhysicalConstants
    (setup : PhotoelectricCircuitExperiment) : Prop where
  electronChargeCalibration :
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
      physlibElementaryChargeInCoulombs
  speedOfLightCalibration :
    speedInMetresPerSecond setup.speedOfLight =
      physlibSpeedOfLightInMetresPerSecond
  planckConstantCalibration :
    planckConstantInJouleSeconds setup.planckConstant =
      physlibPlanckConstantInJouleSeconds

/-- Positivity and emission-side conditions for the physical setup. -/
structure HasPhysicalPhotoelectricCircuitParameters
    (setup : PhotoelectricCircuitExperiment) : Prop where
  earlierWavelengthPositive :
    0 < wavelengthInMetres setup.earlierIncidentWavelength
  newWavelengthPositive :
    0 < wavelengthInMetres setup.newIncidentWavelength
  sourcePotentialPositive :
    0 < potentialInVolts setup.sourcePotentialAtA
  fixedResistancePositive :
    0 < resistanceInOhms setup.fixedSeriesResistance
  electronChargePositive :
    0 < chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  speedOfLightPositive :
    0 < speedInMetresPerSecond setup.speedOfLight
  planckConstantPositive :
    0 < planckConstantInJouleSeconds setup.planckConstant
  workFunctionNonnegative :
    0 ≤ energyInJoules setup.materialWorkFunction
  newPhotonCanEmit :
    energyInJoules setup.materialWorkFunction ≤
      energyInJoules (setup.photonEnergyAt setup.newIncidentWavelength)

/-!
Uniform physical laws used in the calculation:

* photon energy is `Eγ = h c / λ`;
* Einstein's photoelectric balance is `Kmax = Eγ - φ`;
* at switch `a`, the retarding voltage is the voltage-divider readout;
* photocurrent is zero exactly when `e Vret ≥ Kmax`.

All laws quantify over arbitrary wavelengths or resistance settings and none
mentions `13.8 kΩ` or a displayed answer label.
-/
structure SatisfiesPhotoelectricCircuitLaws
    (setup : PhotoelectricCircuitExperiment) : Prop where
  photonEnergyLaw : ∀ wavelength,
    0 < wavelengthInMetres wavelength →
      energyInJoules (setup.photonEnergyAt wavelength) =
        planckConstantInJouleSeconds setup.planckConstant *
          speedInMetresPerSecond setup.speedOfLight /
            wavelengthInMetres wavelength
  einsteinPhotoelectricLaw : ∀ wavelength,
    energyInJoules
        (setup.maximumPhotoelectronKineticEnergyAt wavelength) =
      energyInJoules (setup.photonEnergyAt wavelength) -
        energyInJoules setup.materialWorkFunction
  voltageDividerLawAtA : ∀ resistance,
    potentialInVolts (setup.retardingPotentialAt .a resistance) =
      potentialInVolts setup.sourcePotentialAtA *
          resistanceInOhms resistance /
        (resistanceInOhms resistance +
          resistanceInOhms setup.fixedSeriesResistance)
  zeroPhotocurrentThreshold : ∀ wavelength resistance,
    currentInAmperes (setup.photocurrentAt .a wavelength resistance) = 0 ↔
      energyInJoules
          (setup.maximumPhotoelectronKineticEnergyAt wavelength) ≤
        chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          potentialInVolts (setup.retardingPotentialAt .a resistance)

/-! ## Stopping resistance and answer metadata -/

/-- The ammeter reads zero at the new wavelength and switch position `a`. -/
def PhotocurrentCeasesAt
    (setup : PhotoelectricCircuitExperiment)
    (resistance : ElectricResistanceQuantity) : Prop :=
  currentInAmperes
      (setup.photocurrentAt .a setup.newIncidentWavelength resistance) = 0

/-!
A physical resistance is a minimum stopping setting when it stops the current
and no other stopping setting has a smaller coherent-SI resistance readout.
-/
def IsMinimumStoppingResistance
    (setup : PhotoelectricCircuitExperiment)
    (resistance : ElectricResistanceQuantity) : Prop :=
  PhotocurrentCeasesAt setup resistance ∧
    ∀ otherResistance,
      PhotocurrentCeasesAt setup otherResistance →
        resistanceInOhms resistance ≤ resistanceInOhms otherResistance

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Resistance readout printed for each choice, in kilohms. -/
def displayedResistanceInKiloOhms : AnswerChoice → ℝ
  | .A => 13.8
  | .B => 12.7
  | .C => 11.9
  | .D => 11.6

/-- Half of the `0.1 kΩ` precision to which the choices are displayed. -/
def displayedResistanceToleranceInKiloOhms : ℝ :=
  0.05

/-- A displayed choice agrees, to displayed precision, with a physical minimum. -/
def MatchesDisplayedMinimumStoppingResistance
    (setup : PhotoelectricCircuitExperiment)
    (choice : AnswerChoice) : Prop :=
  ∃ minimumResistance,
    IsMinimumStoppingResistance setup minimumResistance ∧
      |resistanceInKiloOhms minimumResistance -
        displayedResistanceInKiloOhms choice| <
          displayedResistanceToleranceInKiloOhms

/-- Exactly one displayed choice agrees with the physical minimum. -/
def IsUniqueMatchingMinimumStoppingResistance
    (setup : PhotoelectricCircuitExperiment)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedMinimumStoppingResistance setup choice ∧
    ∀ otherChoice,
      MatchesDisplayedMinimumStoppingResistance setup otherChoice →
        otherChoice = choice

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
At a least stopping resistance, the voltage divider supplies exactly the
stopping energy.  This is a derived threshold relation, not an assumption.
-/
lemma minimum_stoppingResistance_satisfies_thresholdEquality
    (setup : PhotoelectricCircuitExperiment)
    (hPhysical : HasPhysicalPhotoelectricCircuitParameters setup)
    (hLaws : SatisfiesPhotoelectricCircuitLaws setup)
    (minimumResistance : ElectricResistanceQuantity)
    (hMinimum : IsMinimumStoppingResistance setup minimumResistance) :
    energyInJoules
        (setup.maximumPhotoelectronKineticEnergyAt
          setup.newIncidentWavelength) =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        potentialInVolts
          (setup.retardingPotentialAt .a minimumResistance) := by
  let kineticEnergy :=
    energyInJoules
      (setup.maximumPhotoelectronKineticEnergyAt
        setup.newIncidentWavelength)
  let charge := chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  let sourceVoltage := potentialInVolts setup.sourcePotentialAtA
  let fixedResistance := resistanceInOhms setup.fixedSeriesResistance
  let minimumReadout := resistanceInOhms minimumResistance
  have hKineticEnergyNonnegative : 0 ≤ kineticEnergy := by
    dsimp [kineticEnergy]
    rw [hLaws.einsteinPhotoelectricLaw]
    exact sub_nonneg.mpr hPhysical.newPhotonCanEmit
  have hChargePositive : 0 < charge := hPhysical.electronChargePositive
  have hSourceVoltagePositive : 0 < sourceVoltage :=
    hPhysical.sourcePotentialPositive
  have hFixedResistancePositive : 0 < fixedResistance :=
    hPhysical.fixedResistancePositive
  have hMinimumReadoutNonnegative : 0 ≤ minimumReadout := by
    dsimp [minimumReadout, resistanceInOhms, nonnegativeSIReadout]
    exact_mod_cast (minimumResistance UnitChoices.SI).val.property
  have hDenominatorPositive : 0 < minimumReadout + fixedResistance := by
    linarith
  have hThreshold :
      kineticEnergy ≤
        charge * (sourceVoltage * minimumReadout /
          (minimumReadout + fixedResistance)) := by
    have hCeases := hMinimum.1
    have hThreshold' :=
      (hLaws.zeroPhotocurrentThreshold
        setup.newIncidentWavelength minimumResistance).mp
        (by simpa [PhotocurrentCeasesAt] using hCeases)
    rw [hLaws.voltageDividerLawAtA] at hThreshold'
    exact hThreshold'
  have hCrossMultiplied :
      kineticEnergy * (minimumReadout + fixedResistance) ≤
        charge * (sourceVoltage * minimumReadout) := by
    apply (le_div_iff₀ hDenominatorPositive).mp
    calc
      kineticEnergy ≤
          charge * (sourceVoltage * minimumReadout /
            (minimumReadout + fixedResistance)) := hThreshold
      _ = charge * (sourceVoltage * minimumReadout) /
          (minimumReadout + fixedResistance) := by ring
  have hAvailableVoltagePositive :
      0 < charge * sourceVoltage - kineticEnergy := by
    have hChargeSourcePositive : 0 < charge * sourceVoltage :=
      mul_pos hChargePositive hSourceVoltagePositive
    have hKineticFixedNonnegative :
        0 ≤ kineticEnergy * fixedResistance :=
      mul_nonneg hKineticEnergyNonnegative
        (le_of_lt hFixedResistancePositive)
    by_contra hNotPositive
    have hNonpositive :
        charge * sourceVoltage - kineticEnergy ≤ 0 :=
      le_of_not_gt hNotPositive
    have hProductNonpositive :
        (charge * sourceVoltage - kineticEnergy) * minimumReadout ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hNonpositive
        hMinimumReadoutNonnegative
    nlinarith
  let thresholdReadout :=
    kineticEnergy * fixedResistance /
      (charge * sourceVoltage - kineticEnergy)
  have hThresholdReadoutNonnegative : 0 ≤ thresholdReadout := by
    dsimp [thresholdReadout]
    positivity
  let thresholdResistance : ElectricResistanceQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      ⟨⟨thresholdReadout, hThresholdReadoutNonnegative⟩⟩
  have hThresholdResistanceReadout :
      resistanceInOhms thresholdResistance = thresholdReadout := by
    dsimp [thresholdResistance, resistanceInOhms, nonnegativeSIReadout]
    rw [CarriesDimension.toDimensionful_apply_apply]
    simp only [UnitChoices.dimScale_self, one_smul]
    rfl
  have hThresholdFormula :
      charge *
          (sourceVoltage * thresholdReadout /
            (thresholdReadout + fixedResistance)) =
        kineticEnergy := by
    dsimp [thresholdReadout]
    field_simp
    ring
  have hThresholdResistanceCeases :
      PhotocurrentCeasesAt setup thresholdResistance := by
    apply
      (hLaws.zeroPhotocurrentThreshold
        setup.newIncidentWavelength thresholdResistance).mpr
    rw [hLaws.voltageDividerLawAtA, hThresholdResistanceReadout]
    exact le_of_eq hThresholdFormula.symm
  have hMinimumLeThreshold :
      minimumReadout ≤ thresholdReadout := by
    simpa [minimumReadout, hThresholdResistanceReadout] using
      hMinimum.2 thresholdResistance hThresholdResistanceCeases
  have hThresholdLeMinimum :
      thresholdReadout ≤ minimumReadout := by
    apply (div_le_iff₀ hAvailableVoltagePositive).mpr
    nlinarith
  have hReadoutEquality : minimumReadout = thresholdReadout :=
    le_antisymm hMinimumLeThreshold hThresholdLeMinimum
  rw [hLaws.voltageDividerLawAtA]
  change kineticEnergy =
    charge *
      (sourceVoltage * minimumReadout /
        (minimumReadout + fixedResistance))
  rw [hReadoutEquality]
  exact hThresholdFormula.symm

/-!
The physical minimum exists and rounds to `13.8 kΩ` after applying the
previous work-function result, the `65.0 nm` readout, the photoelectric laws,
and the switch-`a` voltage divider.
-/
lemma exists_minimum_stoppingResistance_near_thirteenPointEightKiloOhms
    (setup : PhotoelectricCircuitExperiment)
    (hFigure : MatchesPrimaryCircuitFigure setup)
    (hScenario : MatchesProblemScenario setup)
    (hPreviousPart : UsesPreviousPartWorkFunctionResult setup)
    (hConstants : UsesStandardPhysicalConstants setup)
    (hPhysical : HasPhysicalPhotoelectricCircuitParameters setup)
    (hLaws : SatisfiesPhotoelectricCircuitLaws setup) :
    ∃ minimumResistance,
      IsMinimumStoppingResistance setup minimumResistance ∧
        |resistanceInKiloOhms minimumResistance - 13.8| < 0.05 := by
  let wavelength := wavelengthInMetres setup.newIncidentWavelength
  let charge := chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  let lightSpeed := speedInMetresPerSecond setup.speedOfLight
  let planck := planckConstantInJouleSeconds setup.planckConstant
  let workFunction := energyInJoules setup.materialWorkFunction
  let kineticEnergy :=
    energyInJoules
      (setup.maximumPhotoelectronKineticEnergyAt
        setup.newIncidentWavelength)
  let sourceVoltage := potentialInVolts setup.sourcePotentialAtA
  let fixedResistance := resistanceInOhms setup.fixedSeriesResistance
  have hWavelength :
      wavelength = 65 * (10 : ℝ) ^ (-9 : ℤ) := by
    simpa [wavelength, nanometreInMetres] using
      hScenario.newWavelengthReadout
  have hCharge :
      charge = 1.602176634e-19 := by
    calc
      charge = physlibElementaryChargeInCoulombs :=
        hConstants.electronChargeCalibration
      _ = 1.602176634e-19 := by
        norm_num [physlibElementaryChargeInCoulombs,
          ChargeUnit.elementaryCharge, ChargeUnit.coulombs,
          ChargeUnit.scale, ChargeUnit.div_eq_val, NNReal.toReal]
  have hLightSpeed : lightSpeed = 299792458 := by
    calc
      lightSpeed = physlibSpeedOfLightInMetresPerSecond :=
        hConstants.speedOfLightCalibration
      _ = 299792458 := by
        norm_num [physlibSpeedOfLightInMetresPerSecond,
          DimSpeed.speedOfLight_in_SI]
  have hPlanck :
      planck = 2 * Real.pi * 1.054571817e-34 := by
    calc
      planck = physlibPlanckConstantInJouleSeconds :=
        hConstants.planckConstantCalibration
      _ = 2 * Real.pi * 1.054571817e-34 := by
        norm_num [physlibPlanckConstantInJouleSeconds, Constants.ℏ]
  have hSourceVoltage : sourceVoltage = 15 := by
    calc
      sourceVoltage =
          potentialInVolts (setup.figure.batteryPotential .lower) := by
        dsimp [sourceVoltage]
        rw [hFigure.sourceAtAIsLowerBattery]
      _ = 15 := hFigure.bothBatteryLabelsAreFifteenVolts .lower
  have hFixedResistance : fixedResistance = 1000 := by
    calc
      fixedResistance = resistanceInOhms setup.figure.fixedResistor := by
        dsimp [fixedResistance]
        rw [hFigure.figureFixedResistorIsCircuitComponent]
      _ = 1000 := hFigure.fixedResistorLabel
  have hChargePositive : 0 < charge := by
    rw [hCharge]
    norm_num
  have hWorkFunction :
      workFunction = charge * 5.09 := by
    have hRatio := hPreviousPart.workFunctionReadout
    rw [← hConstants.electronChargeCalibration] at hRatio
    change workFunction / charge = 5.09 at hRatio
    have hProduct := (div_eq_iff (ne_of_gt hChargePositive)).mp hRatio
    nlinarith
  have hKineticEnergy :
      kineticEnergy =
        planck * lightSpeed / wavelength - charge * 5.09 := by
    calc
      kineticEnergy =
          energyInJoules
              (setup.photonEnergyAt setup.newIncidentWavelength) -
            workFunction := hLaws.einsteinPhotoelectricLaw _
      _ = planck * lightSpeed / wavelength - workFunction := by
        rw [hLaws.photonEnergyLaw _
          hPhysical.newWavelengthPositive]
      _ = planck * lightSpeed / wavelength - charge * 5.09 := by
        rw [hWorkFunction]
  have hKineticEnergyNumeric :
      kineticEnergy =
        (2 * Real.pi * 1.054571817e-34) * 299792458 /
            (65 * (10 : ℝ) ^ (-9 : ℤ)) -
          (1.602176634e-19 : ℝ) * 5.09 := by
    rw [hKineticEnergy, hPlanck, hLightSpeed, hWavelength, hCharge]
  have hKineticEnergyPositive : 0 < kineticEnergy := by
    rw [hKineticEnergyNumeric]
    norm_num [zpow_neg]
    nlinarith [Real.pi_gt_d20]
  have hAvailableVoltagePositive :
      0 < charge * sourceVoltage - kineticEnergy := by
    rw [hCharge, hSourceVoltage, hKineticEnergyNumeric]
    norm_num [zpow_neg]
    nlinarith [Real.pi_lt_d20]
  let thresholdReadout :=
    kineticEnergy * fixedResistance /
      (charge * sourceVoltage - kineticEnergy)
  have hThresholdReadoutNonnegative : 0 ≤ thresholdReadout := by
    dsimp [thresholdReadout]
    positivity
  let thresholdResistance : ElectricResistanceQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      ⟨⟨thresholdReadout, hThresholdReadoutNonnegative⟩⟩
  have hThresholdResistanceReadout :
      resistanceInOhms thresholdResistance = thresholdReadout := by
    dsimp [thresholdResistance, resistanceInOhms, nonnegativeSIReadout]
    rw [CarriesDimension.toDimensionful_apply_apply]
    simp only [UnitChoices.dimScale_self, one_smul]
    rfl
  have hThresholdFormula :
      charge *
          (sourceVoltage * thresholdReadout /
            (thresholdReadout + fixedResistance)) =
        kineticEnergy := by
    dsimp [thresholdReadout]
    field_simp
    ring
  have hThresholdResistanceCeases :
      PhotocurrentCeasesAt setup thresholdResistance := by
    apply
      (hLaws.zeroPhotocurrentThreshold
        setup.newIncidentWavelength thresholdResistance).mpr
    rw [hLaws.voltageDividerLawAtA, hThresholdResistanceReadout]
    change kineticEnergy ≤
      charge *
        (sourceVoltage * thresholdReadout /
          (thresholdReadout + fixedResistance))
    exact le_of_eq hThresholdFormula.symm
  have hThresholdResistanceMinimum :
      IsMinimumStoppingResistance setup thresholdResistance := by
    refine ⟨hThresholdResistanceCeases, ?_⟩
    intro otherResistance hOtherCeases
    let otherReadout := resistanceInOhms otherResistance
    have hOtherReadoutNonnegative : 0 ≤ otherReadout := by
      dsimp [otherReadout, resistanceInOhms, nonnegativeSIReadout]
      exact_mod_cast (otherResistance UnitChoices.SI).val.property
    have hOtherDenominatorPositive :
        0 < otherReadout + fixedResistance := by
      rw [hFixedResistance]
      linarith
    have hOtherThreshold :
        kineticEnergy ≤
          charge * (sourceVoltage * otherReadout /
            (otherReadout + fixedResistance)) := by
      have hThreshold' :=
        (hLaws.zeroPhotocurrentThreshold
          setup.newIncidentWavelength otherResistance).mp
          (by simpa [PhotocurrentCeasesAt] using hOtherCeases)
      rw [hLaws.voltageDividerLawAtA] at hThreshold'
      simpa [kineticEnergy, charge, sourceVoltage, fixedResistance,
        otherReadout] using hThreshold'
    have hOtherCrossMultiplied :
        kineticEnergy * (otherReadout + fixedResistance) ≤
          charge * (sourceVoltage * otherReadout) := by
      apply (le_div_iff₀ hOtherDenominatorPositive).mp
      calc
        kineticEnergy ≤
            charge * (sourceVoltage * otherReadout /
              (otherReadout + fixedResistance)) := hOtherThreshold
        _ = charge * (sourceVoltage * otherReadout) /
            (otherReadout + fixedResistance) := by ring
    rw [hThresholdResistanceReadout]
    apply (div_le_iff₀ hAvailableVoltagePositive).mpr
    nlinarith
  have hThresholdKilohms :
      resistanceInKiloOhms thresholdResistance =
        kineticEnergy / (charge * sourceVoltage - kineticEnergy) := by
    rw [resistanceInKiloOhms, hThresholdResistanceReadout]
    dsimp [thresholdReadout]
    rw [hFixedResistance]
    field_simp
  have hThresholdNear :
      |resistanceInKiloOhms thresholdResistance - 13.8| < 0.05 := by
    rw [hThresholdKilohms, hKineticEnergyNumeric, hCharge, hSourceVoltage]
    have hDenominator :
        0 < (1.602176634e-19 : ℝ) * 15 -
          ((2 * Real.pi * 1.054571817e-34) * 299792458 /
              (65 * (10 : ℝ) ^ (-9 : ℤ)) -
            (1.602176634e-19 : ℝ) * 5.09) := by
      norm_num [zpow_neg]
      nlinarith [Real.pi_lt_d20]
    rw [abs_lt]
    constructor
    · have hLower :
          (13.75 : ℝ) <
            ((2 * Real.pi * 1.054571817e-34) * 299792458 /
                (65 * (10 : ℝ) ^ (-9 : ℤ)) -
              (1.602176634e-19 : ℝ) * 5.09) /
              ((1.602176634e-19 : ℝ) * 15 -
                ((2 * Real.pi * 1.054571817e-34) * 299792458 /
                    (65 * (10 : ℝ) ^ (-9 : ℤ)) -
                  (1.602176634e-19 : ℝ) * 5.09)) := by
        apply (lt_div_iff₀ hDenominator).mpr
        norm_num [zpow_neg]
        nlinarith [Real.pi_gt_d20]
      linarith
    · have hUpper :
          ((2 * Real.pi * 1.054571817e-34) * 299792458 /
                (65 * (10 : ℝ) ^ (-9 : ℤ)) -
              (1.602176634e-19 : ℝ) * 5.09) /
              ((1.602176634e-19 : ℝ) * 15 -
                ((2 * Real.pi * 1.054571817e-34) * 299792458 /
                    (65 * (10 : ℝ) ^ (-9 : ℤ)) -
                  (1.602176634e-19 : ℝ) * 5.09)) < 13.85 := by
        apply (div_lt_iff₀ hDenominator).mpr
        norm_num [zpow_neg]
        nlinarith [Real.pi_lt_d20]
      linarith
  exact
    ⟨thresholdResistance, hThresholdResistanceMinimum, hThresholdNear⟩

/-!
The minimum resistance that makes the photocurrent cease is approximately
`13.8 kΩ`, uniquely selecting displayed answer A.

This formalizes blueprint label `thm:physics:phyx_mini_0612:target`.
-/
theorem problem_phyx_mini_0612
    (setup : PhotoelectricCircuitExperiment)
    (hFigure : MatchesPrimaryCircuitFigure setup)
    (hScenario : MatchesProblemScenario setup)
    (hPreviousPart : UsesPreviousPartWorkFunctionResult setup)
    (hConstants : UsesStandardPhysicalConstants setup)
    (hPhysical : HasPhysicalPhotoelectricCircuitParameters setup)
    (hLaws : SatisfiesPhotoelectricCircuitLaws setup) :
    IsUniqueMatchingMinimumStoppingResistance setup recordedDatasetAnswer := by
  obtain ⟨minimumResistance, hMinimum, hMinimumNear⟩ :=
    exists_minimum_stoppingResistance_near_thirteenPointEightKiloOhms
      setup hFigure hScenario hPreviousPart hConstants hPhysical hLaws
  constructor
  · refine ⟨minimumResistance, hMinimum, ?_⟩
    simpa [recordedDatasetAnswer, displayedResistanceInKiloOhms,
      displayedResistanceToleranceInKiloOhms] using hMinimumNear
  · intro otherChoice hOtherChoice
    obtain ⟨otherMinimum, hOtherMinimum, hOtherNear⟩ := hOtherChoice
    have hReadoutEquality :
        resistanceInOhms minimumResistance =
          resistanceInOhms otherMinimum :=
      le_antisymm
        (hMinimum.2 otherMinimum hOtherMinimum.1)
        (hOtherMinimum.2 minimumResistance hMinimum.1)
    have hKiloOhmEquality :
        resistanceInKiloOhms minimumResistance =
          resistanceInKiloOhms otherMinimum := by
      rw [resistanceInKiloOhms, resistanceInKiloOhms,
        hReadoutEquality]
    cases otherChoice with
    | A =>
        rfl
    | B =>
        rw [← hKiloOhmEquality] at hOtherNear
        rw [abs_lt] at hMinimumNear hOtherNear
        norm_num [displayedResistanceInKiloOhms,
          displayedResistanceToleranceInKiloOhms] at hOtherNear
        linarith
    | C =>
        rw [← hKiloOhmEquality] at hOtherNear
        rw [abs_lt] at hMinimumNear hOtherNear
        norm_num [displayedResistanceInKiloOhms,
          displayedResistanceToleranceInKiloOhms] at hOtherNear
        linarith
    | D =>
        rw [← hKiloOhmEquality] at hOtherNear
        rw [abs_lt] at hMinimumNear hOtherNear
        norm_num [displayedResistanceInKiloOhms,
          displayedResistanceToleranceInKiloOhms] at hOtherNear
        linarith

end PhyXMiniProblems.ProblemPhyXMini0612
