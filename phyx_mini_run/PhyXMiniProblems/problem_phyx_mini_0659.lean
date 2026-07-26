import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0659

open Dimension

/-!
# Minimum electron speed for the 492 nm mercury line

The supplied figure lists seven mercury energy levels between `0.00 eV` and
`9.53 eV`.  A `492 nm` photon has the energy gap between the `6s8s` level near
`9.22 eV` and the `6s6p` level near `6.70 eV`.  To make that emission possible
from a ground-state atom, an incident electron must nevertheless supply the
full excitation energy from `6s²` at `0.00 eV` to the upper `6s8s` level.

Physical energies, lengths, masses, actions, and speeds are dimensionful
Physlib quantities.  Real numbers occur only at explicitly unit-labelled
readout boundaries, at raster annotations, and in displayed answer choices.
The minimum speed is an independent physical field constrained by general
emission, kinetic-energy, and excitation-threshold laws; no premise assigns it
the recorded numerical answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A signed physical speed, used for the vacuum speed of light. -/
abbrev LightSpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in a selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Coherent-SI readout of a physical energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Electron-volt readout grounded by `DimEnergy.electronVolt`. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a nonnegative physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a signed physical speed such as `c`. -/
def lightSpeedInMetersPerSecond (speed : LightSpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-! ## Mercury levels, the target line, and primary-figure vocabulary -/

/-- Atomic species distinguished by the problem statement. -/
inductive AtomicSpecies where
  | mercury
  | other
  deriving DecidableEq, Repr

/-- Species of the projectile which excites the atom. -/
inductive ProjectileSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/--
The seven configuration-labelled horizontal levels visible in image `659.png`.
The separate `6s7p` and `6s6d` constructors preserve the twofold `8.84 eV`
readout rather than identifying the physical states.
-/
inductive MercuryEnergyLevel where
  | ground6s2
  | level6s6p
  | level6s7s
  | level6s7p
  | level6s6d
  | level6s8s
  | level6s8p
  deriving DecidableEq, Fintype, Repr

/-- Color name assigned to the spectral line in the question. -/
inductive SpectralColor where
  | blue
  | other
  deriving DecidableEq, Repr

/-- Physical quantity represented by the sole plotted axis. -/
inductive FigureAxisQuantity where
  | energy
  | other
  deriving DecidableEq, Repr

/-- Unit printed beside the energy-axis label. -/
inductive FigureEnergyUnit where
  | electronVolt
  | other
  deriving DecidableEq, Repr

/-- Literal qualitative and numerical content visible in the supplied image. -/
structure MercuryEnergyLevelDiagram where
  verticalAxisQuantity : FigureAxisQuantity
  verticalAxisUnit : FigureEnergyUnit
  verticalAxisLabelShown : Bool
  lowestTickElectronVolts : ℝ
  highestTickElectronVolts : ℝ
  integerTickShown : Fin 11 → Bool
  levelIsShown : MercuryEnergyLevel → Bool
  levelIsHorizontal : MercuryEnergyLevel → Bool
  configurationLabelShown : MercuryEnergyLevel → Bool
  printedEnergyElectronVolts : MercuryEnergyLevel → ℝ
  energiesAreInElectronVoltsNoteShown : Bool

/--
The observed blue emission line.  Its endpoints and wavelength are independent
physical data; the governing law below relates them to the level energies.
-/
structure MercuryEmissionLine where
  upperLevel : MercuryEnergyLevel
  lowerLevel : MercuryEnergyLevel
  vacuumWavelength : LengthQuantity
  color : SpectralColor

/--
Independent quantities in the collision-and-emission experiment.  In
particular, neither `minimumIncidentSpeed` nor `thresholdKineticEnergy` is
defined from an answer choice.
-/
structure MercuryExcitationSetup where
  atomSpecies : AtomicSpecies
  projectileSpecies : ProjectileSpecies
  atomInitialLevel : MercuryEnergyLevel
  levelEnergy : MercuryEnergyLevel → DimEnergy
  targetEmissionLine : MercuryEmissionLine
  electronRestMass : MassQuantity
  planckAction : ActionQuantity
  vacuumLightSpeed : LightSpeedQuantity
  minimumIncidentSpeed : DimSpeed
  thresholdKineticEnergy : DimEnergy
  figure : MercuryEnergyLevelDiagram

/-! ## Scenario, source readouts, reference data, and governing laws -/

/-- Agreement with a wavelength printed to the nearest nanometre. -/
def AgreesWithNearestNanometerReadout
    (wavelength : LengthQuantity) (displayedNanometers : ℝ) : Prop :=
  |lengthInNanometers wavelength - displayedNanometers| < (1 / 2 : ℝ)

/-- Agreement with an energy printed to two decimal places in electron volts. -/
def AgreesWithTwoDecimalElectronVoltReadout
    (energy : DimEnergy) (displayedElectronVolts : ℝ) : Prop :=
  |energyInElectronVolts energy - displayedElectronVolts| < (1 / 200 : ℝ)

/-- The prose scenario and the independently supplied `492 nm` blue-line datum. -/
structure MatchesMercuryElectronExcitationScenario
    (setup : MercuryExcitationSetup) : Prop where
  atomIsMercury : setup.atomSpecies = .mercury
  projectileIsElectron : setup.projectileSpecies = .electron
  atomInitiallyInGroundConfiguration : setup.atomInitialLevel = .ground6s2
  targetLineIsBlue : setup.targetEmissionLine.color = .blue
  targetWavelengthReadout :
    AgreesWithNearestNanometerReadout
      setup.targetEmissionLine.vacuumWavelength 492

/--
Primary-image evidence from `659.png`, including both distinct states printed
at `8.84 eV`.  The approximate physical-energy clauses interpret the two-place
labels as measurements and contain no spectral-line endpoint or speed answer.
-/
structure MatchesSuppliedMercuryEnergyLevelDiagram
    (setup : MercuryExcitationSetup) : Prop where
  axisRepresentsEnergy : setup.figure.verticalAxisQuantity = .energy
  axisUsesElectronVolts : setup.figure.verticalAxisUnit = .electronVolt
  axisLabelIsShown : setup.figure.verticalAxisLabelShown = true
  lowestTickIsZero : setup.figure.lowestTickElectronVolts = 0
  highestTickIsTen : setup.figure.highestTickElectronVolts = 10
  everyIntegerTickIsShown : ∀ tick, setup.figure.integerTickShown tick = true
  everyLevelIsShown : ∀ level, setup.figure.levelIsShown level = true
  everyLevelIsHorizontal : ∀ level, setup.figure.levelIsHorizontal level = true
  everyConfigurationLabelIsShown :
    ∀ level, setup.figure.configurationLabelShown level = true
  groundPrintedEnergy :
    setup.figure.printedEnergyElectronVolts .ground6s2 = 0.00
  level6s6pPrintedEnergy :
    setup.figure.printedEnergyElectronVolts .level6s6p = 6.70
  level6s7sPrintedEnergy :
    setup.figure.printedEnergyElectronVolts .level6s7s = 7.92
  level6s7pPrintedEnergy :
    setup.figure.printedEnergyElectronVolts .level6s7p = 8.84
  level6s6dPrintedEnergy :
    setup.figure.printedEnergyElectronVolts .level6s6d = 8.84
  level6s8sPrintedEnergy :
    setup.figure.printedEnergyElectronVolts .level6s8s = 9.22
  level6s8pPrintedEnergy :
    setup.figure.printedEnergyElectronVolts .level6s8p = 9.53
  groundEnergyReadout :
    AgreesWithTwoDecimalElectronVoltReadout
      (setup.levelEnergy .ground6s2) 0.00
  level6s6pEnergyReadout :
    AgreesWithTwoDecimalElectronVoltReadout
      (setup.levelEnergy .level6s6p) 6.70
  level6s7sEnergyReadout :
    AgreesWithTwoDecimalElectronVoltReadout
      (setup.levelEnergy .level6s7s) 7.92
  level6s7pEnergyReadout :
    AgreesWithTwoDecimalElectronVoltReadout
      (setup.levelEnergy .level6s7p) 8.84
  level6s6dEnergyReadout :
    AgreesWithTwoDecimalElectronVoltReadout
      (setup.levelEnergy .level6s6d) 8.84
  level6s8sEnergyReadout :
    AgreesWithTwoDecimalElectronVoltReadout
      (setup.levelEnergy .level6s8s) 9.22
  level6s8pEnergyReadout :
    AgreesWithTwoDecimalElectronVoltReadout
      (setup.levelEnergy .level6s8p) 9.53
  unitsNoteIsShown :
    setup.figure.energiesAreInElectronVoltsNoteShown = true

/-- Standard electron mass, ordinary Planck action, and vacuum light speed. -/
structure UsesStandardElectronAndPhotonReferenceData
    (setup : MercuryExcitationSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.electronRestMass = 9.1093837015e-31
  planckActionJouleSeconds :
    actionInJouleSeconds setup.planckAction =
      2 * Real.pi * (Constants.ℏ : ℝ)
  vacuumLightSpeedCalibration :
    lightSpeedInMetersPerSecond setup.vacuumLightSpeed =
      lightSpeedInMetersPerSecond DimSpeed.speedOfLight

/-- Positivity and nonnegativity conditions selecting the physical branch. -/
structure HasPhysicalMercuryExcitationParameters
    (setup : MercuryExcitationSetup) : Prop where
  positiveElectronMass : 0 < massInKilograms setup.electronRestMass
  positivePlanckAction : 0 < actionInJouleSeconds setup.planckAction
  positiveVacuumLightSpeed :
    0 < lightSpeedInMetersPerSecond setup.vacuumLightSpeed
  positiveTargetWavelength :
    0 < lengthInMeters setup.targetEmissionLine.vacuumWavelength
  positiveMinimumSpeed : 0 < speedInMetersPerSecond setup.minimumIncidentSpeed
  nonnegativeThresholdKineticEnergy :
    0 ≤ energyInJoules setup.thresholdKineticEnergy
  nonnegativeLevelEnergy :
    ∀ level, 0 ≤ energyInJoules (setup.levelEnergy level)

/--
Coherent-SI energy which the collision must supply to reach the target line's
upper level from the atom's initial level.
-/
def targetExcitationEnergyInJoules (setup : MercuryExcitationSetup) : ℝ :=
  energyInJoules
      (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
    energyInJoules (setup.levelEnergy setup.atomInitialLevel)

/--
At a candidate nonnegative scalar speed, the incident electron can supply the
target excitation energy according to nonrelativistic kinetic energy.
-/
def CanExciteTargetLineAtSpeed
    (setup : MercuryExcitationSetup) (candidateMetersPerSecond : ℝ) : Prop :=
  0 ≤ candidateMetersPerSecond ∧
    targetExcitationEnergyInJoules setup ≤
      (1 / 2 : ℝ) * massInKilograms setup.electronRestMass *
        candidateMetersPerSecond ^ 2

/--
General laws used by the problem:

* the emitted photon's energy gap obeys `ΔE λ = h c`;
* the threshold electron has kinetic energy `m v² / 2`;
* energy conservation equates that kinetic energy to the excitation from the
  initial atomic level to the emission line's upper level; and
* the designated threshold speed is the least nonnegative speed capable of
  supplying that excitation energy.

No clause identifies the `492 nm` line's endpoint, assigns a numerical speed,
or selects an answer choice.
-/
structure SatisfiesMercuryEmissionAndThresholdLaws
    (setup : MercuryExcitationSetup) : Prop where
  emissionIsDownward :
    energyInJoules
        (setup.levelEnergy setup.targetEmissionLine.lowerLevel) <
      energyInJoules
        (setup.levelEnergy setup.targetEmissionLine.upperLevel)
  photonEnergyWavelengthRelation :
    (energyInJoules
          (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
        energyInJoules
          (setup.levelEnergy setup.targetEmissionLine.lowerLevel)) *
        lengthInMeters setup.targetEmissionLine.vacuumWavelength =
      actionInJouleSeconds setup.planckAction *
        lightSpeedInMetersPerSecond setup.vacuumLightSpeed
  nonrelativisticThresholdKineticEnergy :
    energyInJoules setup.thresholdKineticEnergy =
      (1 / 2 : ℝ) * massInKilograms setup.electronRestMass *
        speedInMetersPerSecond setup.minimumIncidentSpeed ^ 2
  thresholdEnergyConservation :
    energyInJoules setup.thresholdKineticEnergy =
      targetExcitationEnergyInJoules setup
  minimumSpeedCharacterization :
    IsLeast
      {candidateMetersPerSecond : ℝ |
        CanExciteTargetLineAtSpeed setup candidateMetersPerSecond}
      (speedInMetersPerSecond setup.minimumIncidentSpeed)

/-! ## Derived transition identification and displayed-answer semantics -/

/--
The only downward pair in the supplied list compatible with the rounded
`492 nm` wavelength is the `6s8s → 6s6p` transition.  This is a derived
conclusion, not a figure premise.
-/
lemma blue492nmLine_is_level6s8s_to_level6s6p
    (setup : MercuryExcitationSetup)
    (_scenario : MatchesMercuryElectronExcitationScenario setup)
    (_figure : MatchesSuppliedMercuryEnergyLevelDiagram setup)
    (_references : UsesStandardElectronAndPhotonReferenceData setup)
    (_physical : HasPhysicalMercuryExcitationParameters setup)
    (_laws : SatisfiesMercuryEmissionAndThresholdLaws setup) :
    setup.targetEmissionLine.upperLevel = .level6s8s ∧
      setup.targetEmissionLine.lowerLevel = .level6s6p := by
  have h_electron_volt :
      energyInJoules DimEnergy.electronVolt = (1.602176634e-19 : ℝ) := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have h_electron_volt_pos :
      0 < energyInJoules DimEnergy.electronVolt := by
    rw [h_electron_volt]
    norm_num
  have h_energy_from_readout (level : MercuryEnergyLevel) :
      energyInJoules (setup.levelEnergy level) =
        energyInElectronVolts (setup.levelEnergy level) *
          energyInJoules DimEnergy.electronVolt := by
    rw [energyInElectronVolts]
    field_simp
  have h_wavelength_conversion (wavelength : LengthQuantity) :
      lengthInMeters wavelength =
        lengthInNanometers wavelength * (10 : ℝ) ^ (-9 : ℤ) := by
    have h_change_units := wavelength.property
      ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
    have h_values :=
      congrArg (fun value => ((value.val : NNReal) : ℝ)) h_change_units
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul,
      WithDim.dim_apply] at h_values
    have h_scale :
        ((({UnitChoices.SI with length := LengthUnit.nanometers} :
              UnitChoices).dimScale
            ({UnitChoices.SI with length := LengthUnit.meters} :
              UnitChoices) L𝓭 : NNReal) : ℝ) =
          (10 : ℝ) ^ (-9 : ℤ) := by
      norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
        NNReal.toReal, Real.rpow_zero, Real.rpow_one]
    simp only [lengthInMeters, lengthInNanometers, lengthReadout]
    rw [h_values, h_scale]
    ring
  have h_wavelength_bounds := _scenario.targetWavelengthReadout
  simp only [AgreesWithNearestNanometerReadout, abs_lt] at h_wavelength_bounds
  let nominalEnergy : MercuryEnergyLevel → ℝ
    | .ground6s2 => 0.00
    | .level6s6p => 6.70
    | .level6s7s => 7.92
    | .level6s7p => 8.84
    | .level6s6d => 8.84
    | .level6s8s => 9.22
    | .level6s8p => 9.53
  have h_readout_close (level : MercuryEnergyLevel) :
      |energyInElectronVolts (setup.levelEnergy level) -
        nominalEnergy level| < (1 / 200 : ℝ) := by
    cases level with
    | ground6s2 =>
        simpa [AgreesWithTwoDecimalElectronVoltReadout, nominalEnergy] using
          _figure.groundEnergyReadout
    | level6s6p =>
        simpa [AgreesWithTwoDecimalElectronVoltReadout, nominalEnergy] using
          _figure.level6s6pEnergyReadout
    | level6s7s =>
        simpa [AgreesWithTwoDecimalElectronVoltReadout, nominalEnergy] using
          _figure.level6s7sEnergyReadout
    | level6s7p =>
        simpa [AgreesWithTwoDecimalElectronVoltReadout, nominalEnergy] using
          _figure.level6s7pEnergyReadout
    | level6s6d =>
        simpa [AgreesWithTwoDecimalElectronVoltReadout, nominalEnergy] using
          _figure.level6s6dEnergyReadout
    | level6s8s =>
        simpa [AgreesWithTwoDecimalElectronVoltReadout, nominalEnergy] using
          _figure.level6s8sEnergyReadout
    | level6s8p =>
        simpa [AgreesWithTwoDecimalElectronVoltReadout, nominalEnergy] using
          _figure.level6s8pEnergyReadout
  have h_line_law := _laws.photonEnergyWavelengthRelation
  rw [h_energy_from_readout, h_energy_from_readout,
    h_wavelength_conversion, _references.planckActionJouleSeconds,
    _references.vacuumLightSpeedCalibration] at h_line_law
  have h_scale_ne :
      energyInJoules DimEnergy.electronVolt * (10 : ℝ) ^ (-9 : ℤ) ≠ 0 := by
    positivity
  have h_line_scaled :
      (energyInElectronVolts
              (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
            energyInElectronVolts
              (setup.levelEnergy setup.targetEmissionLine.lowerLevel)) *
          lengthInNanometers setup.targetEmissionLine.vacuumWavelength =
        (2 * Real.pi * (Constants.ℏ : ℝ) *
            lightSpeedInMetersPerSecond DimSpeed.speedOfLight) /
          (energyInJoules DimEnergy.electronVolt *
            (10 : ℝ) ^ (-9 : ℤ)) := by
    apply (eq_div_iff h_scale_ne).2
    calc
      _ =
          (energyInElectronVolts
                  (setup.levelEnergy setup.targetEmissionLine.upperLevel) *
                energyInJoules DimEnergy.electronVolt -
              energyInElectronVolts
                  (setup.levelEnergy setup.targetEmissionLine.lowerLevel) *
                energyInJoules DimEnergy.electronVolt) *
            (lengthInNanometers
                setup.targetEmissionLine.vacuumWavelength *
              (10 : ℝ) ^ (-9 : ℤ)) := by ring
      _ =
          2 * Real.pi * (Constants.ℏ : ℝ) *
            lightSpeedInMetersPerSecond DimSpeed.speedOfLight := h_line_law
  set_option maxHeartbeats 1000000 in
    norm_num [Constants.ℏ, lightSpeedInMetersPerSecond, h_electron_volt] at h_line_scaled
  have h_downward := _laws.emissionIsDownward
  rw [h_energy_from_readout, h_energy_from_readout, h_electron_volt] at h_downward
  have h_downward_readout :
      energyInElectronVolts
          (setup.levelEnergy setup.targetEmissionLine.lowerLevel) <
        energyInElectronVolts
          (setup.levelEnergy setup.targetEmissionLine.upperLevel) := by
    nlinarith only [h_downward, h_electron_volt_pos]
  have h_wavelength_pos :
      0 < lengthInNanometers setup.targetEmissionLine.vacuumWavelength := by
    linarith only [h_wavelength_bounds.1]
  have h_wavelength_upper :
      lengthInNanometers setup.targetEmissionLine.vacuumWavelength <
        (492.5 : ℝ) := by
    linarith only [h_wavelength_bounds.2]
  have h_wavelength_lower :
      (491.5 : ℝ) <
        lengthInNanometers setup.targetEmissionLine.vacuumWavelength := by
    linarith only [h_wavelength_bounds.1]
  have h_gap_pos :
      0 <
        energyInElectronVolts
            (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
          energyInElectronVolts
            (setup.levelEnergy setup.targetEmissionLine.lowerLevel) := by
    linarith only [h_downward_readout]
  have h_gap_lower :
      (2.51 : ℝ) <
        energyInElectronVolts
            (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
          energyInElectronVolts
            (setup.levelEnergy setup.targetEmissionLine.lowerLevel) := by
    by_contra h_not
    have h_gap_le :
        energyInElectronVolts
              (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
            energyInElectronVolts
              (setup.levelEnergy setup.targetEmissionLine.lowerLevel) ≤
          (2.51 : ℝ) := le_of_not_gt h_not
    have h_product_lt :
        (energyInElectronVolts
                (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
              energyInElectronVolts
                (setup.levelEnergy setup.targetEmissionLine.lowerLevel)) *
            lengthInNanometers setup.targetEmissionLine.vacuumWavelength <
          (2.51 : ℝ) * 492.5 := by
      calc
        _ <
            (energyInElectronVolts
                  (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
                energyInElectronVolts
                  (setup.levelEnergy setup.targetEmissionLine.lowerLevel)) *
              492.5 :=
          mul_lt_mul_of_pos_left h_wavelength_upper h_gap_pos
        _ ≤ (2.51 : ℝ) * 492.5 := by
          exact mul_le_mul_of_nonneg_right h_gap_le (by norm_num)
    rw [h_line_scaled] at h_product_lt
    linarith only [h_product_lt, Real.pi_gt_d20]
  have h_gap_upper :
      energyInElectronVolts
            (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
          energyInElectronVolts
            (setup.levelEnergy setup.targetEmissionLine.lowerLevel) <
        (2.53 : ℝ) := by
    by_contra h_not
    have h_gap_ge :
        (2.53 : ℝ) ≤
          energyInElectronVolts
              (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
            energyInElectronVolts
              (setup.levelEnergy setup.targetEmissionLine.lowerLevel) :=
      le_of_not_gt h_not
    have h_product_gt :
        (2.53 : ℝ) * 491.5 <
          (energyInElectronVolts
                (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
              energyInElectronVolts
                (setup.levelEnergy setup.targetEmissionLine.lowerLevel)) *
            lengthInNanometers setup.targetEmissionLine.vacuumWavelength := by
      calc
        (2.53 : ℝ) * 491.5 <
            (2.53 : ℝ) *
              lengthInNanometers setup.targetEmissionLine.vacuumWavelength :=
          mul_lt_mul_of_pos_left h_wavelength_lower (by norm_num)
        _ ≤
            (energyInElectronVolts
                  (setup.levelEnergy setup.targetEmissionLine.upperLevel) -
                energyInElectronVolts
                  (setup.levelEnergy setup.targetEmissionLine.lowerLevel)) *
              lengthInNanometers setup.targetEmissionLine.vacuumWavelength := by
          exact mul_le_mul_of_nonneg_right h_gap_ge
            (le_of_lt h_wavelength_pos)
    rw [h_line_scaled] at h_product_gt
    linarith only [h_product_gt, Real.pi_lt_d20]
  have h_upper_close :=
    (abs_lt.mp (h_readout_close setup.targetEmissionLine.upperLevel))
  have h_lower_close :=
    (abs_lt.mp (h_readout_close setup.targetEmissionLine.lowerLevel))
  have h_nominal_gap_lower :
      (2.50 : ℝ) <
        nominalEnergy setup.targetEmissionLine.upperLevel -
          nominalEnergy setup.targetEmissionLine.lowerLevel := by
    linarith only [h_gap_lower, h_upper_close.2, h_lower_close.1]
  have h_nominal_gap_upper :
      nominalEnergy setup.targetEmissionLine.upperLevel -
          nominalEnergy setup.targetEmissionLine.lowerLevel <
        (2.54 : ℝ) := by
    linarith only [h_gap_upper, h_upper_close.1, h_lower_close.2]
  have h_unique_nominal_pair (upper lower : MercuryEnergyLevel)
      (h_lower :
        (2.50 : ℝ) < nominalEnergy upper - nominalEnergy lower)
      (h_upper :
        nominalEnergy upper - nominalEnergy lower < (2.54 : ℝ)) :
      upper = .level6s8s ∧ lower = .level6s6p := by
    cases upper <;> cases lower
    all_goals
      solve
      | exact ⟨rfl, rfl⟩
      | exfalso
        norm_num [nominalEnergy] at h_lower
      | exfalso
        norm_num [nominalEnergy] at h_upper
  exact h_unique_nominal_pair _ _ h_nominal_gap_lower h_nominal_gap_upper

/--
Once the line is identified, threshold energy conservation uses the full
ground-to-`6s8s` excitation gap, not merely the emitted `6s8s → 6s6p` gap.
-/
lemma thresholdEnergy_is_ground6s2_to_level6s8s
    (setup : MercuryExcitationSetup)
    (_scenario : MatchesMercuryElectronExcitationScenario setup)
    (_figure : MatchesSuppliedMercuryEnergyLevelDiagram setup)
    (_references : UsesStandardElectronAndPhotonReferenceData setup)
    (_physical : HasPhysicalMercuryExcitationParameters setup)
    (_laws : SatisfiesMercuryEmissionAndThresholdLaws setup) :
    energyInJoules setup.thresholdKineticEnergy =
      energyInJoules (setup.levelEnergy .level6s8s) -
        energyInJoules (setup.levelEnergy .ground6s2) := by
  have h_transition :=
    blue492nmLine_is_level6s8s_to_level6s6p setup _scenario _figure
      _references _physical _laws
  rw [_laws.thresholdEnergyConservation]
  unfold targetExcitationEnergyInJoules
  rw [h_transition.1, _scenario.atomInitiallyInGroundConfiguration]

/-- Labels of the four speed choices supplied with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed answer speed in metres per second. -/
def AnswerChoice.speedMetersPerSecond : AnswerChoice → ℝ
  | .A => 1.40 * 10 ^ (6 : ℕ)
  | .B => 1.60 * 10 ^ (6 : ℕ)
  | .C => 1.80 * 10 ^ (6 : ℕ)
  | .D => 2.0 * 10 ^ (6 : ℕ)

/-- Dataset metadata recording answer C; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Absolute error between the modeled minimum speed and one displayed choice. -/
def answerChoiceErrorMetersPerSecond
    (setup : MercuryExcitationSetup) (choice : AnswerChoice) : ℝ :=
  |speedInMetersPerSecond setup.minimumIncidentSpeed -
    choice.speedMetersPerSecond|

/--
Agreement with a speed whose coefficient is displayed to the nearest
hundredth in units of `10^6 m/s`; half a display unit is `5 × 10^3 m/s`.
-/
def AgreesWithDisplayedMinimumSpeed
    (setup : MercuryExcitationSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorMetersPerSecond setup choice < 5 * 10 ^ (3 : ℕ)

/-- A choice is strictly closer to the modeled threshold speed than all others. -/
def IsUniqueClosestMinimumSpeedChoice
    (setup : MercuryExcitationSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMetersPerSecond setup choice <
      answerChoiceErrorMetersPerSecond setup other

/--
The minimum incident-electron speed rounds to `1.80 × 10^6 m/s`, so answer C
is also the unique closest displayed choice.

This is the formalization target corresponding to
`thm:physics:phyx_mini_0659:target`.
-/
theorem minimumElectronSpeed_for_492nmMercuryEmission
    (setup : MercuryExcitationSetup)
    (_scenario : MatchesMercuryElectronExcitationScenario setup)
    (_figure : MatchesSuppliedMercuryEnergyLevelDiagram setup)
    (_references : UsesStandardElectronAndPhotonReferenceData setup)
    (_physical : HasPhysicalMercuryExcitationParameters setup)
    (_laws : SatisfiesMercuryEmissionAndThresholdLaws setup) :
    AgreesWithDisplayedMinimumSpeed setup .C ∧
      IsUniqueClosestMinimumSpeedChoice setup .C := by
  have h_electron_volt :
      energyInJoules DimEnergy.electronVolt = (1.602176634e-19 : ℝ) := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have h_electron_volt_pos :
      0 < energyInJoules DimEnergy.electronVolt := by
    rw [h_electron_volt]
    norm_num
  have h_energy_from_readout (level : MercuryEnergyLevel) :
      energyInJoules (setup.levelEnergy level) =
        energyInElectronVolts (setup.levelEnergy level) *
          energyInJoules DimEnergy.electronVolt := by
    rw [energyInElectronVolts]
    field_simp
  have h_upper_readout := _figure.level6s8sEnergyReadout
  have h_ground_readout := _figure.groundEnergyReadout
  simp only [AgreesWithTwoDecimalElectronVoltReadout, abs_lt] at h_upper_readout
  simp only [AgreesWithTwoDecimalElectronVoltReadout, abs_lt] at h_ground_readout
  have h_upper_energy_lower :
      (9.215 : ℝ) * energyInJoules DimEnergy.electronVolt <
        energyInJoules (setup.levelEnergy .level6s8s) := by
    rw [h_energy_from_readout, h_electron_volt]
    nlinarith only [h_upper_readout.1]
  have h_upper_energy_upper :
      energyInJoules (setup.levelEnergy .level6s8s) <
        (9.225 : ℝ) * energyInJoules DimEnergy.electronVolt := by
    rw [h_energy_from_readout, h_electron_volt]
    nlinarith only [h_upper_readout.2]
  have h_ground_energy_upper :
      energyInJoules (setup.levelEnergy .ground6s2) <
        (0.005 : ℝ) * energyInJoules DimEnergy.electronVolt := by
    rw [h_energy_from_readout, h_electron_volt]
    nlinarith only [h_ground_readout.2]
  have h_ground_energy_nonnegative :
      0 ≤ energyInJoules (setup.levelEnergy .ground6s2) :=
    _physical.nonnegativeLevelEnergy .ground6s2
  have h_threshold :=
    thresholdEnergy_is_ground6s2_to_level6s8s setup _scenario _figure
      _references _physical _laws
  have h_threshold_lower :
      (9.21 : ℝ) * energyInJoules DimEnergy.electronVolt <
        energyInJoules setup.thresholdKineticEnergy := by
    linarith only [h_threshold, h_upper_energy_lower,
      h_ground_energy_upper]
  have h_threshold_upper :
      energyInJoules setup.thresholdKineticEnergy <
        (9.225 : ℝ) * energyInJoules DimEnergy.electronVolt := by
    linarith only [h_threshold, h_upper_energy_upper,
      h_ground_energy_nonnegative]
  let v : ℝ := speedInMetersPerSecond setup.minimumIncidentSpeed
  have h_v_pos : 0 < v := by
    exact _physical.positiveMinimumSpeed
  have h_kinetic := _laws.nonrelativisticThresholdKineticEnergy
  rw [_references.electronMassKilograms] at h_kinetic
  change energyInJoules setup.thresholdKineticEnergy =
    (1 / 2 : ℝ) * 9.1093837015e-31 * v ^ 2 at h_kinetic
  have h_v_lower : (1795000 : ℝ) < v := by
    by_contra h_not
    have h_v_le : v ≤ (1795000 : ℝ) := le_of_not_gt h_not
    have h_v_sq_le : v ^ 2 ≤ (1795000 : ℝ) ^ 2 :=
      (sq_le_sq₀ (le_of_lt h_v_pos) (by norm_num)).2 h_v_le
    nlinarith only [h_kinetic, h_threshold_lower, h_v_sq_le,
      h_electron_volt]
  have h_v_upper : v < (1805000 : ℝ) := by
    by_contra h_not
    have h_v_ge : (1805000 : ℝ) ≤ v := le_of_not_gt h_not
    have h_v_sq_ge : (1805000 : ℝ) ^ 2 ≤ v ^ 2 :=
      (sq_le_sq₀ (by norm_num) (le_of_lt h_v_pos)).2 h_v_ge
    nlinarith only [h_kinetic, h_threshold_upper, h_v_sq_ge,
      h_electron_volt]
  have h_c_error : |v - (1800000 : ℝ)| < (5000 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith only [h_v_lower, h_v_upper]
  constructor
  · norm_num [AgreesWithDisplayedMinimumSpeed,
      answerChoiceErrorMetersPerSecond, AnswerChoice.speedMetersPerSecond]
    change |v - (1800000 : ℝ)| < (5000 : ℝ)
    exact h_c_error
  · intro other h_other
    cases other with
    | A =>
        norm_num [answerChoiceErrorMetersPerSecond,
          AnswerChoice.speedMetersPerSecond]
        change |v - (1800000 : ℝ)| < |v - (1400000 : ℝ)|
        have h_a_nonnegative : 0 ≤ v - (1400000 : ℝ) := by
          linarith only [h_v_lower]
        rw [abs_of_nonneg h_a_nonnegative]
        linarith only [h_c_error, h_v_lower]
    | B =>
        norm_num [answerChoiceErrorMetersPerSecond,
          AnswerChoice.speedMetersPerSecond]
        change |v - (1800000 : ℝ)| < |v - (1600000 : ℝ)|
        have h_b_nonnegative : 0 ≤ v - (1600000 : ℝ) := by
          linarith only [h_v_lower]
        rw [abs_of_nonneg h_b_nonnegative]
        linarith only [h_c_error, h_v_lower]
    | C =>
        exact (h_other rfl).elim
    | D =>
        norm_num [answerChoiceErrorMetersPerSecond,
          AnswerChoice.speedMetersPerSecond]
        change |v - (1800000 : ℝ)| < |v - (2000000 : ℝ)|
        have h_d_nonpositive : v - (2000000 : ℝ) ≤ 0 := by
          linarith only [h_v_upper]
        rw [abs_of_nonpos h_d_nonpositive]
        linarith only [h_c_error, h_v_upper]

end PhyXMiniProblems.ProblemPhyXMini0659
