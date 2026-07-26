import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0458

open Dimension

/-!
# Air equilibrating across a conducting movable piston

An insulated cylinder initially contains two `1 m³` air compartments separated
by a locked piston.  Compartment `A` starts at `200 kPa` and `300 K`, while
compartment `B` starts at `1 MPa` and `1000 K`.  The piston is then unlocked;
its motion and heat conduction produce common final pressure and temperature.

The source records answer `613 kPa`, but supplies neither a caloric equation for
air nor the ideal-air table needed to determine the common final temperature.
Consequently the formal target below gives the strongest source-supported
characterization: `P_f = (5/6) T_f`, together with the isolated-system energy
equation.  It also states that the recorded pressure is obtained exactly when
the missing caloric model gives `T_f = 735.6 K`.  The recorded answer remains
metadata rather than a premise.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- Physical volume, carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Physical mass of one trapped air sample. -/
abbrev AirMassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- Mass-specific internal energy, carrying dimension `L² T⁻²`. -/
abbrev SpecificInternalEnergyQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/--
The mass-specific gas constant, with dimension `L² T⁻² Θ⁻¹`, or energy per
unit mass per absolute temperature.
-/
abbrev SpecificGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical mass in coherent SI kilograms. -/
def airMassInKilograms (mass : AirMassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/--
Read an absolute temperature in kelvins.  Physlib temperatures store a value
relative to an explicit zero-preserving temperature unit.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read specific internal energy in kilojoules per kilogram. -/
def specificInternalEnergyInKilojoulesPerKilogram
    (energy : SpecificInternalEnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val / 1000

/-- Read the specific gas constant in kilojoules per kilogram-kelvin. -/
def specificGasConstantInKilojoulesPerKilogramKelvin
    (gasConstant : SpecificGasConstantQuantity) : ℝ :=
  ((gasConstant UnitChoices.SI).val : ℝ) / 1000

/-! ## Apparatus, thermodynamic states, and figure labels -/

/-- The compartment labels visible in the supplied figure. -/
inductive Compartment where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The stages before and after releasing the piston. -/
inductive ProcessStage where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- The gas named in each compartment. -/
inductive GasSpecies where
  | air
  | other
  deriving DecidableEq, Repr

/-- Whether piston translation along the cylinder is constrained. -/
inductive PistonConstraint where
  | locked
  | freeToMove
  deriving DecidableEq, Repr

/-- Individually identifiable objects in the supplied raster. -/
inductive FigureObject where
  | outerCylinder
  | compartmentA
  | compartmentB
  | separatingPiston
  | pistonRodAndHandle
  | exteriorHatching
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative information read from the primary image.  These fields encode only
visible topology, orientation, labels, and colour; no numerical answer occurs
in the raster.
-/
structure SuppliedTwoCompartmentCylinderFigure where
  showsObject : FigureObject → Bool
  showsCompartmentLabel : Compartment → Bool
  showsAirText : Compartment → Bool
  compartmentAIsLeftOfB : Bool
  pistonIsBetweenCompartments : Bool
  pistonIsVertical : Bool
  cylinderLongAxisIsHorizontal : Bool
  initialCompartmentsHaveEqualDrawnWidth : Bool
  bothAirRegionsAreLightBlue : Bool

/-- One equilibrium state of the trapped gas on one side of the piston. -/
structure CompartmentAirState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  airMass : AirMassQuantity

/-!
An abstract caloric model for ideal air.  The source does not supply its table
entries or a closed formula, so the temperature-to-internal-energy relation is
kept abstract rather than calibrated to the recorded answer.
-/
structure IdealAirCaloricModel where
  specificInternalEnergyAt :
    Temperature → SpecificInternalEnergyQuantity

/-- The two-compartment experiment and its independently stored observables. -/
structure ConductingPistonCylinderSetup where
  figure : SuppliedTwoCompartmentCylinderFigure
  gasSpeciesAt : Compartment → GasSpecies
  stateAt : ProcessStage → Compartment → CompartmentAirState
  airCaloricModel : IdealAirCaloricModel
  specificGasConstant : SpecificGasConstantQuantity
  temperatureStorageUnit : TemperatureUnit
  pistonConstraintAt : ProcessStage → PistonConstraint
  outerCylinderIsInsulated : Bool
  pistonConductsHeat : Bool

/-- The common final pressure, named using the left compartment readout. -/
def finalPressure (setup : ConductingPistonCylinderSetup) : DimPressure :=
  (setup.stateAt .final .A).pressure

/-- The requested final-pressure readout in kilopascals. -/
def finalPressureInKilopascals
    (setup : ConductingPistonCylinderSetup) : ℝ :=
  pressureInKilopascals (finalPressure setup)

/-- The final-temperature readout in kelvins, named using compartment `A`. -/
def finalTemperatureInKelvins
    (setup : ConductingPistonCylinderSetup) : ℝ :=
  temperatureInKelvins setup.temperatureStorageUnit
    (setup.stateAt .final .A).temperature

/-- The ideal-air table readout at one state's temperature. -/
def stateSpecificInternalEnergyInKilojoulesPerKilogram
    (setup : ConductingPistonCylinderSetup)
    (stage : ProcessStage) (side : Compartment) : ℝ :=
  specificInternalEnergyInKilojoulesPerKilogram
    (setup.airCaloricModel.specificInternalEnergyAt
      (setup.stateAt stage side).temperature)

/-! ## Primary-image evidence and source data -/

/-- Exact qualitative topology and labels visible in the supplied raster. -/
structure MatchesSuppliedCylinderFigure
    (setup : ConductingPistonCylinderSetup) : Prop where
  everyObjectIsShown :
    ∀ object, setup.figure.showsObject object = true
  bothCompartmentLabelsAreShown :
    ∀ side, setup.figure.showsCompartmentLabel side = true
  bothAirLabelsAreShown :
    ∀ side, setup.figure.showsAirText side = true
  compartmentAIsOnTheLeft :
    setup.figure.compartmentAIsLeftOfB = true
  pistonSeparatesTheCompartments :
    setup.figure.pistonIsBetweenCompartments = true
  separatingPistonIsVertical :
    setup.figure.pistonIsVertical = true
  cylinderIsDrawnHorizontally :
    setup.figure.cylinderLongAxisIsHorizontal = true
  compartmentsAreInitiallyDrawnEqual :
    setup.figure.initialCompartmentsHaveEqualDrawnWidth = true
  airRegionsAreLightBlue :
    setup.figure.bothAirRegionsAreLightBlue = true

/-!
Numerical readouts and apparatus facts stated in the problem.  No final
pressure, final temperature, air-table entry, or answer label is a field.
-/
structure MatchesProblemData
    (setup : ConductingPistonCylinderSetup) : Prop where
  bothCompartmentsContainAir :
    ∀ side, setup.gasSpeciesAt side = .air
  temperatureScaleIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  initialVolumeAIsOneCubicMeter :
    volumeInCubicMeters (setup.stateAt .initial .A).volume = 1
  initialVolumeBIsOneCubicMeter :
    volumeInCubicMeters (setup.stateAt .initial .B).volume = 1
  initialPressureAIs200Kilopascals :
    pressureInKilopascals (setup.stateAt .initial .A).pressure = 200
  initialTemperatureAIs300Kelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.stateAt .initial .A).temperature = 300
  initialPressureBIsOneMegapascal :
    pressureInKilopascals (setup.stateAt .initial .B).pressure = 1000
  initialTemperatureBIs1000Kelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.stateAt .initial .B).temperature = 1000
  pistonIsInitiallyLocked :
    setup.pistonConstraintAt .initial = .locked
  pistonIsUnlockedAndFreeToMove :
    setup.pistonConstraintAt .final = .freeToMove
  cylinderIsInsulated :
    setup.outerCylinderIsInsulated = true
  pistonIsHeatConducting :
    setup.pistonConductsHeat = true

/-! ## Physical branch and governing laws -/

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalParameters
    (setup : ConductingPistonCylinderSetup) : Prop where
  pressurePositive :
    ∀ stage side,
      0 < pressureInKilopascals (setup.stateAt stage side).pressure
  volumePositive :
    ∀ stage side,
      0 < volumeInCubicMeters (setup.stateAt stage side).volume
  absoluteTemperaturePositive :
    ∀ stage side,
      0 < temperatureInKelvins setup.temperatureStorageUnit
        (setup.stateAt stage side).temperature
  airMassPositive :
    ∀ stage side,
      0 < airMassInKilograms (setup.stateAt stage side).airMass
  specificGasConstantPositive :
    0 < specificGasConstantInKilojoulesPerKilogramKelvin
      setup.specificGasConstant

/-!
Macroscopic governing physics for the two trapped air samples:

* every state obeys the mass-specific ideal-gas equation `PV = mRT`;
* the piston preserves the mass of each trapped sample;
* the cylinder preserves total volume;
* insulation preserves the total internal energy of the two air samples;
* a free conducting piston gives final mechanical and thermal equilibrium.

These laws contain no solved pressure, final temperature, air-table
calibration, or answer-choice value.
-/
structure SatisfiesConductingPistonIdealAirLaws
    (setup : ConductingPistonCylinderSetup) : Prop where
  idealGasEquation :
    ∀ stage side,
      pressureInKilopascals (setup.stateAt stage side).pressure *
          volumeInCubicMeters (setup.stateAt stage side).volume =
        airMassInKilograms (setup.stateAt stage side).airMass *
          specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant *
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.stateAt stage side).temperature
  eachCompartmentMassIsConserved :
    ∀ side,
      (setup.stateAt .final side).airMass =
        (setup.stateAt .initial side).airMass
  cylinderPreservesTotalVolume :
    volumeInCubicMeters (setup.stateAt .final .A).volume +
        volumeInCubicMeters (setup.stateAt .final .B).volume =
      volumeInCubicMeters (setup.stateAt .initial .A).volume +
        volumeInCubicMeters (setup.stateAt .initial .B).volume
  insulatedCylinderPreservesTotalAirInternalEnergy :
    airMassInKilograms (setup.stateAt .final .A).airMass *
          stateSpecificInternalEnergyInKilojoulesPerKilogram setup .final .A +
        airMassInKilograms (setup.stateAt .final .B).airMass *
          stateSpecificInternalEnergyInKilojoulesPerKilogram setup .final .B =
      airMassInKilograms (setup.stateAt .initial .A).airMass *
          stateSpecificInternalEnergyInKilojoulesPerKilogram setup .initial .A +
        airMassInKilograms (setup.stateAt .initial .B).airMass *
          stateSpecificInternalEnergyInKilojoulesPerKilogram setup .initial .B
  freePistonGivesFinalMechanicalEquilibrium :
    pressureInKilopascals (setup.stateAt .final .A).pressure =
      pressureInKilopascals (setup.stateAt .final .B).pressure
  conductingPistonGivesFinalThermalEquilibrium :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.stateAt .final .A).temperature =
      temperatureInKelvins setup.temperatureStorageUnit
        (setup.stateAt .final .B).temperature

/-! ## Displayed answers and the source-supported target -/

/-- The four answer labels printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The pressure displayed by each choice, in kilopascals. -/
def displayedPressureInKilopascals : AnswerChoice → ℝ
  | .A => 400
  | .B => 1000
  | .C => 500
  | .D => 613

/-- Dataset metadata recording the supplied answer label; never a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The source-supported laws determine the final pressure from the still-unknown
common final temperature and constrain that temperature by the ideal-air
caloric model.  In particular, the displayed `613 kPa` value is equivalent to
the missing caloric model selecting `735.6 K`; it is not asserted outright.

Blueprint label: `thm:physics:phyx_mini_0458:target`.
-/
theorem finalPressureAndEnergyCharacterization
    (setup : ConductingPistonCylinderSetup)
    (_figure : MatchesSuppliedCylinderFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesConductingPistonIdealAirLaws setup) :
    finalPressureInKilopascals setup =
        (5 : ℝ) / 6 * finalTemperatureInKelvins setup ∧
      5 * stateSpecificInternalEnergyInKilojoulesPerKilogram
          setup .final .A =
        2 * stateSpecificInternalEnergyInKilojoulesPerKilogram
            setup .initial .A +
          3 * stateSpecificInternalEnergyInKilojoulesPerKilogram
            setup .initial .B ∧
      (finalPressureInKilopascals setup =
          displayedPressureInKilopascals .D ↔
        finalTemperatureInKelvins setup = 3678 / 5) := by
  have hMassA :=
    congrArg airMassInKilograms
      (_laws.eachCompartmentMassIsConserved Compartment.A)
  have hMassB :=
    congrArg airMassInKilograms
      (_laws.eachCompartmentMassIsConserved Compartment.B)
  have hInitialIdealA :=
    _laws.idealGasEquation ProcessStage.initial Compartment.A
  have hInitialIdealB :=
    _laws.idealGasEquation ProcessStage.initial Compartment.B
  rw [_data.initialPressureAIs200Kilopascals,
    _data.initialVolumeAIsOneCubicMeter,
    _data.initialTemperatureAIs300Kelvins] at hInitialIdealA
  rw [_data.initialPressureBIsOneMegapascal,
    _data.initialVolumeBIsOneCubicMeter,
    _data.initialTemperatureBIs1000Kelvins] at hInitialIdealB
  have hMassGasA :
      airMassInKilograms (setup.stateAt .initial .A).airMass *
          specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant =
        (2 : ℝ) / 3 := by
    nlinarith [hInitialIdealA]
  have hMassGasB :
      airMassInKilograms (setup.stateAt .initial .B).airMass *
          specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant =
        1 := by
    nlinarith [hInitialIdealB]
  have hFinalIdealA :=
    _laws.idealGasEquation ProcessStage.final Compartment.A
  have hFinalIdealB :=
    _laws.idealGasEquation ProcessStage.final Compartment.B
  rw [hMassA, hMassGasA] at hFinalIdealA
  rw [hMassB, hMassGasB] at hFinalIdealB
  have hFinalVolume := _laws.cylinderPreservesTotalVolume
  rw [_data.initialVolumeAIsOneCubicMeter,
    _data.initialVolumeBIsOneCubicMeter] at hFinalVolume
  have hPressureSum :
      finalPressureInKilopascals setup *
          (volumeInCubicMeters (setup.stateAt .final .A).volume +
            volumeInCubicMeters (setup.stateAt .final .B).volume) =
        (5 : ℝ) / 3 * finalTemperatureInKelvins setup := by
    calc
      finalPressureInKilopascals setup *
            (volumeInCubicMeters (setup.stateAt .final .A).volume +
              volumeInCubicMeters (setup.stateAt .final .B).volume) =
          pressureInKilopascals (setup.stateAt .final .A).pressure *
              volumeInCubicMeters (setup.stateAt .final .A).volume +
            pressureInKilopascals (setup.stateAt .final .A).pressure *
              volumeInCubicMeters (setup.stateAt .final .B).volume := by
                rw [show finalPressureInKilopascals setup =
                  pressureInKilopascals
                    (setup.stateAt .final .A).pressure from rfl]
                ring
      _ =
          (2 : ℝ) / 3 *
              temperatureInKelvins setup.temperatureStorageUnit
                (setup.stateAt .final .A).temperature +
            pressureInKilopascals (setup.stateAt .final .B).pressure *
              volumeInCubicMeters (setup.stateAt .final .B).volume := by
                rw [hFinalIdealA,
                  _laws.freePistonGivesFinalMechanicalEquilibrium]
      _ =
          (2 : ℝ) / 3 *
              temperatureInKelvins setup.temperatureStorageUnit
                (setup.stateAt .final .A).temperature +
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.stateAt .final .B).temperature := by
                rw [hFinalIdealB]
                ring
      _ = (5 : ℝ) / 3 * finalTemperatureInKelvins setup := by
        rw [← _laws.conductingPistonGivesFinalThermalEquilibrium]
        change (2 : ℝ) / 3 * finalTemperatureInKelvins setup +
            finalTemperatureInKelvins setup =
          (5 : ℝ) / 3 * finalTemperatureInKelvins setup
        ring
  have hPressure :
      finalPressureInKilopascals setup =
        (5 : ℝ) / 6 * finalTemperatureInKelvins setup := by
    calc
      finalPressureInKilopascals setup =
          finalPressureInKilopascals setup *
              (volumeInCubicMeters (setup.stateAt .final .A).volume +
                volumeInCubicMeters (setup.stateAt .final .B).volume) / 2 := by
                    rw [hFinalVolume]
                    ring
      _ = ((5 : ℝ) / 3 * finalTemperatureInKelvins setup) / 2 := by
        rw [hPressureSum]
      _ = (5 : ℝ) / 6 * finalTemperatureInKelvins setup := by ring
  have hTemperatureToReal :
      Temperature.toReal (setup.stateAt .final .A).temperature =
        Temperature.toReal (setup.stateAt .final .B).temperature := by
    have hThermal :=
      _laws.conductingPistonGivesFinalThermalEquilibrium
    simpa [_data.temperatureScaleIsKelvin, temperatureInKelvins] using hThermal
  have hFinalTemperature :
      (setup.stateAt .final .A).temperature =
        (setup.stateAt .final .B).temperature := by
    apply Temperature.ext
    apply NNReal.coe_injective
    exact hTemperatureToReal
  have hFinalSpecificEnergy :
      stateSpecificInternalEnergyInKilojoulesPerKilogram setup .final .B =
        stateSpecificInternalEnergyInKilojoulesPerKilogram
          setup .final .A := by
    unfold stateSpecificInternalEnergyInKilojoulesPerKilogram
    rw [← hFinalTemperature]
  have hEnergy :=
    _laws.insulatedCylinderPreservesTotalAirInternalEnergy
  rw [hMassA, hMassB, hFinalSpecificEnergy] at hEnergy
  have hGasConstantNonzero :
      specificGasConstantInKilojoulesPerKilogramKelvin
          setup.specificGasConstant ≠ 0 :=
    ne_of_gt _physical.specificGasConstantPositive
  have hMassRatioScaled :
      (3 * airMassInKilograms (setup.stateAt .initial .A).airMass -
          2 * airMassInKilograms (setup.stateAt .initial .B).airMass) *
          specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant =
        0 := by
    calc
      (3 * airMassInKilograms (setup.stateAt .initial .A).airMass -
            2 * airMassInKilograms (setup.stateAt .initial .B).airMass) *
            specificGasConstantInKilojoulesPerKilogramKelvin
              setup.specificGasConstant =
          3 * (airMassInKilograms (setup.stateAt .initial .A).airMass *
              specificGasConstantInKilojoulesPerKilogramKelvin
                setup.specificGasConstant) -
            2 * (airMassInKilograms (setup.stateAt .initial .B).airMass *
              specificGasConstantInKilojoulesPerKilogramKelvin
                setup.specificGasConstant) := by ring
      _ = 0 := by rw [hMassGasA, hMassGasB]; norm_num
  have hMassRatio :
      3 * airMassInKilograms (setup.stateAt .initial .A).airMass =
        2 * airMassInKilograms (setup.stateAt .initial .B).airMass := by
    have hDifference :
        3 * airMassInKilograms (setup.stateAt .initial .A).airMass -
            2 * airMassInKilograms (setup.stateAt .initial .B).airMass =
          0 :=
      (mul_eq_zero.mp hMassRatioScaled).resolve_right hGasConstantNonzero
    linarith
  have hMassBInTermsOfA :
      airMassInKilograms (setup.stateAt .initial .B).airMass =
        (3 : ℝ) / 2 *
          airMassInKilograms (setup.stateAt .initial .A).airMass := by
    linarith [hMassRatio]
  rw [hMassBInTermsOfA] at hEnergy
  have hMassANonzero :
      airMassInKilograms (setup.stateAt .initial .A).airMass ≠ 0 :=
    ne_of_gt (_physical.airMassPositive .initial .A)
  have hNormalizedEnergy :
      stateSpecificInternalEnergyInKilojoulesPerKilogram
            setup .final .A +
          (3 : ℝ) / 2 *
            stateSpecificInternalEnergyInKilojoulesPerKilogram
              setup .final .A =
        stateSpecificInternalEnergyInKilojoulesPerKilogram
            setup .initial .A +
          (3 : ℝ) / 2 *
            stateSpecificInternalEnergyInKilojoulesPerKilogram
              setup .initial .B := by
    apply mul_left_cancel₀ hMassANonzero
    calc
      airMassInKilograms (setup.stateAt .initial .A).airMass *
            (stateSpecificInternalEnergyInKilojoulesPerKilogram
                setup .final .A +
              (3 : ℝ) / 2 *
                stateSpecificInternalEnergyInKilojoulesPerKilogram
                  setup .final .A) =
          airMassInKilograms (setup.stateAt .initial .A).airMass *
                stateSpecificInternalEnergyInKilojoulesPerKilogram
                  setup .final .A +
            ((3 : ℝ) / 2 *
                airMassInKilograms (setup.stateAt .initial .A).airMass) *
              stateSpecificInternalEnergyInKilojoulesPerKilogram
                setup .final .A := by ring
      _ =
          airMassInKilograms (setup.stateAt .initial .A).airMass *
                stateSpecificInternalEnergyInKilojoulesPerKilogram
                  setup .initial .A +
            ((3 : ℝ) / 2 *
                airMassInKilograms (setup.stateAt .initial .A).airMass) *
              stateSpecificInternalEnergyInKilojoulesPerKilogram
                setup .initial .B := hEnergy
      _ =
          airMassInKilograms (setup.stateAt .initial .A).airMass *
            (stateSpecificInternalEnergyInKilojoulesPerKilogram
                setup .initial .A +
              (3 : ℝ) / 2 *
                stateSpecificInternalEnergyInKilojoulesPerKilogram
                  setup .initial .B) := by ring
  have hEnergyCharacterization :
      5 * stateSpecificInternalEnergyInKilojoulesPerKilogram
          setup .final .A =
        2 * stateSpecificInternalEnergyInKilojoulesPerKilogram
            setup .initial .A +
          3 * stateSpecificInternalEnergyInKilojoulesPerKilogram
            setup .initial .B := by
    linarith [hNormalizedEnergy]
  refine ⟨hPressure, hEnergyCharacterization, ?_⟩
  rw [hPressure]
  constructor
  · intro h
    change (5 : ℝ) / 6 * finalTemperatureInKelvins setup = 613 at h
    linarith
  · intro h
    change finalTemperatureInKelvins setup = (3678 : ℝ) / 5 at h
    change (5 : ℝ) / 6 * finalTemperatureInKelvins setup = 613
    linarith

end PhyXMiniProblems.ProblemPhyXMini0458
