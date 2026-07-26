import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0462

open Dimension

/-!
# Heat rejected while R-410A cools beneath a loaded piston

A closed piston--cylinder initially contains `0.5 m^3` of R-410A at
`2 MPa` and `150 °C`.  The primary raster shows the refrigerant below a
horizontal piston, with the piston adjacent to upper stops.  Piston weight
and atmospheric loading correspond to a float pressure of `450 kPa`.
Cooling in a freezer at `-20 °C` therefore has two idealized stages: constant
volume while the upper stops remain active, followed by constant-pressure
compression after the piston begins to descend.

Pressure and energy use Physlib's dimensionful quantities, absolute
temperature uses Physlib's `Temperature`, and the remaining thermodynamic
quantities carry explicit physical dimensions.  Real numbers occur only as
readouts in named units or as the displayed multiple-choice values.

Assumption/target split:

* scenario, source readouts, and raster facts are recorded separately;
* an abstract R-410A equilibrium-property table supplies the endpoint
  specific-volume and specific-internal-energy quantities, but no uncited
  numerical table values or requested heat-transfer value;
* the laws state mass conservation, the two mechanical regimes, boundary
  work, and the closed-system first law;
* the target is the strongest source-supported symbolic heat formula in terms
  of the endpoint table lookups; `-7906.6 kJ` and answer D occur only as
  answer-sheet metadata, never as physical premises or conclusions.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- Physical dimension of volume, `L^3`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- Physical dimension of specific volume, `L^3 M^-1`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- Physical dimension of specific internal energy, `L^2 T^-2`. -/
def specificInternalEnergyDimension : Dimension :=
  L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-- A nonnegative physical specific internal energy. -/
abbrev SpecificInternalEnergyQuantity : Type :=
  Dimensionful (WithDim specificInternalEnergyDimension NNReal)

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical specific volume in cubic metres per kilogram. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume UnitChoices.SI).val : ℝ)

/-- Read specific internal energy in joules per kilogram. -/
def specificInternalEnergyInJoulesPerKilogram
    (specificInternalEnergy : SpecificInternalEnergyQuantity) : ℝ :=
  ((specificInternalEnergy UnitChoices.SI).val : ℝ)

/-- Read specific internal energy in kilojoules per kilogram. -/
def specificInternalEnergyInKilojoulesPerKilogram
    (specificInternalEnergy : SpecificInternalEnergyQuantity) : ℝ :=
  specificInternalEnergyInJoulesPerKilogram specificInternalEnergy / 1000

/-- Read a Physlib pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a Physlib pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a Physlib pressure in megapascals. -/
def pressureInMegapascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000000

/-- Read a signed physical energy, heat, or work in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a signed physical energy, heat, or work in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/--
Read a Physlib absolute temperature in kelvins.  The storage unit is explicit
because `Temperature` stores a nonnegative value in an arbitrary
zero-preserving temperature unit.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Exact Celsius-zero offset, `273.15 K`. -/
def celsiusZeroInKelvin : ℝ := 5463 / 20

/-- Affine Celsius readout of an absolute temperature. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - celsiusZeroInKelvin

/-! ## Process states and physical roles -/

/-- States separating the fixed-volume and floating-piston stages. -/
inductive ProcessState where
  | initialAtUpperStops
  | onsetOfFloating
  | finalInFreezer
  deriving DecidableEq, Fintype, Repr

/-- Directed legs of the cooling process. -/
inductive ProcessLeg where
  | fixedVolumeCooling
  | floatingPistonCooling
  deriving DecidableEq, Fintype, Repr

/-- Source state of each directed cooling leg. -/
def legSource : ProcessLeg → ProcessState
  | .fixedVolumeCooling => .initialAtUpperStops
  | .floatingPistonCooling => .onsetOfFloating

/-- Target state of each directed cooling leg. -/
def legTarget : ProcessLeg → ProcessState
  | .fixedVolumeCooling => .onsetOfFloating
  | .floatingPistonCooling => .finalInFreezer

/-- Refrigerant identity, distinct from all scalar property readouts. -/
inductive RefrigerantKind where
  | r410A
  | other
  deriving DecidableEq, Repr

/-- Equilibrium region returned by an R-410A property table. -/
inductive RefrigerantPhaseRegion where
  | compressedLiquid
  | saturatedMixture
  | superheatedVapor
  | supercriticalGas
  | other
  deriving DecidableEq, Repr

/-- Orientation of the cylinder axis. -/
inductive CylinderOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Mechanical support regime of the piston. -/
inductive PistonSupportRegime where
  | pressingAgainstUpperStops
  | freelyFloatingUnderLoad
  | other
  deriving DecidableEq, Repr

/-- Origin of the constant load pressure stated in the prose. -/
inductive LoadPressureOrigin where
  | pistonMassAndAtmosphere
  | other
  deriving DecidableEq, Repr

/-- Thermal environment surrounding the complete apparatus. -/
inductive ThermalEnvironment where
  | maintainedFreezer
  | other
  deriving DecidableEq, Repr

/-- Sign convention for every heat and work observable below. -/
inductive EnergySignConvention where
  | heatIntoSystemAndWorkBySystemPositive
  deriving DecidableEq, Repr

/-! ## Property table, thermodynamic state, and primary figure -/

/--
An external equilibrium-property table for R-410A.  Its outputs retain their
physical dimensions; the table does not contain a net process heat.
-/
structure R410APropertyTable where
  phaseAt :
    TemperatureUnit → DimPressure → Temperature → RefrigerantPhaseRegion
  specificVolumeAt :
    TemperatureUnit → DimPressure → Temperature → SpecificVolumeQuantity
  specificInternalEnergyAt :
    TemperatureUnit → DimPressure → Temperature →
      SpecificInternalEnergyQuantity

/-- A macroscopic equilibrium state of the closed refrigerant sample. -/
structure RefrigerantState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  phaseRegion : RefrigerantPhaseRegion
  specificVolume : SpecificVolumeQuantity
  specificInternalEnergy : SpecificInternalEnergyQuantity

/-- Objects visible in the supplied sectional raster. -/
inductive FigureObject where
  | cylinderWalls
  | horizontalPiston
  | leftUpperStop
  | rightUpperStop
  | lightBlueRefrigerantRegion
  deriving DecidableEq, Fintype, Repr

/-- Literal label printed inside the light-blue region. -/
inductive FigureLabel where
  | r410A
  deriving DecidableEq, Fintype, Repr

/-- Qualitative content transcribed from the primary image. -/
structure SuppliedPistonCylinderFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  pistonIsHorizontal : Bool
  refrigerantIsBelowPiston : Bool
  refrigerantTouchesCylinderBottom : Bool
  pistonIsAdjacentToUpperStops : Bool
  cylinderIsClosedAtBottom : Bool

/-!
The complete apparatus and its independent observables.  `netHeatTransfer`
is positive into the R-410A, while each work observable is positive when done
by the R-410A on its surroundings.  No field is assigned a numerical answer.
-/
structure R410ACoolingPistonCylinder where
  refrigerant : RefrigerantKind
  cylinderOrientation : CylinderOrientation
  supportRegime : ProcessState → PistonSupportRegime
  loadPressureOrigin : LoadPressureOrigin
  thermalEnvironment : ThermalEnvironment
  signConvention : EnergySignConvention
  closedRefrigerantSample : Bool
  negligiblePistonFriction : Bool
  negligibleBulkKineticAndPotentialEnergyChanges : Bool
  temperatureStorageUnit : TemperatureUnit
  floatPressure : DimPressure
  freezerTemperature : Temperature
  refrigerantMass : MassQuantity
  stateAt : ProcessState → RefrigerantState
  totalInternalEnergyAt : ProcessState → DimEnergy
  heatTransferredIntoRefrigerantOn : ProcessLeg → DimEnergy
  boundaryWorkDoneByRefrigerantOn : ProcessLeg → DimEnergy
  netHeatTransferIntoRefrigerant : DimEnergy
  netBoundaryWorkDoneByRefrigerant : DimEnergy
  propertyTable : R410APropertyTable
  figure : SuppliedPistonCylinderFigure

/-- Celsius readout at one modeled process state. -/
def stateTemperatureInDegreesCelsius
    (setup : R410ACoolingPistonCylinder) (state : ProcessState) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    (setup.stateAt state).temperature

/-- Kelvin readout at one modeled process state. -/
def stateTemperatureInKelvin
    (setup : R410ACoolingPistonCylinder) (state : ProcessState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.stateAt state).temperature

/-- Kilojoule readout of total internal energy at a modeled state. -/
def totalInternalEnergyInKilojoules
    (setup : R410ACoolingPistonCylinder) (state : ProcessState) : ℝ :=
  energyInKilojoules (setup.totalInternalEnergyAt state)

/-- Signed heat into the refrigerant on one leg, in kilojoules. -/
def legHeatTransferInKilojoules
    (setup : R410ACoolingPistonCylinder) (leg : ProcessLeg) : ℝ :=
  energyInKilojoules (setup.heatTransferredIntoRefrigerantOn leg)

/-- Signed boundary work by the refrigerant on one leg, in kilojoules. -/
def legBoundaryWorkInKilojoules
    (setup : R410ACoolingPistonCylinder) (leg : ProcessLeg) : ℝ :=
  energyInKilojoules (setup.boundaryWorkDoneByRefrigerantOn leg)

/-- Requested overall signed heat transfer, in kilojoules. -/
def netHeatTransferInKilojoules
    (setup : R410ACoolingPistonCylinder) : ℝ :=
  energyInKilojoules setup.netHeatTransferIntoRefrigerant

/-- Overall signed boundary work by the refrigerant, in kilojoules. -/
def netBoundaryWorkInKilojoules
    (setup : R410ACoolingPistonCylinder) : ℝ :=
  energyInKilojoules setup.netBoundaryWorkDoneByRefrigerant

/-! ## Scenario, data readouts, primary-image evidence, and laws -/

/-- Qualitative physical conditions stated or implied by the problem. -/
structure MatchesCoolingR410AScenario
    (setup : R410ACoolingPistonCylinder) : Prop where
  containsR410A : setup.refrigerant = .r410A
  cylinderIsVertical : setup.cylinderOrientation = .vertical
  initiallyAtUpperStops :
    setup.supportRegime .initialAtUpperStops =
      .pressingAgainstUpperStops
  pistonFloatsAtTransition :
    setup.supportRegime .onsetOfFloating = .freelyFloatingUnderLoad
  pistonFloatsAtFinalState :
    setup.supportRegime .finalInFreezer = .freelyFloatingUnderLoad
  pressureComesFromPistonAndAtmosphere :
    setup.loadPressureOrigin = .pistonMassAndAtmosphere
  apparatusIsInMaintainedFreezer :
    setup.thermalEnvironment = .maintainedFreezer
  closedSample : setup.closedRefrigerantSample = true
  frictionIsNegligible : setup.negligiblePistonFriction = true
  kineticAndPotentialChangesAreNegligible :
    setup.negligibleBulkKineticAndPotentialEnergyChanges = true
  statedSignConvention :
    setup.signConvention = .heatIntoSystemAndWorkBySystemPositive

/-!
Numerical readouts stated in the prose.  No field mentions heat transfer,
internal-energy change, boundary work, or an answer choice.
-/
structure MatchesProblemReadouts
    (setup : R410ACoolingPistonCylinder) : Prop where
  initialVolumeCubicMeters :
    volumeInCubicMeters
        (setup.stateAt .initialAtUpperStops).volume = 1 / 2
  initialPressureMegapascals :
    pressureInMegapascals
        (setup.stateAt .initialAtUpperStops).pressure = 2
  initialTemperatureCelsius :
    stateTemperatureInDegreesCelsius setup .initialAtUpperStops = 150
  floatPressureKilopascals :
    pressureInKilopascals setup.floatPressure = 450
  freezerTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
        setup.freezerTemperature = -20
  finalTemperatureCelsius :
    stateTemperatureInDegreesCelsius setup .finalInFreezer = -20
  finalTemperatureEqualsFreezer :
    (setup.stateAt .finalInFreezer).temperature = setup.freezerTemperature

/-!
Primary-raster evidence.  The bitmap supplies geometry and the `R-410a`
label but no pressure, temperature, volume, heat, work, or answer readout.
-/
structure MatchesSuppliedPistonCylinderFigure
    (setup : R410ACoolingPistonCylinder) : Prop where
  everyNamedObjectIsShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  refrigerantLabelIsShown : setup.figure.showsLabel .r410A = true
  pistonIsHorizontal : setup.figure.pistonIsHorizontal = true
  refrigerantBelowPiston : setup.figure.refrigerantIsBelowPiston = true
  refrigerantAtCylinderBottom :
    setup.figure.refrigerantTouchesCylinderBottom = true
  pistonAdjacentToStops :
    setup.figure.pistonIsAdjacentToUpperStops = true
  cylinderClosedAtBottom : setup.figure.cylinderIsClosedAtBottom = true

/-!
Symbolic constitutive information required from an equilibrium R-410A
property table at the two source-specified endpoint states.  The source does
not identify a property-table edition or provide numerical endpoint values,
so this interface records only that the state properties come from the table.
In particular, it contains no heat-transfer value or answer choice.
-/
structure MatchesReferenceR410APropertyData
    (setup : R410ACoolingPistonCylinder) : Prop where
  initialRegionFromReferenceTable :
    (setup.stateAt .initialAtUpperStops).phaseRegion =
      setup.propertyTable.phaseAt
        setup.temperatureStorageUnit
        (setup.stateAt .initialAtUpperStops).pressure
        (setup.stateAt .initialAtUpperStops).temperature
  finalRegionFromReferenceTable :
    (setup.stateAt .finalInFreezer).phaseRegion =
      setup.propertyTable.phaseAt
        setup.temperatureStorageUnit
        (setup.stateAt .finalInFreezer).pressure
        (setup.stateAt .finalInFreezer).temperature
  initialSpecificVolumeFromReferenceTable :
    (setup.stateAt .initialAtUpperStops).specificVolume =
      setup.propertyTable.specificVolumeAt
        setup.temperatureStorageUnit
        (setup.stateAt .initialAtUpperStops).pressure
        (setup.stateAt .initialAtUpperStops).temperature
  finalSpecificVolumeFromReferenceTable :
    (setup.stateAt .finalInFreezer).specificVolume =
      setup.propertyTable.specificVolumeAt
        setup.temperatureStorageUnit
        (setup.stateAt .finalInFreezer).pressure
        (setup.stateAt .finalInFreezer).temperature
  initialSpecificInternalEnergyFromReferenceTable :
    (setup.stateAt .initialAtUpperStops).specificInternalEnergy =
      setup.propertyTable.specificInternalEnergyAt
        setup.temperatureStorageUnit
        (setup.stateAt .initialAtUpperStops).pressure
        (setup.stateAt .initialAtUpperStops).temperature
  finalSpecificInternalEnergyFromReferenceTable :
    (setup.stateAt .finalInFreezer).specificInternalEnergy =
      setup.propertyTable.specificInternalEnergyAt
        setup.temperatureStorageUnit
        (setup.stateAt .finalInFreezer).pressure
        (setup.stateAt .finalInFreezer).temperature

/-- Positivity and branch conditions selecting the stated physical process. -/
structure HasPhysicalR410ACoolingParameters
    (setup : R410ACoolingPistonCylinder) : Prop where
  massPositive : 0 < massInKilograms setup.refrigerantMass
  floatPressurePositive : 0 < pressureInKilopascals setup.floatPressure
  statePressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  stateVolumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  absoluteTemperaturePositive : ∀ state,
    0 < stateTemperatureInKelvin setup state
  specificVolumePositive : ∀ state,
    0 < specificVolumeInCubicMetersPerKilogram
      (setup.stateAt state).specificVolume
  initialPressureExceedsFloatPressure :
    pressureInPascals setup.floatPressure <
      pressureInPascals
        (setup.stateAt .initialAtUpperStops).pressure
  finalVolumeBelowInitialVolume :
    volumeInCubicMeters (setup.stateAt .finalInFreezer).volume <
      volumeInCubicMeters (setup.stateAt .initialAtUpperStops).volume

/-!
Governing geometry, mechanics, work, and energy laws:

* the same closed mass satisfies `V = m v` and `U = m u` at every state;
* the first leg is isochoric until pressure reaches the float pressure;
* the second leg is isobaric at the piston-and-atmosphere load pressure;
* `W_by = P_float (V_f - V_transition)` on the moving leg, using
  `1 kPa m^3 = 1 kJ`;
* on each leg, `Q_in = U_f - U_i + W_by`;
* net heat and work are the sums over the two legs.

None of these laws specifies a numerical net heat, an answer choice, or the
recorded `-7906.6 kJ` value.
-/
structure SatisfiesR410ACoolingLaws
    (setup : R410ACoolingPistonCylinder) : Prop where
  volumeFromClosedMassAndSpecificVolume : ∀ state,
    volumeInCubicMeters (setup.stateAt state).volume =
      massInKilograms setup.refrigerantMass *
        specificVolumeInCubicMetersPerKilogram
          (setup.stateAt state).specificVolume
  totalInternalEnergyFromSpecificProperty : ∀ state,
    totalInternalEnergyInKilojoules setup state =
      massInKilograms setup.refrigerantMass *
        specificInternalEnergyInKilojoulesPerKilogram
          (setup.stateAt state).specificInternalEnergy
  fixedVolumeUntilPistonFloats :
    (setup.stateAt .onsetOfFloating).volume =
      (setup.stateAt .initialAtUpperStops).volume
  transitionOccursAtFloatPressure :
    (setup.stateAt .onsetOfFloating).pressure = setup.floatPressure
  floatingPistonMaintainsLoadPressure :
    (setup.stateAt .finalInFreezer).pressure = setup.floatPressure
  fixedVolumeLegDoesNoBoundaryWork :
    legBoundaryWorkInKilojoules setup .fixedVolumeCooling = 0
  floatingPistonBoundaryWork :
    legBoundaryWorkInKilojoules setup .floatingPistonCooling =
      pressureInKilopascals setup.floatPressure *
        (volumeInCubicMeters (setup.stateAt .finalInFreezer).volume -
          volumeInCubicMeters (setup.stateAt .onsetOfFloating).volume)
  firstLawOnEachLeg : ∀ leg,
    legHeatTransferInKilojoules setup leg =
      totalInternalEnergyInKilojoules setup (legTarget leg) -
        totalInternalEnergyInKilojoules setup (legSource leg) +
          legBoundaryWorkInKilojoules setup leg
  netHeatIsSumOfLegHeats :
    netHeatTransferInKilojoules setup =
      legHeatTransferInKilojoules setup .fixedVolumeCooling +
        legHeatTransferInKilojoules setup .floatingPistonCooling
  netWorkIsSumOfLegWorks :
    netBoundaryWorkInKilojoules setup =
      legBoundaryWorkInKilojoules setup .fixedVolumeCooling +
        legBoundaryWorkInKilojoules setup .floatingPistonCooling

/-! ## Derived energy relation and source-supported target -/

/-!
The two stagewise first laws telescope.  Using the fixed initial volume and
the constant float pressure on the moving leg yields both the total-energy
and the mass-specific-property forms of the overall heat balance.
-/
theorem overallHeatTransferFormula
    (setup : R410ACoolingPistonCylinder)
    (_physical : HasPhysicalR410ACoolingParameters setup)
    (_laws : SatisfiesR410ACoolingLaws setup) :
    netHeatTransferInKilojoules setup =
        totalInternalEnergyInKilojoules setup .finalInFreezer -
          totalInternalEnergyInKilojoules setup .initialAtUpperStops +
        pressureInKilopascals setup.floatPressure *
          (volumeInCubicMeters (setup.stateAt .finalInFreezer).volume -
            volumeInCubicMeters
              (setup.stateAt .initialAtUpperStops).volume) ∧
      netHeatTransferInKilojoules setup =
        massInKilograms setup.refrigerantMass *
            (specificInternalEnergyInKilojoulesPerKilogram
                (setup.stateAt .finalInFreezer).specificInternalEnergy -
              specificInternalEnergyInKilojoulesPerKilogram
                (setup.stateAt .initialAtUpperStops).specificInternalEnergy) +
          pressureInKilopascals setup.floatPressure *
            (volumeInCubicMeters (setup.stateAt .finalInFreezer).volume -
              volumeInCubicMeters
                (setup.stateAt .initialAtUpperStops).volume) := by
  sorry

/-- Labels of the four answers printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed heat transfer in kilojoules printed beside each answer label. -/
def displayedHeatTransferInKilojoules : AnswerChoice → ℝ
  | .A => -(2179 / 10)
  | .B => -(747 / 2)
  | .C => -(223 / 10)
  | .D => -(39533 / 5)

/-- Answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
For the stated source data, primary-image geometry, symbolic R-410A endpoint
property lookups, physical branch, and governing laws, the overall heat into
the refrigerant is determined by the closed-system first law.  Substituting
`V₁ = 0.5 m³`, `P_float = 450 kPa`, `m = V₁ / v₁`, and `V₂ = m v₂` gives the
formula below.  A numerical choice requires independently grounded values for
`v₁`, `u₁`, `v₂`, and `u₂`; the supplied source does not provide them or name
a property-table edition.  Consequently the recorded answer remains metadata
and is not asserted as a physical conclusion.

Blueprint label: `thm:physics:phyx_mini_0462:target`.
-/
theorem problem_phyx_mini_0462
    (setup : R410ACoolingPistonCylinder)
    (_scenario : MatchesCoolingR410AScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedPistonCylinderFigure setup)
    (_referenceData : MatchesReferenceR410APropertyData setup)
    (_physical : HasPhysicalR410ACoolingParameters setup)
    (_laws : SatisfiesR410ACoolingLaws setup) :
    let initialState := setup.stateAt .initialAtUpperStops
    let finalState := setup.stateAt .finalInFreezer
    let v₁ := specificVolumeInCubicMetersPerKilogram
      (setup.propertyTable.specificVolumeAt
        setup.temperatureStorageUnit
        initialState.pressure initialState.temperature)
    let u₁ := specificInternalEnergyInKilojoulesPerKilogram
      (setup.propertyTable.specificInternalEnergyAt
        setup.temperatureStorageUnit
        initialState.pressure initialState.temperature)
    let v₂ := specificVolumeInCubicMetersPerKilogram
      (setup.propertyTable.specificVolumeAt
        setup.temperatureStorageUnit
        finalState.pressure finalState.temperature)
    let u₂ := specificInternalEnergyInKilojoulesPerKilogram
      (setup.propertyTable.specificInternalEnergyAt
        setup.temperatureStorageUnit
        finalState.pressure finalState.temperature)
    netHeatTransferInKilojoules setup =
      ((1 / 2 : ℝ) / v₁) * (u₂ - u₁) +
        450 * (((1 / 2 : ℝ) / v₁) * v₂ - 1 / 2) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0462
