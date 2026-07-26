import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Heat transfer to water in a spring-loaded piston--cylinder

A closed piston--cylinder initially contains `0.5 kg` of saturated water
vapor at `120 °C`.  Heating raises a vertical piston restrained by a linear
spring.  The stated spring constant is `15 kN/m`, the piston area is
`0.05 m²`, and the final pressure is `500 kPa`.

The physical mass, length, area, volume, pressure, specific volume, specific
internal energy, total internal energy, work, and heat below carry dimensions
through Physlib.  Real numbers occur only as explicitly named unit readouts,
path parameters, reference-table entries, and displayed answer values.

Assumption/target split:

* scenario premises record the closed water system, heating, piston rise,
  linear spring, and quasistatic process;
* figure premises record the cylinder, water, piston, spring, and their
  relative positions in the primary raster;
* readout premises record only the numerical data stated in the problem;
* reference premises give independent saturated- and superheated-water table
  entries at the states selected by the governing equations;
* governing laws state mass--specific-property relations, piston sweep,
  Hooke/static-load balance, linear `pV` work, and the closed-system first law;
* the conclusion, rather than any premise, computes the heat and selects the
  displayed `587 kJ` answer D.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0452

open Dimension

/-! ## Dimensionful quantities and named unit readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative vertical piston position or displacement. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume, carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative thermodynamic specific volume, carrying dimension `L³ M⁻¹`. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹) NNReal)

/-- A signed specific internal energy, carrying dimension `L² T⁻²`. -/
abbrev SpecificEnergyQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A linear spring constant, with force-per-length dimension `M T⁻²`. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-metre-per-kilogram readout of a physical specific volume. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Kilopascal readout used by the source problem and steam table. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Joule-per-kilogram readout of a physical specific energy. -/
def specificEnergyInJoulesPerKilogram
    (energy : SpecificEnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- Kilojoule-per-kilogram readout used by the steam table. -/
def specificEnergyInKilojoulesPerKilogram
    (energy : SpecificEnergyQuantity) : ℝ :=
  specificEnergyInJoulesPerKilogram energy / 1000

/-- Joule readout of a signed physical energy, heat transfer, or work. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Kilojoule readout used by the displayed heat choices. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Newton-per-metre readout of a physical linear spring constant. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-!
Physlib's `Temperature` is an absolute nonnegative temperature.  The affine
Celsius readout and its exact `273.15 K` offset are recorded alongside that
physical value rather than identifying temperature with a real scalar.
-/
structure CelsiusTemperatureReading where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ
  celsiusKelvinCalibration :
    absoluteTemperature.toReal = degreesCelsius + 5463 / 20

/-! ## Water states, apparatus, and primary-figure vocabulary -/

/-- The two equilibrium states named by the process description. -/
inductive ProcessState where
  | initialSaturatedVapor
  | finalAtFiveHundredKilopascals
  deriving DecidableEq, Fintype, Repr

/-- Chemical substance occupying the closed cylinder. -/
inductive WorkingSubstance where
  | water
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic region of an equilibrium water state. -/
inductive WaterRegion where
  | compressedLiquid
  | saturatedMixture
  | saturatedVapor
  | superheatedVapor
  | other
  deriving DecidableEq, Repr

/-- Constitutive model assigned to the restraining spring. -/
inductive SpringModel where
  | linearHookean
  | other
  deriving DecidableEq, Repr

/-- Objects visible in the primary raster `phyx_data/test_image/452.png`. -/
inductive FigureObject where
  | rigidCylinderWalls
  | waterRegion
  | movablePiston
  | coiledSpring
  | fixedTopSupport
  deriving DecidableEq, Fintype, Repr

/-- Text printed in the primary raster. -/
inductive FigureTextLabel where
  | waterH2O
  deriving DecidableEq, Fintype, Repr

/-- Distinguished endpoints of the drawn vertical spring. -/
inductive SpringEndpoint where
  | pistonUpperFace
  | fixedTopSupport
  deriving DecidableEq, Repr

/-!
Qualitative geometry transcribed from the primary image.  It contains no
numeric heat, pressure, volume, displacement, or steam-table readout.
-/
structure SpringPistonFigure where
  objectShown : FigureObject → Bool
  textLabelShown : FigureTextLabel → Bool
  springEndpoints : SpringEndpoint × SpringEndpoint
  pistonIsHorizontal : Bool
  waterIsBelowPiston : Bool
  springIsAbovePiston : Bool
  rigidWallsEncloseWaterAndPiston : Bool

/-- One equilibrium water state, with independent dimensionful observables. -/
structure ThermodynamicState where
  pressure : DimPressure
  temperature : CelsiusTemperatureReading
  volume : VolumeQuantity
  specificVolume : SpecificVolumeQuantity
  specificInternalEnergy : SpecificEnergyQuantity
  waterRegion : WaterRegion

/-!
An external equilibrium-water property table.  Its entries are physical
quantities, and its arguments select a state independently of the requested
process heat.
-/
structure WaterPropertyTable where
  saturationPressureAt : Temperature → DimPressure
  saturatedVaporSpecificVolumeAt : Temperature → SpecificVolumeQuantity
  saturatedVaporSpecificInternalEnergyAt :
    Temperature → SpecificEnergyQuantity
  specificInternalEnergyAtPressureAndSpecificVolume :
    DimPressure → SpecificVolumeQuantity → SpecificEnergyQuantity
  regionAtPressureAndSpecificVolume :
    DimPressure → SpecificVolumeQuantity → WaterRegion

/-!
The closed spring-piston experiment.  Heat into the water and boundary work
done by the water are positive.  Neither is defined from an answer choice.
-/
structure SpringPistonWaterProcess where
  figure : SpringPistonFigure
  workingSubstance : WorkingSubstance
  waterMass : MassQuantity
  state : ProcessState → ThermodynamicState
  stateAlongPath : ℝ → ThermodynamicState
  totalInternalEnergy : ProcessState → DimEnergy
  heatTransferredToWater : DimEnergy
  workDoneByWater : DimEnergy
  pistonArea : DimArea
  pistonHeight : ProcessState → LengthQuantity
  springConstant : SpringConstantQuantity
  springModel : SpringModel
  waterTable : WaterPropertyTable
  systemIsClosed : Bool
  pistonIsMovable : Bool
  pistonIsFrictionless : Bool
  processIsQuasistatic : Bool
  heatIsAddedToWater : Bool
  pressureVariesLinearlyWithVolume : Bool

/-! ## Scenario, primary-image evidence, and supplied readouts -/

/-- Qualitative physical facts stated or implied by the source scenario. -/
structure MatchesClosedSpringPistonWaterScenario
    (setup : SpringPistonWaterProcess) : Prop where
  substanceIsWater : setup.workingSubstance = .water
  initiallySaturatedVapor :
    (setup.state .initialSaturatedVapor).waterRegion = .saturatedVapor
  closedWaterSample : setup.systemIsClosed = true
  movablePiston : setup.pistonIsMovable = true
  frictionlessPiston : setup.pistonIsFrictionless = true
  quasistaticProcess : setup.processIsQuasistatic = true
  heatAdded : setup.heatIsAddedToWater = true
  linearSpring : setup.springModel = .linearHookean
  linearPressureVolumePath :
    setup.pressureVariesLinearlyWithVolume = true
  pistonRises :
    lengthInMeters
        (setup.pistonHeight .initialSaturatedVapor) <
      lengthInMeters
        (setup.pistonHeight .finalAtFiveHundredKilopascals)

/-!
Evidence read from the primary raster: water lies below a horizontal movable
piston, and a coiled spring joins the piston's upper face to the fixed top of
the enclosing cylinder.
-/
structure MatchesPrimarySpringPistonFigure
    (figure : SpringPistonFigure) : Prop where
  everyObjectShown : ∀ object, figure.objectShown object = true
  everyTextLabelShown : ∀ label, figure.textLabelShown label = true
  springAttachmentGeometry :
    figure.springEndpoints = (.pistonUpperFace, .fixedTopSupport)
  horizontalPiston : figure.pistonIsHorizontal = true
  waterBelowPiston : figure.waterIsBelowPiston = true
  springAbovePiston : figure.springIsAbovePiston = true
  enclosingRigidWalls : figure.rigidWallsEncloseWaterAndPiston = true

/-!
The five numerical values stated in the prose.  In particular, no heat,
boundary work, internal-energy change, or answer choice occurs here.
-/
structure MatchesProblemReadouts
    (setup : SpringPistonWaterProcess) : Prop where
  waterMassKilograms : massInKilograms setup.waterMass = 1 / 2
  initialTemperatureDegreesCelsius :
    (setup.state .initialSaturatedVapor).temperature.degreesCelsius = 120
  springConstantNewtonsPerMeter :
    springConstantInNewtonsPerMeter setup.springConstant = 15000
  pistonAreaSquareMeters : areaInSquareMeters setup.pistonArea = 1 / 20
  finalPressureKilopascals :
    pressureInKilopascals
      (setup.state .finalAtFiveHundredKilopascals).pressure = 500

/-! Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalSpringPistonParameters
    (setup : SpringPistonWaterProcess) : Prop where
  massPositive : 0 < massInKilograms setup.waterMass
  pistonAreaPositive : 0 < areaInSquareMeters setup.pistonArea
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.state state).pressure
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.state state).volume
  specificVolumePositive :
    ∀ state,
      0 < specificVolumeInCubicMetersPerKilogram
        (setup.state state).specificVolume
  absoluteTemperaturePositive :
    ∀ state, 0 < (setup.state state).temperature.absoluteTemperature.toReal

/-! ## Water-property calibration and governing laws -/

/-!
Constitutive water-property relations.  The initial saturated-vapor entries
are indexed by its absolute temperature.  The final internal energy and phase
are indexed by the independently determined final pressure and specific
volume.  No process heat appears in these relations.
-/
structure SatisfiesWaterPropertyModel
    (setup : SpringPistonWaterProcess) : Prop where
  initialSaturationPressure :
    (setup.state .initialSaturatedVapor).pressure =
      setup.waterTable.saturationPressureAt
        (setup.state .initialSaturatedVapor).temperature.absoluteTemperature
  initialSaturatedVaporSpecificVolume :
    (setup.state .initialSaturatedVapor).specificVolume =
      setup.waterTable.saturatedVaporSpecificVolumeAt
        (setup.state .initialSaturatedVapor).temperature.absoluteTemperature
  initialSaturatedVaporSpecificInternalEnergy :
    (setup.state .initialSaturatedVapor).specificInternalEnergy =
      setup.waterTable.saturatedVaporSpecificInternalEnergyAt
        (setup.state .initialSaturatedVapor).temperature.absoluteTemperature
  finalSpecificInternalEnergy :
    (setup.state .finalAtFiveHundredKilopascals).specificInternalEnergy =
      setup.waterTable.specificInternalEnergyAtPressureAndSpecificVolume
        (setup.state .finalAtFiveHundredKilopascals).pressure
        (setup.state .finalAtFiveHundredKilopascals).specificVolume
  finalWaterRegion :
    (setup.state .finalAtFiveHundredKilopascals).waterRegion =
      setup.waterTable.regionAtPressureAndSpecificVolume
        (setup.state .finalAtFiveHundredKilopascals).pressure
        (setup.state .finalAtFiveHundredKilopascals).specificVolume

/-!
Rounded reference steam-table entries used by the textbook calculation:

* saturated water vapor at `120 °C` has `p_sat = 198.53 kPa`,
  `v_g = 0.8919 m³/kg`, and `u_g = 2529.1 kJ/kg`;
* at the final pressure and the specific volume fixed by the spring-piston
  equations, interpolation in the superheated table gives approximately
  `u₂ = 3668.1 kJ/kg`.

These are independent material-property calibrations, not a heat answer.
-/
structure MatchesReferenceSteamTableData
    (setup : SpringPistonWaterProcess) : Prop where
  initialSaturationPressureKilopascals :
    pressureInKilopascals
        (setup.waterTable.saturationPressureAt
          (setup.state .initialSaturatedVapor).temperature.absoluteTemperature) =
      19853 / 100
  initialSaturatedVaporSpecificVolume :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.saturatedVaporSpecificVolumeAt
          (setup.state .initialSaturatedVapor).temperature.absoluteTemperature) =
      8919 / 10000
  initialSaturatedVaporSpecificInternalEnergy :
    specificEnergyInKilojoulesPerKilogram
        (setup.waterTable.saturatedVaporSpecificInternalEnergyAt
          (setup.state .initialSaturatedVapor).temperature.absoluteTemperature) =
      25291 / 10
  finalSpecificInternalEnergy :
    specificEnergyInKilojoulesPerKilogram
        (setup.waterTable.specificInternalEnergyAtPressureAndSpecificVolume
          (setup.state .finalAtFiveHundredKilopascals).pressure
          (setup.state .finalAtFiveHundredKilopascals).specificVolume) =
      36681 / 10
  finalStateIsSuperheatedVapor :
    setup.waterTable.regionAtPressureAndSpecificVolume
        (setup.state .finalAtFiveHundredKilopascals).pressure
        (setup.state .finalAtFiveHundredKilopascals).specificVolume =
      .superheatedVapor

/-!
Definitions of total volume and total internal energy from mass and specific
properties, expressed in coherent named readouts at each endpoint.
-/
structure SatisfiesMassSpecificPropertyLaws
    (setup : SpringPistonWaterProcess) : Prop where
  volumeFromMassAndSpecificVolume : ∀ state : ProcessState,
    volumeInCubicMeters (setup.state state).volume =
      massInKilograms setup.waterMass *
        specificVolumeInCubicMetersPerKilogram
          (setup.state state).specificVolume
  totalInternalEnergyFromSpecificInternalEnergy : ∀ state : ProcessState,
    energyInKilojoules (setup.totalInternalEnergy state) =
      massInKilograms setup.waterMass *
        specificEnergyInKilojoulesPerKilogram
          (setup.state state).specificInternalEnergy

/-!
Mechanical and pressure--volume laws for the spring-loaded piston:

* piston sweep changes volume by area times vertical displacement;
* the increase in pressure force balances the increase in Hookean spring
  force, while constant atmospheric and piston-weight loads cancel;
* pressure and volume are affine along the quasistatic path;
* boundary work on that straight `pV` path is its trapezoid area.

None of these laws assigns a numerical heat transfer.
-/
structure SatisfiesLinearSpringPistonAndWorkLaws
    (setup : SpringPistonWaterProcess) : Prop where
  pathStartsAtInitialState :
    setup.stateAlongPath 0 = setup.state .initialSaturatedVapor
  pathFinishesAtFinalState :
    setup.stateAlongPath 1 =
      setup.state .finalAtFiveHundredKilopascals
  affineVolumeAlongPath :
    ∀ parameter ∈ Set.Icc (0 : ℝ) 1,
      volumeInCubicMeters (setup.stateAlongPath parameter).volume =
        (1 - parameter) *
            volumeInCubicMeters
              (setup.state .initialSaturatedVapor).volume +
          parameter *
            volumeInCubicMeters
              (setup.state .finalAtFiveHundredKilopascals).volume
  affinePressureAlongPath :
    ∀ parameter ∈ Set.Icc (0 : ℝ) 1,
      pressureInPascals (setup.stateAlongPath parameter).pressure =
        (1 - parameter) *
            pressureInPascals
              (setup.state .initialSaturatedVapor).pressure +
          parameter *
            pressureInPascals
              (setup.state .finalAtFiveHundredKilopascals).pressure
  pistonSweptVolumeLaw :
    volumeInCubicMeters
          (setup.state .finalAtFiveHundredKilopascals).volume -
        volumeInCubicMeters
          (setup.state .initialSaturatedVapor).volume =
      areaInSquareMeters setup.pistonArea *
        (lengthInMeters
              (setup.pistonHeight .finalAtFiveHundredKilopascals) -
          lengthInMeters
              (setup.pistonHeight .initialSaturatedVapor))
  linearSpringLoadIncrement :
    (pressureInPascals
          (setup.state .finalAtFiveHundredKilopascals).pressure -
        pressureInPascals
          (setup.state .initialSaturatedVapor).pressure) *
        areaInSquareMeters setup.pistonArea =
      springConstantInNewtonsPerMeter setup.springConstant *
        (lengthInMeters
              (setup.pistonHeight .finalAtFiveHundredKilopascals) -
          lengthInMeters
              (setup.pistonHeight .initialSaturatedVapor))
  straightPathBoundaryWork :
    energyInJoules setup.workDoneByWater =
      (pressureInPascals
            (setup.state .initialSaturatedVapor).pressure +
          pressureInPascals
            (setup.state .finalAtFiveHundredKilopascals).pressure) / 2 *
        (volumeInCubicMeters
              (setup.state .finalAtFiveHundredKilopascals).volume -
          volumeInCubicMeters
              (setup.state .initialSaturatedVapor).volume)

/-!
Closed-system first law with heat positive into the water and boundary work
positive when done by the water: `Q = U₂ - U₁ + W_by`.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : SpringPistonWaterProcess) : Prop where
  firstLaw :
    energyInKilojoules setup.heatTransferredToWater =
      energyInKilojoules
          (setup.totalInternalEnergy .finalAtFiveHundredKilopascals) -
        energyInKilojoules
          (setup.totalInternalEnergy .initialSaturatedVapor) +
        energyInKilojoules setup.workDoneByWater

/-! ## Derived quantities, displayed answers, and current target -/

/-- The initial saturation pressure obtained from the water table. -/
lemma initialPressure_in_kilopascals
    (setup : SpringPistonWaterProcess)
    (_properties : SatisfiesWaterPropertyModel setup)
    (_reference : MatchesReferenceSteamTableData setup) :
    pressureInKilopascals
        (setup.state .initialSaturatedVapor).pressure =
      19853 / 100 := by
  rw [_properties.initialSaturationPressure]
  exact _reference.initialSaturationPressureKilopascals

/-- Spring kinematics and straight-path work give `17.548819925 kJ`. -/
lemma boundaryWork_in_kilojoules
    (setup : SpringPistonWaterProcess)
    (_readouts : MatchesProblemReadouts setup)
    (_properties : SatisfiesWaterPropertyModel setup)
    (_reference : MatchesReferenceSteamTableData setup)
    (_mechanics : SatisfiesLinearSpringPistonAndWorkLaws setup) :
    energyInKilojoules setup.workDoneByWater =
      701952797 / 40000000 := by
  have initialPressure :=
    initialPressure_in_kilopascals setup _properties _reference
  have finalPressure := _readouts.finalPressureKilopascals
  have springLoad := _mechanics.linearSpringLoadIncrement
  have sweptVolume := _mechanics.pistonSweptVolumeLaw
  rw [_readouts.pistonAreaSquareMeters,
    _readouts.springConstantNewtonsPerMeter] at springLoad
  rw [_readouts.pistonAreaSquareMeters] at sweptVolume
  rw [pressureInKilopascals] at initialPressure finalPressure
  rw [energyInKilojoules, _mechanics.straightPathBoundaryWork]
  norm_num at initialPressure finalPressure ⊢
  nlinarith

/-- The calibrated endpoint properties give `ΔU = 569.5 kJ`. -/
lemma internalEnergyChange_in_kilojoules
    (setup : SpringPistonWaterProcess)
    (_readouts : MatchesProblemReadouts setup)
    (_properties : SatisfiesWaterPropertyModel setup)
    (_reference : MatchesReferenceSteamTableData setup)
    (_massEnergy : SatisfiesMassSpecificPropertyLaws setup) :
    energyInKilojoules
          (setup.totalInternalEnergy .finalAtFiveHundredKilopascals) -
        energyInKilojoules
          (setup.totalInternalEnergy .initialSaturatedVapor) =
      1139 / 2 := by
  rw [_massEnergy.totalInternalEnergyFromSpecificInternalEnergy,
    _massEnergy.totalInternalEnergyFromSpecificInternalEnergy,
    _readouts.waterMassKilograms,
    _properties.finalSpecificInternalEnergy,
    _properties.initialSaturatedVaporSpecificInternalEnergy,
    _reference.finalSpecificInternalEnergy,
    _reference.initialSaturatedVaporSpecificInternalEnergy]
  norm_num

/-- Labels printed beside the four candidate heat transfers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat transfer in kilojoules printed beside each answer label. -/
def displayedHeatInKilojoules : AnswerChoice → ℝ
  | .A => 578
  | .B => 446
  | .C => 491
  | .D => 587

/-- Dataset answer metadata, deliberately absent from every theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed value is strictly closer to the calculated heat than all others. -/
def IsUniqueClosestDisplayedHeat
    (actualHeatInKilojoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualHeatInKilojoules - displayedHeatInKilojoules choice| <
      |actualHeatInKilojoules - displayedHeatInKilojoules other|

/-!
The reference properties give `ΔU = 569.5 kJ`; the linear spring path gives
`W_by = 17.548819925 kJ`; hence the first law gives
`Q = 587.048819925 kJ`.  The unique closest displayed value is `587 kJ`,
answer D.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0452:target`.
-/
theorem problem_phyx_mini_0452
    (setup : SpringPistonWaterProcess)
    (_scenario : MatchesClosedSpringPistonWaterScenario setup)
    (_figure : MatchesPrimarySpringPistonFigure setup.figure)
    (_readouts : MatchesProblemReadouts setup)
    (_physical : HasPhysicalSpringPistonParameters setup)
    (_properties : SatisfiesWaterPropertyModel setup)
    (_reference : MatchesReferenceSteamTableData setup)
    (_massEnergy : SatisfiesMassSpecificPropertyLaws setup)
    (_mechanics : SatisfiesLinearSpringPistonAndWorkLaws setup)
    (_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInKilojoules setup.heatTransferredToWater =
        23481952797 / 40000000 ∧
      IsUniqueClosestDisplayedHeat
        (energyInKilojoules setup.heatTransferredToWater) .D := by
  have work :=
    boundaryWork_in_kilojoules
      setup _readouts _properties _reference _mechanics
  have internalEnergyChange :=
    internalEnergyChange_in_kilojoules
      setup _readouts _properties _reference _massEnergy
  have heat :
      energyInKilojoules setup.heatTransferredToWater =
        23481952797 / 40000000 := by
    rw [_firstLaw.firstLaw]
    norm_num at work internalEnergyChange ⊢
    linarith
  refine ⟨heat, ?_⟩
  rw [heat]
  intro other other_ne
  cases other with
  | A => norm_num [displayedHeatInKilojoules]
  | B => norm_num [displayedHeatInKilojoules]
  | C => norm_num [displayedHeatInKilojoules]
  | D => exact (other_ne rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0452
