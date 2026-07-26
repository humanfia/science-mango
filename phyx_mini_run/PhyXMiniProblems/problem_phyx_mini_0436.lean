import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Piston lift caused by heat transfer between two helium systems

This file formalizes problem `phyx_mini_0436`.  Two helium samples are inside
an externally insulated container and exchange heat through their common thin
wall.  System 1 is in a rigid compartment.  System 2 is connected to a
vertical cylinder and supports a frictionless piston against atmospheric
pressure and gravity.

The primary image labels System 1 by `0.060 mol He, 600 K`, System 2 by
`0.030 mol He, 300 K`, and the piston by `2.0 kg piston`.  The prose additionally
specifies one atmosphere above the piston and a piston diameter of ten
centimetres.  The compartment volumes and cylinder diameter are retained as
physical parameters even though no numerical readouts for them are supplied.

All basic physical magnitudes are dimensionful Physlib quantities.  Scalar
real numbers occur only in named coherent-SI/unit readouts and in the displayed
answer values.  Physlib's current dimension basis has no amount-of-substance
coordinate, so mole amounts use dimension-one `Dimensionful` quantities, with
`amountInMoles` explicitly documenting the mole readout convention.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose and bitmap readouts;
* `UsesTextbookPhysicalConstants` gives the conventional `R` and `g` values;
* `HasPhysicalParameters` selects positive physical states;
* `ObeysTwoCompartmentThermodynamics` states ideal-gas behavior, helium heat
  capacities, the two process constraints, thermal equilibrium, and heat
  conservation across the wall;
* `ObeysFrictionlessPistonMechanics` states circular geometry, quasistatic
  vertical force balance, and swept-volume kinematics; and
* `pistonLift_matches_recordedAnswerD` concludes that the lift rounds to
  `0.050 m` and uniquely selects answer D at millimetre precision.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0436

open Dimension

/-! ## Dimensionful physical quantities and named unit readouts -/

/-- Amount of gas.  Physlib treats the mole count as dimension one. -/
abbrev AmountQuantity : Type := Dimensionful (WithDim 1 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative absolute temperature. -/
abbrev TemperatureQuantity : Type := Dimensionful (WithDim Θ𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Piston face or cylinder bore area, using Physlib's supplied area type. -/
abbrev AreaQuantity : Type := DimArea

/-- Thermodynamic pressure, using Physlib's supplied pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed heat transferred to a gas, using Physlib's supplied energy type. -/
abbrev EnergyQuantity : Type := DimEnergy

/-!
A molar gas constant or molar heat capacity has SI units
`J mol⁻¹ K⁻¹`.  Since the mole count is dimension one in the available Physlib
dimension basis, its represented dimension is energy per temperature.
-/
abbrev MolarEnergyPerTemperatureQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹)
      NNReal)

/-- Mole readout of an amount of gas. -/
def amountInMoles (amount : AmountQuantity) : ℝ :=
  ((amount UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used for the stated piston diameter. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Kelvin readout of an absolute temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Standard-atmosphere readout used in the prose. -/
def pressureInStandardAtmospheres (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- Joule readout of signed heat. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- `J mol⁻¹ K⁻¹` readout of a gas constant or molar heat capacity. -/
def molarEnergyPerTemperatureInJoulesPerMoleKelvin
    (quantity : MolarEnergyPerTemperatureQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-! ## Gas samples, process states, apparatus, and primary-figure vocabulary -/

/-- The two gas regions named in the figure. -/
inductive GasSystem where
  | system1
  | system2
  deriving DecidableEq, Repr

/-- The endpoints of the heat-transfer process. -/
inductive ProcessState where
  | initial
  | finalEquilibrium
  deriving DecidableEq, Repr

/-- Gas species specified in both figure labels. -/
inductive GasSpecies where
  | helium
  deriving DecidableEq, Repr

/-- Atomicity relevant to helium's heat capacities. -/
inductive GasAtomicity where
  | monatomic
  deriving DecidableEq, Repr

/-- Equation-of-state model used in this textbook problem. -/
inductive GasModel where
  | ideal
  deriving DecidableEq, Repr

/-- Mechanical boundary condition of each gas region. -/
inductive GasBoundaryConstraint where
  | rigidFixedVolume
  | frictionlessPistonAtConstantLoad
  deriving DecidableEq, Repr

/-- Thermal behavior of the thin wall separating the gas regions. -/
inductive SeparatingWallModel where
  | thinHeatConductingWall
  deriving DecidableEq, Repr

/-- Thermal behavior of the outside boundary of the combined apparatus. -/
inductive OuterBoundaryModel where
  | externallyInsulated
  deriving DecidableEq, Repr

/-- Direction in which the cylinder guides the piston. -/
inductive PistonGuide where
  | verticalTranslation
  deriving DecidableEq, Repr

/-- Contact model between the piston and its cylinder. -/
inductive PistonFrictionModel where
  | frictionless
  deriving DecidableEq, Repr

/-- A physical helium sample, separate from its amount and state readouts. -/
structure GasSample where
  species : GasSpecies
  atomicity : GasAtomicity
  model : GasModel

/-- Pressure, volume, and absolute temperature at one equilibrium state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  absoluteTemperature : TemperatureQuantity

/-- Components visibly distinguished in primary image `436.png`. -/
inductive FigureComponent where
  | outerContainer
  | system1GasRegion
  | system2GasRegion
  | separatingWall
  | verticalCylinder
  | piston
  deriving DecidableEq, Repr

/-- Text labels visible in primary image `436.png`. -/
inductive FigureLabel where
  | system1Name
  | system1Amount
  | system1InitialTemperature
  | system2Name
  | system2Amount
  | system2InitialTemperature
  | pistonMass
  deriving DecidableEq, Repr

/-- The physical object or region denoted by a visible label. -/
inductive FigureLabelTarget where
  | system1Gas
  | system2Gas
  | piston
  deriving DecidableEq, Repr

/-- Structured transcription of the labels and geometry in image `436.png`. -/
structure TwoCompartmentFigure where
  componentShown : FigureComponent → Bool
  labelShown : FigureLabel → Bool
  labelTarget : FigureLabel → FigureLabelTarget
  separatingWallBetweenGasRegions : Bool
  cylinderConnectedAboveSystem2 : Bool
  pistonDrawnInsideCylinder : Bool
  pistonDrawnAboveSystem2 : Bool

/-!
The full experimental setup.  In particular, `pistonLift`, all gas state
variables, and the initially unknown volumes are independent physical fields;
none is defined from an answer choice.
-/
structure HeatTransferPistonSetup where
  gas : GasSystem → GasSample
  gasAmount : GasSystem → AmountQuantity
  boundaryConstraint : GasSystem → GasBoundaryConstraint
  separatingWallModel : SeparatingWallModel
  outerBoundaryModel : OuterBoundaryModel
  state : GasSystem → ProcessState → ThermodynamicState
  heatTransferredToGas : GasSystem → EnergyQuantity
  universalGasConstant : MolarEnergyPerTemperatureQuantity
  heliumMolarHeatCapacityAtConstantVolume :
    MolarEnergyPerTemperatureQuantity
  heliumMolarHeatCapacityAtConstantPressure :
    MolarEnergyPerTemperatureQuantity
  outsideAtmosphericPressure : PressureQuantity
  gravitationalAcceleration : AccelerationQuantity
  pistonMass : MassQuantity
  pistonDiameter : LengthQuantity
  pistonFaceArea : AreaQuantity
  cylinderBoreDiameter : LengthQuantity
  cylinderBoreArea : AreaQuantity
  cylinderDiameterReadoutProvided : Bool
  compartmentVolumeReadoutProvided : GasSystem → Bool
  pistonGuide : PistonGuide
  pistonFrictionModel : PistonFrictionModel
  pistonLift : LengthQuantity
  figure : TwoCompartmentFigure

/-! ## Problem data and primary-image readouts -/

/-!
Exact transcription of the prose and primary bitmap.  The `false` fields
record that no numerical cylinder-diameter or compartment-volume readout is
printed; the corresponding physical quantities remain present in the setup.
No final temperature, final volume, or piston lift is recorded here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : HeatTransferPistonSetup) : Prop where
  bothSamplesAreHelium :
    ∀ system : GasSystem, (setup.gas system).species = .helium
  bothSamplesAreMonatomic :
    ∀ system : GasSystem, (setup.gas system).atomicity = .monatomic
  bothSamplesUseIdealGasModel :
    ∀ system : GasSystem, (setup.gas system).model = .ideal
  system1HasRigidBoundary :
    setup.boundaryConstraint .system1 = .rigidFixedVolume
  system2HasPistonBoundary :
    setup.boundaryConstraint .system2 = .frictionlessPistonAtConstantLoad
  commonWallIsThinAndConducting :
    setup.separatingWallModel = .thinHeatConductingWall
  combinedApparatusIsExternallyInsulated :
    setup.outerBoundaryModel = .externallyInsulated
  pistonMovesVertically : setup.pistonGuide = .verticalTranslation
  pistonSlidesWithoutFriction :
    setup.pistonFrictionModel = .frictionless
  system1AmountIsSixHundredthsMole :
    amountInMoles (setup.gasAmount .system1) = 6 / 100
  system2AmountIsThreeHundredthsMole :
    amountInMoles (setup.gasAmount .system2) = 3 / 100
  system1InitialTemperatureIsSixHundredKelvin :
    temperatureInKelvins
        (setup.state .system1 .initial).absoluteTemperature = 600
  system2InitialTemperatureIsThreeHundredKelvin :
    temperatureInKelvins
        (setup.state .system2 .initial).absoluteTemperature = 300
  outsidePressureIsOneAtmosphere :
    pressureInStandardAtmospheres setup.outsideAtmosphericPressure = 1
  pistonMassIsTwoKilograms :
    massInKilograms setup.pistonMass = 2
  pistonDiameterIsTenCentimeters :
    lengthInCentimeters setup.pistonDiameter = 10
  cylinderDiameterNumericallySpecified :
    setup.cylinderDiameterReadoutProvided = false
  compartmentVolumesNumericallySpecified :
    ∀ system : GasSystem,
      setup.compartmentVolumeReadoutProvided system = false
  everyFigureComponentIsShown :
    ∀ component : FigureComponent,
      setup.figure.componentShown component = true
  everyFigureLabelIsShown :
    ∀ label : FigureLabel, setup.figure.labelShown label = true
  system1LabelsTargetSystem1Gas :
    setup.figure.labelTarget .system1Name = .system1Gas ∧
      setup.figure.labelTarget .system1Amount = .system1Gas ∧
      setup.figure.labelTarget .system1InitialTemperature = .system1Gas
  system2LabelsTargetSystem2Gas :
    setup.figure.labelTarget .system2Name = .system2Gas ∧
      setup.figure.labelTarget .system2Amount = .system2Gas ∧
      setup.figure.labelTarget .system2InitialTemperature = .system2Gas
  pistonMassLabelTargetsPiston :
    setup.figure.labelTarget .pistonMass = .piston
  wallIsDrawnBetweenGasRegions :
    setup.figure.separatingWallBetweenGasRegions = true
  cylinderIsDrawnAboveSystem2 :
    setup.figure.cylinderConnectedAboveSystem2 = true
  pistonIsDrawnInCylinderAboveSystem2 :
    setup.figure.pistonDrawnInsideCylinder = true ∧
      setup.figure.pistonDrawnAboveSystem2 = true

/-!
Standard textbook constants needed to evaluate the numerical multiple-choice
answer.  These do not mention the unknown piston lift.
-/
structure UsesTextbookPhysicalConstants
    (setup : HeatTransferPistonSetup) : Prop where
  universalGasConstantInSI :
    molarEnergyPerTemperatureInJoulesPerMoleKelvin
        setup.universalGasConstant = 8314 / 1000
  terrestrialGravityInSI :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 981 / 100

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalParameters
    (setup : HeatTransferPistonSetup) : Prop where
  gasAmountsPositive :
    ∀ system : GasSystem, 0 < amountInMoles (setup.gasAmount system)
  statePressuresPositive : ∀ system : GasSystem, ∀ instant : ProcessState,
    0 < pressureInPascals (setup.state system instant).pressure
  stateVolumesPositive : ∀ system : GasSystem, ∀ instant : ProcessState,
    0 < volumeInCubicMeters (setup.state system instant).volume
  stateTemperaturesPositive : ∀ system : GasSystem, ∀ instant : ProcessState,
    0 < temperatureInKelvins
      (setup.state system instant).absoluteTemperature
  gasConstantPositive :
    0 < molarEnergyPerTemperatureInJoulesPerMoleKelvin
      setup.universalGasConstant
  heatCapacitiesPositive :
    0 < molarEnergyPerTemperatureInJoulesPerMoleKelvin
        setup.heliumMolarHeatCapacityAtConstantVolume ∧
      0 < molarEnergyPerTemperatureInJoulesPerMoleKelvin
        setup.heliumMolarHeatCapacityAtConstantPressure
  outsidePressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressure
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  pistonAndBoreDiametersPositive :
    0 < lengthInMeters setup.pistonDiameter ∧
      0 < lengthInMeters setup.cylinderBoreDiameter
  pistonAndBoreAreasPositive :
    0 < areaInSquareMeters setup.pistonFaceArea ∧
      0 < areaInSquareMeters setup.cylinderBoreArea
  pistonLiftNonnegative : 0 ≤ lengthInMeters setup.pistonLift

/-! ## Governing thermodynamics and piston mechanics -/

/-!
Thermodynamic laws for the two helium samples.  Heat is positive into a gas.
Thus conservation across the internal wall says the two signed transfers sum
to zero.  The constant-volume and constant-pressure heat relations encode the
appropriate monatomic molar heat capacities without assuming a final answer.
-/
structure ObeysTwoCompartmentThermodynamics
    (setup : HeatTransferPistonSetup) : Prop where
  finalTemperaturesAreEqual :
    (setup.state .system1 .finalEquilibrium).absoluteTemperature =
      (setup.state .system2 .finalEquilibrium).absoluteTemperature
  system1VolumeIsConstant :
    (setup.state .system1 .finalEquilibrium).volume =
      (setup.state .system1 .initial).volume
  system2PressureIsConstant :
    (setup.state .system2 .finalEquilibrium).pressure =
      (setup.state .system2 .initial).pressure
  idealGasLawInSI : ∀ system : GasSystem, ∀ instant : ProcessState,
    pressureInPascals (setup.state system instant).pressure *
        volumeInCubicMeters (setup.state system instant).volume =
      amountInMoles (setup.gasAmount system) *
        molarEnergyPerTemperatureInJoulesPerMoleKelvin
          setup.universalGasConstant *
        temperatureInKelvins
          (setup.state system instant).absoluteTemperature
  monatomicConstantVolumeHeatCapacity :
    molarEnergyPerTemperatureInJoulesPerMoleKelvin
        setup.heliumMolarHeatCapacityAtConstantVolume =
      (3 / 2 : ℝ) *
        molarEnergyPerTemperatureInJoulesPerMoleKelvin
          setup.universalGasConstant
  monatomicConstantPressureHeatCapacity :
    molarEnergyPerTemperatureInJoulesPerMoleKelvin
        setup.heliumMolarHeatCapacityAtConstantPressure =
      (5 / 2 : ℝ) *
        molarEnergyPerTemperatureInJoulesPerMoleKelvin
          setup.universalGasConstant
  heatIntoSystem1AtConstantVolume :
    energyInJoules (setup.heatTransferredToGas .system1) =
      amountInMoles (setup.gasAmount .system1) *
        molarEnergyPerTemperatureInJoulesPerMoleKelvin
          setup.heliumMolarHeatCapacityAtConstantVolume *
        (temperatureInKelvins
            (setup.state .system1 .finalEquilibrium).absoluteTemperature -
          temperatureInKelvins
            (setup.state .system1 .initial).absoluteTemperature)
  heatIntoSystem2AtConstantPressure :
    energyInJoules (setup.heatTransferredToGas .system2) =
      amountInMoles (setup.gasAmount .system2) *
        molarEnergyPerTemperatureInJoulesPerMoleKelvin
          setup.heliumMolarHeatCapacityAtConstantPressure *
        (temperatureInKelvins
            (setup.state .system2 .finalEquilibrium).absoluteTemperature -
          temperatureInKelvins
            (setup.state .system2 .initial).absoluteTemperature)
  heatIsConservedAcrossInternalWall :
    energyInJoules (setup.heatTransferredToGas .system1) +
      energyInJoules (setup.heatTransferredToGas .system2) = 0

/-!
Geometry, statics, and swept-volume kinematics of the frictionless piston.
The force balance is imposed at both equilibrium endpoints.  The piston lift
remains an unknown field related to, but not defined from, the volume change.
-/
structure ObeysFrictionlessPistonMechanics
    (setup : HeatTransferPistonSetup) : Prop where
  pistonFaceIsCircular :
    areaInSquareMeters setup.pistonFaceArea =
      Real.pi * (lengthInMeters setup.pistonDiameter / 2) ^ 2
  cylinderBoreIsCircular :
    areaInSquareMeters setup.cylinderBoreArea =
      Real.pi * (lengthInMeters setup.cylinderBoreDiameter / 2) ^ 2
  pistonFitsCylinderBore :
    setup.pistonFaceArea = setup.cylinderBoreArea
  quasistaticVerticalForceBalance : ∀ instant : ProcessState,
    pressureInPascals (setup.state .system2 instant).pressure *
        areaInSquareMeters setup.pistonFaceArea =
      pressureInPascals setup.outsideAtmosphericPressure *
          areaInSquareMeters setup.pistonFaceArea +
        massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration
  system2SweptVolumeEqualsAreaTimesLift :
    volumeInCubicMeters
          (setup.state .system2 .finalEquilibrium).volume -
        volumeInCubicMeters (setup.state .system2 .initial).volume =
      areaInSquareMeters setup.pistonFaceArea *
        lengthInMeters setup.pistonLift

/-! ## Derived intermediate and recorded multiple-choice conclusion -/

/-- The equilibrium temperature derived from the heat-capacity balance. -/
theorem finalEquilibriumTemperatureInKelvins
    (setup : HeatTransferPistonSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hConstants : UsesTextbookPhysicalConstants setup)
    (hPhysical : HasPhysicalParameters setup)
    (hThermo : ObeysTwoCompartmentThermodynamics setup) :
    temperatureInKelvins
          (setup.state .system1 .finalEquilibrium).absoluteTemperature =
        5100 / 11 ∧
      temperatureInKelvins
          (setup.state .system2 .finalEquilibrium).absoluteTemperature =
        5100 / 11 := by
  have hFinalTemperatures :
      temperatureInKelvins
          (setup.state .system1 .finalEquilibrium).absoluteTemperature =
        temperatureInKelvins
          (setup.state .system2 .finalEquilibrium).absoluteTemperature :=
    congrArg temperatureInKelvins hThermo.finalTemperaturesAreEqual
  have hHeat1 := hThermo.heatIntoSystem1AtConstantVolume
  have hHeat2 := hThermo.heatIntoSystem2AtConstantPressure
  rw [hData.system1AmountIsSixHundredthsMole,
    hThermo.monatomicConstantVolumeHeatCapacity,
    hData.system1InitialTemperatureIsSixHundredKelvin] at hHeat1
  rw [hData.system2AmountIsThreeHundredthsMole,
    hThermo.monatomicConstantPressureHeatCapacity,
    hData.system2InitialTemperatureIsThreeHundredKelvin,
    ← hFinalTemperatures] at hHeat2
  have hGasConstantPositive := hPhysical.gasConstantPositive
  have hGasConstantValue := hConstants.universalGasConstantInSI
  constructor <;>
    nlinarith [hThermo.heatIsConservedAcrossInternalWall, hGasConstantValue]

/-- The four lift values displayed in the problem, in metres. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre value printed beside each multiple-choice label. -/
def displayedLiftInMeters : AnswerChoice → ℝ
  | .A => 150 / 1000
  | .B => 98 / 1000
  | .C => 20 / 1000
  | .D => 50 / 1000

/-- Agreement after rounding a metre value to the nearest millimetre. -/
def agreesToNearestMillimeter (measured displayed : ℝ) : Prop :=
  |measured - displayed| < 1 / 2000

/-- The answer label recorded by the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The requested piston lift is approximately `0.050 m`: it agrees with choice D
to the precision displayed in the source, and no other displayed choice agrees
at that precision.  This numerical conclusion appears only in the theorem.
-/
theorem pistonLift_matches_recordedAnswerD
    (setup : HeatTransferPistonSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hConstants : UsesTextbookPhysicalConstants setup)
    (hPhysical : HasPhysicalParameters setup)
    (hThermo : ObeysTwoCompartmentThermodynamics setup)
    (hMechanics : ObeysFrictionlessPistonMechanics setup) :
    agreesToNearestMillimeter
        (lengthInMeters setup.pistonLift)
        (displayedLiftInMeters recordedAnswerChoice) ∧
      ∀ choice : AnswerChoice,
        agreesToNearestMillimeter
            (lengthInMeters setup.pistonLift)
            (displayedLiftInMeters choice) →
          choice = recordedAnswerChoice := by
  have hFinalTemperature :=
    finalEquilibriumTemperatureInKelvins
      setup hData hConstants hPhysical hThermo
  have hOutsidePressureInPascals :
      pressureInPascals setup.outsideAtmosphericPressure = 101325 := by
    have hAtmospheres := hData.outsidePressureIsOneAtmosphere
    simp [pressureInStandardAtmospheres, pressureInPascals,
      DimPressure.standardAtmosphere, DimPressure.pascal,
      CarriesDimension.toDimensionful_apply_apply] at hAtmospheres ⊢
    linarith
  have hPistonDiameterInMeters :
      lengthInMeters setup.pistonDiameter = 1 / 10 := by
    have hDiameter := hData.pistonDiameterIsTenCentimeters
    simp [lengthInCentimeters] at hDiameter
    linarith
  have hPistonArea :
      areaInSquareMeters setup.pistonFaceArea = Real.pi / 400 := by
    calc
      areaInSquareMeters setup.pistonFaceArea =
          Real.pi * (lengthInMeters setup.pistonDiameter / 2) ^ 2 :=
        hMechanics.pistonFaceIsCircular
      _ = Real.pi / 400 := by
        rw [hPistonDiameterInMeters]
        ring
  have hPressureConstant :
      pressureInPascals
          (setup.state .system2 .finalEquilibrium).pressure =
        pressureInPascals (setup.state .system2 .initial).pressure :=
    congrArg pressureInPascals hThermo.system2PressureIsConstant
  have hIdealInitial := hThermo.idealGasLawInSI .system2 .initial
  have hIdealFinal :=
    hThermo.idealGasLawInSI .system2 .finalEquilibrium
  rw [hData.system2AmountIsThreeHundredthsMole,
    hConstants.universalGasConstantInSI,
    hData.system2InitialTemperatureIsThreeHundredKelvin] at hIdealInitial
  rw [hPressureConstant, hData.system2AmountIsThreeHundredthsMole,
    hConstants.universalGasConstantInSI, hFinalTemperature.2] at hIdealFinal
  have hPressureTimesVolumeChange :
      pressureInPascals (setup.state .system2 .initial).pressure *
          (volumeInCubicMeters
                (setup.state .system2 .finalEquilibrium).volume -
            volumeInCubicMeters (setup.state .system2 .initial).volume) =
        (3 / 100) * (8314 / 1000) * (5100 / 11 - 300) := by
    nlinarith [hIdealInitial, hIdealFinal]
  rw [hMechanics.system2SweptVolumeEqualsAreaTimesLift] at hPressureTimesVolumeChange
  have hForceBalance :=
    hMechanics.quasistaticVerticalForceBalance .initial
  rw [hOutsidePressureInPascals, hData.pistonMassIsTwoKilograms,
    hConstants.terrestrialGravityInSI] at hForceBalance
  have hLiftEquation :
      (101325 * areaInSquareMeters setup.pistonFaceArea +
            2 * (981 / 100)) *
          lengthInMeters setup.pistonLift =
        (3 / 100) * (8314 / 1000) * (5100 / 11 - 300) := by
    calc
      (101325 * areaInSquareMeters setup.pistonFaceArea +
              2 * (981 / 100)) *
            lengthInMeters setup.pistonLift =
          (pressureInPascals (setup.state .system2 .initial).pressure *
              areaInSquareMeters setup.pistonFaceArea) *
            lengthInMeters setup.pistonLift := by
              rw [hForceBalance]
      _ = pressureInPascals (setup.state .system2 .initial).pressure *
            (areaInSquareMeters setup.pistonFaceArea *
              lengthInMeters setup.pistonLift) := by ring
      _ = (3 / 100) * (8314 / 1000) * (5100 / 11 - 300) :=
        hPressureTimesVolumeChange
  rw [hPistonArea] at hLiftEquation
  have hLiftEquation' :
      (101325 * (Real.pi / 400) + 981 / 50) *
          lengthInMeters setup.pistonLift =
        (3 / 100) * (8314 / 1000) * (5100 / 11 - 300) := by
    convert hLiftEquation using 1
    all_goals ring
  have hCosLower : 0 < Real.cos (39 / 25 : ℝ) := by
    have hBound :=
      Real.cos_bound (x := (13 / 50 : ℝ))
        (by norm_num [abs_of_nonneg])
    rw [abs_le] at hBound
    have hCos0Positive : 0 < Real.cos (13 / 50 : ℝ) :=
      Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])
    have hCos1Positive : 0 < Real.cos (13 / 25 : ℝ) :=
      Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])
    have hDouble :
        Real.cos (13 / 25 : ℝ) =
          2 * Real.cos (13 / 50 : ℝ) ^ 2 - 1 := by
      rw [show (13 / 25 : ℝ) = 2 * (13 / 50) by norm_num,
        Real.cos_two_mul]
    have hTriple :
        Real.cos (39 / 25 : ℝ) =
          4 * Real.cos (13 / 25 : ℝ) ^ 3 -
            3 * Real.cos (13 / 25 : ℝ) := by
      rw [show (39 / 25 : ℝ) = 3 * (13 / 25) by norm_num,
        Real.cos_three_mul]
    have hCos0 :
        (965961 / 1000000 : ℝ) < Real.cos (13 / 50 : ℝ) := by
      norm_num [abs_of_nonneg] at hBound ⊢
      linarith
    have hCos0Squared :
        (965961 / 1000000 : ℝ) ^ 2 < Real.cos (13 / 50 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hCos0Positive.le).2 hCos0
    have hCos1 :
        (86615 / 100000 : ℝ) < Real.cos (13 / 25 : ℝ) := by nlinarith
    have hCos1Squared :
        (86615 / 100000 : ℝ) ^ 2 < Real.cos (13 / 25 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hCos1Positive.le).2 hCos1
    rw [hTriple]
    have hFactorPositive :
        0 < 4 * Real.cos (13 / 25 : ℝ) ^ 2 - 3 := by nlinarith
    nlinarith [mul_pos hCos1Positive hFactorPositive]
  have hPiLower : (78 / 25 : ℝ) < Real.pi := by
    by_contra hNotLower
    have hPiAtMost : Real.pi ≤ (78 / 25 : ℝ) :=
      le_of_not_gt hNotLower
    have hPastPiOverTwo :
        Real.pi / 2 ≤ (39 / 25 : ℝ) := by linarith
    have hBeforeThreePiOverTwo :
        (39 / 25 : ℝ) ≤ Real.pi + Real.pi / 2 := by
      nlinarith [Real.two_le_pi]
    have hCosNonpositive :=
      Real.cos_nonpos_of_pi_div_two_le_of_le
        hPastPiOverTwo hBeforeThreePiOverTwo
    linarith
  have hCosUpper : Real.cos (317 / 200 : ℝ) < 0 := by
    have hBound :=
      Real.cos_bound (x := (317 / 1200 : ℝ))
        (by norm_num [abs_of_nonneg])
    rw [abs_le] at hBound
    have hCos0Positive : 0 < Real.cos (317 / 1200 : ℝ) :=
      Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])
    have hCos1Positive : 0 < Real.cos (317 / 600 : ℝ) :=
      Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])
    have hDouble :
        Real.cos (317 / 600 : ℝ) =
          2 * Real.cos (317 / 1200 : ℝ) ^ 2 - 1 := by
      rw [show (317 / 600 : ℝ) = 2 * (317 / 1200) by norm_num,
        Real.cos_two_mul]
    have hTriple :
        Real.cos (317 / 200 : ℝ) =
          4 * Real.cos (317 / 600 : ℝ) ^ 3 -
            3 * Real.cos (317 / 600 : ℝ) := by
      rw [show (317 / 200 : ℝ) = 3 * (317 / 600) by norm_num,
        Real.cos_three_mul]
    have hCos0 :
        Real.cos (317 / 1200 : ℝ) < (96537 / 100000 : ℝ) := by
      norm_num [abs_of_nonneg] at hBound ⊢
      linarith
    have hCos0Squared :
        Real.cos (317 / 1200 : ℝ) ^ 2 < (96537 / 100000 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hCos0Positive.le (by norm_num)).2 hCos0
    have hCos1 :
        Real.cos (317 / 600 : ℝ) < (8639 / 10000 : ℝ) := by nlinarith
    have hCos1Squared :
        Real.cos (317 / 600 : ℝ) ^ 2 < (8639 / 10000 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hCos1Positive.le (by norm_num)).2 hCos1
    rw [hTriple]
    have hFactorNegative :
        4 * Real.cos (317 / 600 : ℝ) ^ 2 - 3 < 0 := by nlinarith
    nlinarith [mul_neg_of_pos_of_neg hCos1Positive hFactorNegative]
  have hPiUpper : Real.pi < (317 / 100 : ℝ) := by
    by_contra hNotUpper
    have hPiAtLeast : (317 / 100 : ℝ) ≤ Real.pi :=
      le_of_not_gt hNotUpper
    have hAfterNegativePiOverTwo :
        -(Real.pi / 2) ≤ (317 / 200 : ℝ) := by
      nlinarith [Real.pi_pos]
    have hBeforePiOverTwo :
        (317 / 200 : ℝ) ≤ Real.pi / 2 := by linarith
    have hCosNonnegative :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        hAfterNegativePiOverTwo hBeforePiOverTwo
    linarith
  let lift : ℝ := lengthInMeters setup.pistonLift
  have hLiftEquationScalar :
      (101325 * (Real.pi / 400) + 981 / 50) * lift =
        (3 / 100) * (8314 / 1000) * (5100 / 11 - 300) := by
    simpa [lift] using hLiftEquation'
  have hLiftNonnegative : 0 ≤ lift := by
    simpa [lift] using hPhysical.pistonLiftNonnegative
  have hLiftPositive : 0 < lift := by
    by_contra hNotPositive
    have hLiftZero : lift = 0 :=
      le_antisymm (le_of_not_gt hNotPositive) hLiftNonnegative
    rw [hLiftZero] at hLiftEquationScalar
    norm_num at hLiftEquationScalar
  have hLiftBounds :
      (99 / 2000 : ℝ) < lift ∧ lift < 101 / 2000 := by
    constructor
    · by_contra hNotLower
      have hLiftAtMost : lift ≤ (99 / 2000 : ℝ) :=
        le_of_not_gt hNotLower
      have hPiLiftUpper :
          Real.pi * lift < (317 / 100 : ℝ) * (99 / 2000) := calc
        Real.pi * lift < (317 / 100 : ℝ) * lift :=
          mul_lt_mul_of_pos_right hPiUpper hLiftPositive
        _ ≤ (317 / 100 : ℝ) * (99 / 2000) :=
          mul_le_mul_of_nonneg_left hLiftAtMost (by norm_num)
      nlinarith only [hLiftEquationScalar, hLiftAtMost, hPiLiftUpper]
    · by_contra hNotUpper
      have hLiftAtLeast : (101 / 2000 : ℝ) ≤ lift :=
        le_of_not_gt hNotUpper
      have hPiLiftLower :
          (78 / 25 : ℝ) * (101 / 2000) < Real.pi * lift := calc
        (78 / 25 : ℝ) * (101 / 2000) <
            Real.pi * (101 / 2000) :=
          mul_lt_mul_of_pos_right hPiLower (by norm_num)
        _ ≤ Real.pi * lift :=
          mul_le_mul_of_nonneg_left hLiftAtLeast Real.pi_nonneg
      nlinarith only [hLiftEquationScalar, hLiftAtLeast, hPiLiftLower]
  constructor
  · simp only [agreesToNearestMillimeter, recordedAnswerChoice,
      displayedLiftInMeters]
    change |lift - 50 / 1000| < 1 / 2000
    rw [abs_lt]
    constructor <;> norm_num <;> linarith [hLiftBounds.1, hLiftBounds.2]
  · intro choice hChoice
    change agreesToNearestMillimeter lift (displayedLiftInMeters choice) at hChoice
    cases choice with
    | A =>
        simp only [agreesToNearestMillimeter, displayedLiftInMeters] at hChoice
        rw [abs_lt] at hChoice
        norm_num at hChoice
        exfalso
        linarith only [hChoice.1, hLiftBounds.2]
    | B =>
        simp only [agreesToNearestMillimeter, displayedLiftInMeters] at hChoice
        rw [abs_lt] at hChoice
        norm_num at hChoice
        exfalso
        linarith only [hChoice.1, hLiftBounds.2]
    | C =>
        simp only [agreesToNearestMillimeter, displayedLiftInMeters] at hChoice
        rw [abs_lt] at hChoice
        norm_num at hChoice
        exfalso
        linarith only [hChoice.2, hLiftBounds.1]
    | D =>
        rfl

end PhyXMiniProblems.ProblemPhyXMini0436
