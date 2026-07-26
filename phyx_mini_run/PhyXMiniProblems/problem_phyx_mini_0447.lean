import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0447

open Dimension

/-!
# Cooling air beneath a piston initially held by upper stops

A closed sample of air starts at `250 kPa` and `300 °C` below a `50 kg`
piston.  The piston has diameter `0.1 m` and initially presses against upper
stops.  The primary figure gives an initial gas-column height of `25 cm`,
labels the atmosphere above the piston by `P₀`, and shows gravity downward.
The atmospheric pressure is `100 kPa`; cooling continues until the air reaches
the ambient temperature `20 °C`.

The piston first remains at the stops while pressure falls.  It then descends
under the constant load due to atmospheric pressure and its own weight.
Dimensionful physical quantities are kept distinct from their explicitly
named SI readouts.  In particular, the piston drop is an independent physical
observable and is not defined to equal the recorded multiple-choice value.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the chosen unit system. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude, with dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read a Physlib pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a Physlib pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-!
Read a Physlib absolute temperature in kelvin.  The storage unit is explicit
because `Temperature` stores a nonnegative value in an arbitrary
zero-preserving temperature unit.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- The exact Celsius-zero offset, `273.15 K`. -/
def celsiusZeroInKelvin : ℝ := 5463 / 20

/-- Affine Celsius readout of a physical absolute temperature. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - celsiusZeroInKelvin

/-! ## Process states, apparatus, and primary-figure vocabulary -/

/-- States separating the fixed-height and freely descending phases. -/
inductive ProcessState where
  | initialAtStops
  | onsetOfDescent
  | finalAtAmbient
  deriving DecidableEq, Fintype, Repr

/-- The material confined below the piston. -/
inductive EnclosedGas where
  | air
  | other
  deriving DecidableEq, Repr

/-- Orientation of the cylinder axis. -/
inductive CylinderOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Cross-sectional idealization used for the cylinder volume. -/
inductive CylinderCrossSection where
  | circular
  | other
  deriving DecidableEq, Repr

/-- Mechanical support regime of the piston. -/
inductive PistonSupportRegime where
  | pressingAgainstUpperStops
  | freelySlidingStaticEquilibrium
  | other
  deriving DecidableEq, Repr

/-- Thermal process described by the problem. -/
inductive ThermalProcess where
  | coolingByHeatTransferToAmbient
  | other
  deriving DecidableEq, Repr

/-- Directions appearing in the vertical cross-sectional figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied raster image. -/
inductive FigureObject where
  | cylinderWalls
  | piston
  | enclosedAirRegion
  | upperStops
  | gasHeightArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal labels visible in the supplied raster image. -/
inductive FigureLabel where
  | atmosphericPressureP0
  | gravityG
  | air
  | height25Centimeters
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from the primary image.  Numerical figure
evidence is connected to the initial thermodynamic state below, not encoded as
a value of the requested displacement.
-/
structure PistonCylinderFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  pistonIsHorizontal : Bool
  airIsBelowPiston : Bool
  atmosphereIsAbovePiston : Bool
  p0LabelDenotesAtmosphericPressure : Bool
  gravityArrowDirection : VerticalDirection
  heightArrowSpansInitialGasColumn : Bool
  pistonIsDrawnAtUpperStops : Bool

/-- A gas state together with its cylinder-height observable. -/
structure GasState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  gasColumnHeight : LengthQuantity

/-!
Independent apparatus parameters and endpoint observables.  The amount of air
has an abstract physical carrier and only an explicitly calibrated mole
readout.  Neither `pistonDrop` nor the final height is assigned a numerical
answer here.
-/
structure CoolingPistonSetup (AmountOfSubstance : Type) where
  enclosedGas : EnclosedGas
  cylinderOrientation : CylinderOrientation
  crossSectionShape : CylinderCrossSection
  supportRegime : ProcessState → PistonSupportRegime
  thermalProcess : ThermalProcess
  gasSampleIsClosed : Bool
  pistonMovesWithoutFriction : Bool
  cylinderInnerDiameter : LengthQuantity
  pistonCrossSectionalArea : DimArea
  pistonMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  pistonWeight : ForceQuantity
  atmosphericPressureP0 : DimPressure
  ambientTemperature : Temperature
  temperatureStorageUnit : TemperatureUnit
  gasStateAt : ProcessState → GasState
  initialUpperStopReaction : ForceQuantity
  pistonDrop : LengthQuantity
  amountOfAir : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  universalGasConstantJoulesPerMoleKelvin : ℝ
  figure : PistonCylinderFigure

/-- Mole readout of the fixed amount of enclosed air. -/
def airAmountInMoles
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : ℝ :=
  setup.amountInMoles setup.amountOfAir

/-- Kelvin readout of the air temperature at a modeled state. -/
def gasTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance)
    (state : ProcessState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.gasStateAt state).temperature

/-- Celsius readout of the air temperature at a modeled state. -/
def gasTemperatureInDegreesCelsius
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance)
    (state : ProcessState) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    (setup.gasStateAt state).temperature

/-- Kelvin readout of the ambient temperature. -/
def ambientTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit setup.ambientTemperature

/-- Celsius readout of the ambient temperature. -/
def ambientTemperatureInDegreesCelsius
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    setup.ambientTemperature

/-! ## Assumptions: scenario, stated data, figure evidence, and laws -/

/-- Qualitative physical conditions stated or implied by the problem. -/
structure MatchesCoolingPistonScenario
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : Prop where
  containsAir : setup.enclosedGas = .air
  verticalCylinder : setup.cylinderOrientation = .vertical
  circularCylinder : setup.crossSectionShape = .circular
  initiallyPressesAgainstStops :
    setup.supportRegime .initialAtStops = .pressingAgainstUpperStops
  releasedPistonIsFreelySupported :
    setup.supportRegime .onsetOfDescent = .freelySlidingStaticEquilibrium
  finalPistonIsFreelySupported :
    setup.supportRegime .finalAtAmbient = .freelySlidingStaticEquilibrium
  statedCoolingProcess :
    setup.thermalProcess = .coolingByHeatTransferToAmbient
  closedAirSample : setup.gasSampleIsClosed = true
  negligiblePistonFriction : setup.pistonMovesWithoutFriction = true

/-!
Numerical data stated in the prose.  The requested drop and final gas-column
height are deliberately absent.
-/
structure MatchesProblemReadouts
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : Prop where
  initialGasPressureKilopascals :
    pressureInKilopascals
        (setup.gasStateAt .initialAtStops).pressure = 250
  initialGasTemperatureCelsius :
    gasTemperatureInDegreesCelsius setup .initialAtStops = 300
  pistonMassKilograms : massInKilograms setup.pistonMass = 50
  pistonDiameterMeters : lengthInMeters setup.cylinderInnerDiameter = 1 / 10
  atmosphericPressureKilopascals :
    pressureInKilopascals setup.atmosphericPressureP0 = 100
  ambientTemperatureCelsius :
    ambientTemperatureInDegreesCelsius setup = 20

/-!
Primary-raster evidence: `P₀` is above the piston, `g` points downward, air is
below the piston, the piston touches the upper stops, and the height arrow
reads `25 cm`.  The image contains no final displacement readout.
-/
structure MatchesSuppliedPistonCylinderFigure
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : Prop where
  everyNamedObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyLiteralLabelShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  horizontalPiston : setup.figure.pistonIsHorizontal = true
  airBelowPiston : setup.figure.airIsBelowPiston = true
  atmosphereAbovePiston : setup.figure.atmosphereIsAbovePiston = true
  p0IsAtmosphericPressure :
    setup.figure.p0LabelDenotesAtmosphericPressure = true
  downwardGravityArrow : setup.figure.gravityArrowDirection = .downward
  heightArrowSpansInitialAir :
    setup.figure.heightArrowSpansInitialGasColumn = true
  pistonShownAtUpperStops : setup.figure.pistonIsDrawnAtUpperStops = true
  initialGasColumnHeightCentimeters :
    lengthInCentimeters
        (setup.gasStateAt .initialAtStops).gasColumnHeight = 25

/-- Independent textbook constants used by the physical prediction. -/
structure UsesTextbookPhysicalConstants
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 981 / 100
  universalGasConstantSI :
    setup.universalGasConstantJoulesPerMoleKelvin = 8314 / 1000

/-- Positivity and nondegeneracy conditions selecting physical states. -/
structure HasPhysicalCoolingPistonParameters
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : Prop where
  diameterPositive : 0 < lengthInMeters setup.cylinderInnerDiameter
  areaPositive : 0 < areaInSquareMeters setup.pistonCrossSectionalArea
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  pistonWeightPositive : 0 < forceInNewtons setup.pistonWeight
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericPressureP0
  ambientTemperaturePositive : 0 < ambientTemperatureInKelvin setup
  gasPressurePositive : ∀ state,
    0 < pressureInPascals (setup.gasStateAt state).pressure
  gasVolumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.gasStateAt state).volume
  gasTemperaturePositive : ∀ state,
    0 < gasTemperatureInKelvin setup state
  gasColumnHeightPositive : ∀ state,
    0 < lengthInMeters (setup.gasStateAt state).gasColumnHeight
  stopReactionPositive : 0 < forceInNewtons setup.initialUpperStopReaction
  airAmountPositive : 0 < airAmountInMoles setup
  universalGasConstantPositive :
    0 < setup.universalGasConstantJoulesPerMoleKelvin

/-!
The event named in the question: cooling continues until the air reaches the
ambient absolute temperature.  This fixes when displacement is measured, not
the value of that displacement.
-/
structure ReachesAmbientTemperature
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : Prop where
  finalAirTemperatureEqualsAmbient :
    gasTemperatureInKelvin setup .finalAtAmbient =
      ambientTemperatureInKelvin setup

/-!
Governing geometry, mechanics, thermodynamics, and phase behavior:

* the piston face is circular and gas volume is area times column height;
* piston weight is `m g`;
* while the upper stops engage, the height remains fixed and the stops supply
  the excess downward reaction;
* after release, static force balance fixes gas pressure from atmospheric
  loading plus piston weight;
* the same closed amount of ideal air obeys `P V = n R T` at every state;
* the independent piston-drop observable is the decrease in gas height.

No field assigns `5.3 cm` or an answer label to the piston drop.
-/
structure SatisfiesCoolingPistonLaws
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance) : Prop where
  circularCrossSection :
    areaInSquareMeters setup.pistonCrossSectionalArea =
      Real.pi * (lengthInMeters setup.cylinderInnerDiameter / 2) ^ 2
  cylindricalGasVolume : ∀ state,
    volumeInCubicMeters (setup.gasStateAt state).volume =
      areaInSquareMeters setup.pistonCrossSectionalArea *
        lengthInMeters (setup.gasStateAt state).gasColumnHeight
  pistonWeightLaw :
    forceInNewtons setup.pistonWeight =
      massInKilograms setup.pistonMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  fixedHeightUntilRelease :
    (setup.gasStateAt .onsetOfDescent).gasColumnHeight =
      (setup.gasStateAt .initialAtStops).gasColumnHeight
  initialStopForceBalance :
    pressureInPascals (setup.gasStateAt .initialAtStops).pressure *
        areaInSquareMeters setup.pistonCrossSectionalArea =
      pressureInPascals setup.atmosphericPressureP0 *
          areaInSquareMeters setup.pistonCrossSectionalArea +
        forceInNewtons setup.pistonWeight +
          forceInNewtons setup.initialUpperStopReaction
  freePistonForceBalanceDuringDescent :
    ∀ state, state = .onsetOfDescent ∨ state = .finalAtAmbient →
      pressureInPascals (setup.gasStateAt state).pressure *
          areaInSquareMeters setup.pistonCrossSectionalArea =
        pressureInPascals setup.atmosphericPressureP0 *
            areaInSquareMeters setup.pistonCrossSectionalArea +
          forceInNewtons setup.pistonWeight
  idealGasEquation : ∀ state,
    pressureInPascals (setup.gasStateAt state).pressure *
        volumeInCubicMeters (setup.gasStateAt state).volume =
      airAmountInMoles setup *
        setup.universalGasConstantJoulesPerMoleKelvin *
          gasTemperatureInKelvin setup state
  pistonDropIsHeightDecrease :
    lengthInMeters setup.pistonDrop =
      lengthInMeters
          (setup.gasStateAt .initialAtStops).gasColumnHeight -
        lengthInMeters
          (setup.gasStateAt .finalAtAmbient).gasColumnHeight

/-! ## Derived relation and multiple-choice target -/

/-!
Combining the endpoint ideal-gas equations, cylindrical geometry, final
free-piston force balance, and the ambient-temperature event gives this
general displacement relation.  It contains no problem-specific answer value.
-/
theorem pistonDropFormulaInMeters
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance)
    (_physical : HasPhysicalCoolingPistonParameters setup)
    (_ambient : ReachesAmbientTemperature setup)
    (_laws : SatisfiesCoolingPistonLaws setup) :
    lengthInMeters setup.pistonDrop =
      lengthInMeters
          (setup.gasStateAt .initialAtStops).gasColumnHeight -
        (lengthInMeters
              (setup.gasStateAt .initialAtStops).gasColumnHeight *
            pressureInPascals
              (setup.gasStateAt .initialAtStops).pressure *
            ambientTemperatureInKelvin setup *
            areaInSquareMeters setup.pistonCrossSectionalArea) /
          (gasTemperatureInKelvin setup .initialAtStops *
            (pressureInPascals setup.atmosphericPressureP0 *
                areaInSquareMeters setup.pistonCrossSectionalArea +
              forceInNewtons setup.pistonWeight)) := by
  have initialIdealGas :=
    _laws.idealGasEquation ProcessState.initialAtStops
  have finalIdealGas :=
    _laws.idealGasEquation ProcessState.finalAtAmbient
  rw [_laws.cylindricalGasVolume] at initialIdealGas finalIdealGas
  rw [_ambient.finalAirTemperatureEqualsAmbient] at finalIdealGas
  have finalForceBalance :=
    _laws.freePistonForceBalanceDuringDescent
      ProcessState.finalAtAmbient (Or.inr rfl)
  have crossMultipliedIdealGas :
      (pressureInPascals
            (setup.gasStateAt .finalAtAmbient).pressure *
          (areaInSquareMeters setup.pistonCrossSectionalArea *
            lengthInMeters
              (setup.gasStateAt .finalAtAmbient).gasColumnHeight)) *
          gasTemperatureInKelvin setup .initialAtStops =
        (pressureInPascals
            (setup.gasStateAt .initialAtStops).pressure *
          (areaInSquareMeters setup.pistonCrossSectionalArea *
            lengthInMeters
              (setup.gasStateAt .initialAtStops).gasColumnHeight)) *
          ambientTemperatureInKelvin setup := by
    calc
      _ = (airAmountInMoles setup *
              setup.universalGasConstantJoulesPerMoleKelvin *
                ambientTemperatureInKelvin setup) *
            gasTemperatureInKelvin setup .initialAtStops := by
          rw [finalIdealGas]
      _ = (airAmountInMoles setup *
              setup.universalGasConstantJoulesPerMoleKelvin *
                gasTemperatureInKelvin setup .initialAtStops) *
            ambientTemperatureInKelvin setup := by
          ring
      _ = _ := by
          rw [← initialIdealGas]
  have denominatorPositive :
      0 <
        gasTemperatureInKelvin setup .initialAtStops *
          (pressureInPascals setup.atmosphericPressureP0 *
              areaInSquareMeters setup.pistonCrossSectionalArea +
            forceInNewtons setup.pistonWeight) := by
    exact mul_pos (_physical.gasTemperaturePositive .initialAtStops)
      (add_pos
        (mul_pos _physical.atmosphericPressurePositive
          _physical.areaPositive)
        _physical.pistonWeightPositive)
  rw [_laws.pistonDropIsHeightDecrease]
  congr 1
  apply (eq_div_iff (ne_of_gt denominatorPositive)).2
  calc
    lengthInMeters
          (setup.gasStateAt .finalAtAmbient).gasColumnHeight *
        (gasTemperatureInKelvin setup .initialAtStops *
          (pressureInPascals setup.atmosphericPressureP0 *
              areaInSquareMeters setup.pistonCrossSectionalArea +
            forceInNewtons setup.pistonWeight)) =
      (pressureInPascals
            (setup.gasStateAt .finalAtAmbient).pressure *
          (areaInSquareMeters setup.pistonCrossSectionalArea *
            lengthInMeters
              (setup.gasStateAt .finalAtAmbient).gasColumnHeight)) *
        gasTemperatureInKelvin setup .initialAtStops := by
          calc
            _ = lengthInMeters
                    (setup.gasStateAt .finalAtAmbient).gasColumnHeight *
                  gasTemperatureInKelvin setup .initialAtStops *
                  (pressureInPascals setup.atmosphericPressureP0 *
                      areaInSquareMeters setup.pistonCrossSectionalArea +
                    forceInNewtons setup.pistonWeight) := by
                  ring
            _ = lengthInMeters
                    (setup.gasStateAt .finalAtAmbient).gasColumnHeight *
                  gasTemperatureInKelvin setup .initialAtStops *
                  (pressureInPascals
                      (setup.gasStateAt .finalAtAmbient).pressure *
                    areaInSquareMeters setup.pistonCrossSectionalArea) := by
                  rw [← finalForceBalance]
            _ = _ := by
                  ring
    _ = _ := crossMultipliedIdealGas
    _ = lengthInMeters
            (setup.gasStateAt .initialAtStops).gasColumnHeight *
          pressureInPascals
            (setup.gasStateAt .initialAtStops).pressure *
          ambientTemperatureInKelvin setup *
          areaInSquareMeters setup.pistonCrossSectionalArea := by
          ring

/-- Labels of the four answers printed in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Piston drop in centimetres printed beside each answer label. -/
def displayedDropCentimeters : AnswerChoice → ℝ
  | .A => 1 / 4
  | .B => 39 / 5
  | .C => 16 / 5
  | .D => 53 / 10

/-- Answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The modeled drop rounds to a display given to the nearest `0.1 cm`. -/
def RoundsToNearestTenthCentimeter
    (exactCentimeters displayedCentimeters : ℝ) : Prop :=
  |exactCentimeters - displayedCentimeters| < 1 / 20

/-- A chosen display is strictly closer than every alternative display. -/
def IsUniqueClosestChoice
    (predictedCentimeters : ℝ) (chosen : AnswerChoice) : Prop :=
  ∀ other, other ≠ chosen →
    |predictedCentimeters - displayedDropCentimeters chosen| <
      |predictedCentimeters - displayedDropCentimeters other|

/-!
For the stated prose data, primary-image height, textbook constants, endpoint
event, and governing laws, the piston drop rounds to `5.3 cm` and uniquely
selects the recorded answer D.

Blueprint label: `thm:physics:phyx_mini_0447:target`.
-/
theorem problem_phyx_mini_0447
    {AmountOfSubstance : Type}
    (setup : CoolingPistonSetup AmountOfSubstance)
    (_scenario : MatchesCoolingPistonScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedPistonCylinderFigure setup)
    (_constants : UsesTextbookPhysicalConstants setup)
    (_physical : HasPhysicalCoolingPistonParameters setup)
    (_ambient : ReachesAmbientTemperature setup)
    (_laws : SatisfiesCoolingPistonLaws setup) :
    RoundsToNearestTenthCentimeter
        (lengthInCentimeters setup.pistonDrop)
        (displayedDropCentimeters recordedDatasetAnswer) ∧
      IsUniqueClosestChoice
        (lengthInCentimeters setup.pistonDrop) recordedDatasetAnswer := by
  have initialPressurePascals :
      pressureInPascals
          (setup.gasStateAt .initialAtStops).pressure = 250000 := by
    have stated := _readouts.initialGasPressureKilopascals
    norm_num [pressureInKilopascals] at stated ⊢
    linarith
  have atmosphericPressurePascals :
      pressureInPascals setup.atmosphericPressureP0 = 100000 := by
    have stated := _readouts.atmosphericPressureKilopascals
    norm_num [pressureInKilopascals] at stated ⊢
    linarith
  have initialTemperatureKelvin :
      gasTemperatureInKelvin setup .initialAtStops = 11463 / 20 := by
    have stated := _readouts.initialGasTemperatureCelsius
    change
      gasTemperatureInKelvin setup .initialAtStops - 5463 / 20 = 300
        at stated
    norm_num at stated ⊢
    linarith
  have ambientTemperatureKelvin :
      ambientTemperatureInKelvin setup = 5863 / 20 := by
    have stated := _readouts.ambientTemperatureCelsius
    change ambientTemperatureInKelvin setup - 5463 / 20 = 20 at stated
    norm_num at stated ⊢
    linarith
  have initialHeightMeters :
      lengthInMeters
          (setup.gasStateAt .initialAtStops).gasColumnHeight = 1 / 4 := by
    have shown := _figure.initialGasColumnHeightCentimeters
    change
      100 *
          lengthInMeters
            (setup.gasStateAt .initialAtStops).gasColumnHeight = 25
        at shown
    norm_num at shown ⊢
    linarith
  have pistonMassKilograms :
      massInKilograms setup.pistonMass = 50 :=
    _readouts.pistonMassKilograms
  have gravitationalAccelerationSI :
      accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration = 981 / 100 :=
    _constants.gravitationalAccelerationSI
  have pistonWeightNewtons :
      forceInNewtons setup.pistonWeight = 981 / 2 := by
    calc
      forceInNewtons setup.pistonWeight =
          massInKilograms setup.pistonMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration :=
        _laws.pistonWeightLaw
      _ = 50 * (981 / 100) := by
        rw [pistonMassKilograms, gravitationalAccelerationSI]
      _ = 981 / 2 := by norm_num
  have pistonDiameterMeters :
      lengthInMeters setup.cylinderInnerDiameter = 1 / 10 :=
    _readouts.pistonDiameterMeters
  have pistonAreaSquareMeters :
      areaInSquareMeters setup.pistonCrossSectionalArea = Real.pi / 400 := by
    calc
      areaInSquareMeters setup.pistonCrossSectionalArea =
          Real.pi *
            (lengthInMeters setup.cylinderInnerDiameter / 2) ^ 2 :=
        _laws.circularCrossSection
      _ = Real.pi / 400 := by
        rw [pistonDiameterMeters]
        ring
  have dropFormula :=
    pistonDropFormulaInMeters setup _physical _ambient _laws
  have exactDropCentimeters :
      lengthInCentimeters setup.pistonDrop =
        100 *
          (1 / 4 -
            ((1 / 4) * 250000 * (5863 / 20) * (Real.pi / 400)) /
              ((11463 / 20) *
                (100000 * (Real.pi / 400) + 981 / 2))) := by
    rw [lengthInCentimeters, dropFormula, initialHeightMeters,
      initialPressurePascals, ambientTemperatureKelvin,
      initialTemperatureKelvin, atmosphericPressurePascals,
      pistonAreaSquareMeters, pistonWeightNewtons]
  have denominatorPositive :
      0 < (11463 / 20 : ℝ) *
        (100000 * (Real.pi / 400) + 981 / 2) := by
    positivity
  have ratioUpper :
      ((1 / 4 : ℝ) * 250000 * (5863 / 20) * (Real.pi / 400)) /
          ((11463 / 20) *
            (100000 * (Real.pi / 400) + 981 / 2)) <
        79 / 400 := by
    rw [div_lt_iff₀ denominatorPositive]
    nlinarith [Real.pi_lt_d2]
  have ratioLower :
      (393 / 2000 : ℝ) <
        ((1 / 4) * 250000 * (5863 / 20) * (Real.pi / 400)) /
          ((11463 / 20) *
            (100000 * (Real.pi / 400) + 981 / 2)) := by
    rw [lt_div_iff₀ denominatorPositive]
    nlinarith [Real.pi_gt_d2]
  have predictedBounds :
      (21 / 4 : ℝ) < lengthInCentimeters setup.pistonDrop ∧
        lengthInCentimeters setup.pistonDrop < 107 / 20 := by
    rw [exactDropCentimeters]
    constructor <;> nlinarith
  have chosenDistance :
      |lengthInCentimeters setup.pistonDrop - 53 / 10| < 1 / 20 := by
    rw [abs_lt]
    constructor <;> linarith [predictedBounds.1, predictedBounds.2]
  constructor
  · simpa only [RoundsToNearestTenthCentimeter, recordedDatasetAnswer,
      displayedDropCentimeters] using chosenDistance
  · intro other hother
    fin_cases other
    · simpa only [recordedDatasetAnswer, displayedDropCentimeters,
        abs_of_pos
          (show 0 <
              lengthInCentimeters setup.pistonDrop - 1 / 4 by
            linarith [predictedBounds.1])] using
        (lt_trans chosenDistance
          (show (1 / 20 : ℝ) <
              lengthInCentimeters setup.pistonDrop - 1 / 4 by
            linarith [predictedBounds.1]))
    · simpa only [recordedDatasetAnswer, displayedDropCentimeters,
        abs_of_neg
          (show lengthInCentimeters setup.pistonDrop - 39 / 5 < 0 by
            linarith [predictedBounds.2])] using
        (lt_trans chosenDistance
          (show (1 / 20 : ℝ) <
              -(lengthInCentimeters setup.pistonDrop - 39 / 5) by
            linarith [predictedBounds.2]))
    · simpa only [recordedDatasetAnswer, displayedDropCentimeters,
        abs_of_pos
          (show 0 <
              lengthInCentimeters setup.pistonDrop - 16 / 5 by
            linarith [predictedBounds.1])] using
        (lt_trans chosenDistance
          (show (1 / 20 : ℝ) <
              lengthInCentimeters setup.pistonDrop - 16 / 5 by
            linarith [predictedBounds.1]))
    · contradiction

end PhyXMiniProblems.ProblemPhyXMini0447
