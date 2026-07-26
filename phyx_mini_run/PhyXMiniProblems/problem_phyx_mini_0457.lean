import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0457

open Dimension

/-!
# Heating air below a massless piston while expelling water

A vertical cylinder is open to atmospheric pressure `P₀` at its upper water
surface.  Water lies above a massless piston and a closed sample of air lies
below it.  Heating the air raises the piston and spills water over the rim
until no water remains.

Physical length, volume, mass, density, acceleration, pressure, area, and
energy are represented by dimensionful quantities.  Real numbers occur only
as explicitly named SI readouts, dimensionless material coefficients, and
displayed answer values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of a choice of units. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative mass density, with dimension `M L⁻³`. -/
abbrev DensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical mass density in kilograms per cubic metre. -/
def densityInKilogramsPerCubicMeter (density : DensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read an acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a Physlib pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a Physlib energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a Physlib energy in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-!
Physlib's `Temperature` stores an absolute temperature in an arbitrary
zero-preserving temperature unit.  The explicit storage unit makes the kelvin
and Celsius readouts unambiguous.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- The exact offset between zero degrees Celsius and zero kelvin. -/
def celsiusZeroInKelvin : ℝ := 5463 / 20

/-- Read an absolute temperature on the affine Celsius scale. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - celsiusZeroInKelvin

/-! ## States, apparatus, and primary-figure vocabulary -/

/-- The initial state and the state at which all water has been expelled. -/
inductive ProcessState where
  | initial
  | allWaterExpelled
  deriving DecidableEq, Fintype, Repr

/-- Material confined below the piston. -/
inductive GasSubstance where
  | air
  | other
  deriving DecidableEq, Repr

/-- Liquid initially resting above the piston. -/
inductive UpperLiquid where
  | water
  | other
  deriving DecidableEq, Repr

/-- Orientation of the cylinder axis and of the gravity arrow. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The quasistatic idealization used for the moving piston. -/
inductive ProcessRegime where
  | quasistaticHeatingWithOverflow
  | other
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied raster. -/
inductive FigureObject where
  | cylinderWalls
  | masslessPiston
  | upperWaterRegion
  | lowerAirRegion
  | openWaterSurface
  deriving DecidableEq, Fintype, Repr

/-- Literal labels visible in the supplied raster. -/
inductive FigureLabel where
  | atmosphericPressureP0
  | waterH2O
  | air
  | gravityG
  deriving DecidableEq, Fintype, Repr

/-- Qualitative and symbolic information transcribed from the primary image. -/
structure WaterPistonCylinderFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  pressureDenotedByP0 : DimPressure
  waterIsAbovePiston : Bool
  airIsBelowPiston : Bool
  pistonSpansCylinder : Bool
  p0ActsOnOpenWaterSurface : Bool
  gravityArrowDirection : VerticalDirection
  containsHeatTransferValue : Bool

/-- One equilibrium state of the closed air sample. -/
structure AirState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
The complete physical setup.  The two real-valued path functions are SI
readouts of a physical water height and pressure as functions of the SI air
volume readout; they do not replace the corresponding physical quantities.
-/
structure WaterExpulsionSetup where
  enclosedGas : GasSubstance
  upperLiquid : UpperLiquid
  processRegime : ProcessRegime
  cylinderHeight : LengthQuantity
  cylinderCrossSectionalArea : DimArea
  pistonMass : MassQuantity
  waterDensity : DensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  atmosphericPressureP0 : DimPressure
  waterTemperature : Temperature
  temperatureStorageUnit : TemperatureUnit
  stateAt : ProcessState → AirState
  airMass : MassQuantity
  specificGasConstantJoulesPerKilogramKelvin : ℝ
  internalEnergyCoefficientCvOverR : ℝ
  waterColumnHeightInMetersAtAirVolume : ℝ → ℝ
  processPressureInPascals : ℝ → ℝ
  boundaryWorkDoneByAir : DimEnergy
  internalEnergyChangeOfAir : DimEnergy
  heatTransferredToAir : DimEnergy
  pistonMovesWithoutFriction : Bool
  cylinderIsOpenAtTop : Bool
  waterSpillsOverRim : Bool
  airSampleIsClosed : Bool
  figure : WaterPistonCylinderFigure

/-- Kelvin readout of the air temperature at a process endpoint. -/
def airTemperatureInKelvin
    (setup : WaterExpulsionSetup) (state : ProcessState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.stateAt state).temperature

/-- Celsius readout of the water temperature. -/
def waterTemperatureInDegreesCelsius
    (setup : WaterExpulsionSetup) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    setup.waterTemperature

/-! ## Assumptions: scenario, stated data, figure, reference data, and laws -/

/-- Qualitative conditions stated or conventionally idealized in the problem. -/
structure MatchesWaterExpulsionScenario
    (setup : WaterExpulsionSetup) : Prop where
  lowerSubstanceIsAir : setup.enclosedGas = .air
  upperLiquidIsWater : setup.upperLiquid = .water
  quasistaticOverflowRegime :
    setup.processRegime = .quasistaticHeatingWithOverflow
  pistonIsMassless : massInKilograms setup.pistonMass = 0
  negligiblePistonFriction : setup.pistonMovesWithoutFriction = true
  topOpenToAtmosphere : setup.cylinderIsOpenAtTop = true
  waterOverflowsRim : setup.waterSpillsOverRim = true
  fixedClosedAirSample : setup.airSampleIsClosed = true

/-!
The four numerical readouts explicitly supplied by the prose.  Neither the
final temperature nor the requested heat transfer appears here.
-/
structure MatchesProblemReadouts (setup : WaterExpulsionSetup) : Prop where
  cylinderHeightMeters : lengthInMeters setup.cylinderHeight = 10
  crossSectionalAreaSquareMeters :
    areaInSquareMeters setup.cylinderCrossSectionalArea = 1 / 10
  initialAirVolumeCubicMeters :
    volumeInCubicMeters (setup.stateAt .initial).volume = 3 / 10
  initialAirTemperatureKelvin :
    airTemperatureInKelvin setup .initial = 300
  initialWaterTemperatureCelsius :
    waterTemperatureInDegreesCelsius setup = 20

/-!
Primary-raster evidence: `P₀` is applied at the open upper water surface,
water is above the piston, air is below it, and `g` points downward.  The
image contains no numerical heat-transfer readout.
-/
structure MatchesSuppliedWaterPistonFigure
    (setup : WaterExpulsionSetup) : Prop where
  everyNamedObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyLiteralLabelShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  P0DenotesAtmosphericPressure :
    setup.figure.pressureDenotedByP0 = setup.atmosphericPressureP0
  P0AtOpenWaterSurface : setup.figure.p0ActsOnOpenWaterSurface = true
  waterAbovePiston : setup.figure.waterIsAbovePiston = true
  airBelowPiston : setup.figure.airIsBelowPiston = true
  pistonCrossesCylinderBore : setup.figure.pistonSpansCylinder = true
  downwardGravityArrow : setup.figure.gravityArrowDirection = .downward
  noHeatTransferValueInFigure :
    setup.figure.containsHeatTransferValue = false

/-!
Standard engineering reference values used at the precision of the answer
choices: `P₀ = 101.3 kPa`, liquid-water density `1000 kg/m³`,
`g = 9.8 m/s²`, dry-air `R = 287 J/(kg K)`, and `cᵥ/R = 5/2`.
-/
structure UsesEngineeringReferenceData
    (setup : WaterExpulsionSetup) : Prop where
  atmosphericPressurePascals :
    pressureInPascals setup.atmosphericPressureP0 = 101300
  waterDensitySI :
    densityInKilogramsPerCubicMeter setup.waterDensity = 1000
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5
  specificGasConstantSI :
    setup.specificGasConstantJoulesPerKilogramKelvin = 287
  idealDiatomicAirCvOverR :
    setup.internalEnergyCoefficientCvOverR = 5 / 2

/-- Positivity and endpoint ordering selecting the physical expansion branch. -/
structure HasPhysicalWaterExpulsionParameters
    (setup : WaterExpulsionSetup) : Prop where
  heightPositive : 0 < lengthInMeters setup.cylinderHeight
  areaPositive : 0 < areaInSquareMeters setup.cylinderCrossSectionalArea
  densityPositive : 0 < densityInKilogramsPerCubicMeter setup.waterDensity
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericPressureP0
  airMassPositive : 0 < massInKilograms setup.airMass
  gasConstantPositive :
    0 < setup.specificGasConstantJoulesPerKilogramKelvin
  airPressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  airVolumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  airTemperaturePositive : ∀ state,
    0 < airTemperatureInKelvin setup state
  airVolumeIncreases :
    volumeInCubicMeters (setup.stateAt .initial).volume <
      volumeInCubicMeters (setup.stateAt .allWaterExpelled).volume

/-!
The stopping event named in the question.  It fixes the final water-column
height, not the final air temperature or the heat supplied.
-/
structure AllWaterHasBeenPushedOut
    (setup : WaterExpulsionSetup) : Prop where
  finalWaterColumnHeightIsZero :
    setup.waterColumnHeightInMetersAtAirVolume
      (volumeInCubicMeters (setup.stateAt .allWaterExpelled).volume) = 0

/-!
Governing geometry, hydrostatics, ideal-gas behavior, boundary work, caloric
behavior, and the closed-system first law.

The internal-energy relation is the general calorically-perfect ideal-air
identity `ΔU = (cᵥ/R) Δ(PV)`.  The first law uses the convention that both
heat transferred to the air and work done by the air are positive.  No field
assigns a numerical value to the requested heat transfer or chooses D.
-/
structure SatisfiesWaterExpulsionLaws
    (setup : WaterExpulsionSetup) : Prop where
  waterColumnGeometry : ∀ airVolume : ℝ,
    airVolume ∈ Set.Icc
        (volumeInCubicMeters (setup.stateAt .initial).volume)
        (volumeInCubicMeters (setup.stateAt .allWaterExpelled).volume) →
      setup.waterColumnHeightInMetersAtAirVolume airVolume =
        lengthInMeters setup.cylinderHeight -
          airVolume / areaInSquareMeters setup.cylinderCrossSectionalArea
  hydrostaticMasslessPistonBalance : ∀ airVolume : ℝ,
    airVolume ∈ Set.Icc
        (volumeInCubicMeters (setup.stateAt .initial).volume)
        (volumeInCubicMeters (setup.stateAt .allWaterExpelled).volume) →
      setup.processPressureInPascals airVolume =
        pressureInPascals setup.atmosphericPressureP0 +
          densityInKilogramsPerCubicMeter setup.waterDensity *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            setup.waterColumnHeightInMetersAtAirVolume airVolume
  pressurePathMatchesEndpoints : ∀ state : ProcessState,
    setup.processPressureInPascals
        (volumeInCubicMeters (setup.stateAt state).volume) =
      pressureInPascals (setup.stateAt state).pressure
  idealGasEquationAtEndpoints : ∀ state : ProcessState,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      massInKilograms setup.airMass *
        setup.specificGasConstantJoulesPerKilogramKelvin *
          airTemperatureInKelvin setup state
  quasistaticBoundaryWorkIntegral :
    energyInJoules setup.boundaryWorkDoneByAir =
      ∫ airVolume in
          volumeInCubicMeters (setup.stateAt .initial).volume..
          volumeInCubicMeters (setup.stateAt .allWaterExpelled).volume,
        setup.processPressureInPascals airVolume
  caloricallyPerfectAirInternalEnergy :
    energyInJoules setup.internalEnergyChangeOfAir =
      setup.internalEnergyCoefficientCvOverR *
        (pressureInPascals (setup.stateAt .allWaterExpelled).pressure *
            volumeInCubicMeters
              (setup.stateAt .allWaterExpelled).volume -
          pressureInPascals (setup.stateAt .initial).pressure *
            volumeInCubicMeters (setup.stateAt .initial).volume)
  closedSystemFirstLaw :
    energyInJoules setup.heatTransferredToAir =
      energyInJoules setup.internalEnergyChangeOfAir +
        energyInJoules setup.boundaryWorkDoneByAir

/-! ## Derived quantities and answer metadata -/

/-- Labels printed beside the four candidate heat-transfer values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat transfer in kilojoules printed beside each answer label. -/
def displayedHeatTransferInKilojoules : AnswerChoice → ℝ
  | .A => 1013 / 10
  | .B => 4331 / 10
  | .C => 1698 / 10
  | .D => 2207 / 10

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement after reporting to the `0.1 kJ` precision of the answer list. -/
def IsReportedHeatChoice
    (setup : WaterExpulsionSetup) (choice : AnswerChoice) : Prop :=
  round (10 * energyInKilojoules setup.heatTransferredToAir) =
    round (10 * displayedHeatTransferInKilojoules choice)

/-- A displayed choice is the unique value agreeing at the stated precision. -/
def IsUniqueReportedHeatChoice
    (setup : WaterExpulsionSetup) (choice : AnswerChoice) : Prop :=
  IsReportedHeatChoice setup choice ∧
    ∀ other, IsReportedHeatChoice setup other → other = choice

/-!
With no water remaining, the air fills the `10 m × 0.1 m²` cylinder, so its
final volume is `1 m³`.  This is a geometric consequence, not an independent
final-volume readout.
-/
lemma finalAirVolumeInCubicMeters
    (setup : WaterExpulsionSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalWaterExpulsionParameters setup)
    (hEndpoint : AllWaterHasBeenPushedOut setup)
    (hLaws : SatisfiesWaterExpulsionLaws setup) :
    volumeInCubicMeters (setup.stateAt .allWaterExpelled).volume = 1 := by
  have hFinalVolumeMem :
      volumeInCubicMeters (setup.stateAt .allWaterExpelled).volume ∈
        Set.Icc
          (volumeInCubicMeters (setup.stateAt .initial).volume)
          (volumeInCubicMeters
            (setup.stateAt .allWaterExpelled).volume) :=
    ⟨hPhysical.airVolumeIncreases.le, le_rfl⟩
  have hGeometry :=
    hLaws.waterColumnGeometry
      (volumeInCubicMeters
        (setup.stateAt .allWaterExpelled).volume)
      hFinalVolumeMem
  rw [hEndpoint.finalWaterColumnHeightIsZero,
    hReadouts.cylinderHeightMeters,
    hReadouts.crossSectionalAreaSquareMeters] at hGeometry
  norm_num at hGeometry ⊢
  linarith

/-!
The hydrostatic pressure path, ideal-air caloric relation, and first law give
`220745 J = 220.745 kJ` before answer-list reporting.
-/
lemma heatTransferredToAirInJoules_exact
    (setup : WaterExpulsionSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReference : UsesEngineeringReferenceData setup)
    (hPhysical : HasPhysicalWaterExpulsionParameters setup)
    (hEndpoint : AllWaterHasBeenPushedOut setup)
    (hLaws : SatisfiesWaterExpulsionLaws setup) :
    energyInJoules setup.heatTransferredToAir = 220745 := by
  have hFinalVolume :=
    finalAirVolumeInCubicMeters setup hReadouts hPhysical hEndpoint hLaws
  have hPressurePath (airVolume : ℝ)
      (hAirVolume : airVolume ∈ Set.Icc (3 / 10 : ℝ) 1) :
      setup.processPressureInPascals airVolume =
        199300 - 98000 * airVolume := by
    have hAirVolumeOriginal :
        airVolume ∈ Set.Icc
          (volumeInCubicMeters (setup.stateAt .initial).volume)
          (volumeInCubicMeters
            (setup.stateAt .allWaterExpelled).volume) := by
      simpa [hReadouts.initialAirVolumeCubicMeters, hFinalVolume] using
        hAirVolume
    have hGeometry :=
      hLaws.waterColumnGeometry airVolume hAirVolumeOriginal
    have hHydrostatic :=
      hLaws.hydrostaticMasslessPistonBalance
        airVolume hAirVolumeOriginal
    rw [hReadouts.cylinderHeightMeters,
      hReadouts.crossSectionalAreaSquareMeters] at hGeometry
    rw [hReference.atmosphericPressurePascals,
      hReference.waterDensitySI,
      hReference.gravitationalAccelerationSI,
      hGeometry] at hHydrostatic
    norm_num at hHydrostatic ⊢
    linarith
  have hInitialPressure :
      pressureInPascals (setup.stateAt .initial).pressure = 169900 := by
    rw [← hLaws.pressurePathMatchesEndpoints .initial,
      hReadouts.initialAirVolumeCubicMeters]
    have hInitialPressurePath :=
      hPressurePath (3 / 10) (by norm_num)
    norm_num at hInitialPressurePath
    exact hInitialPressurePath
  have hFinalPressure :
      pressureInPascals
        (setup.stateAt .allWaterExpelled).pressure = 101300 := by
    rw [← hLaws.pressurePathMatchesEndpoints .allWaterExpelled,
      hFinalVolume]
    have hFinalPressurePath := hPressurePath 1 (by norm_num)
    norm_num at hFinalPressurePath
    exact hFinalPressurePath
  have hBoundaryWork :
      energyInJoules setup.boundaryWorkDoneByAir = 94920 := by
    rw [hLaws.quasistaticBoundaryWorkIntegral,
      hReadouts.initialAirVolumeCubicMeters, hFinalVolume]
    calc
      (∫ airVolume : ℝ in (3 / 10)..1,
          setup.processPressureInPascals airVolume) =
          ∫ airVolume : ℝ in (3 / 10)..1,
            (199300 - 98000 * airVolume) := by
              apply intervalIntegral.integral_congr
              intro airVolume hAirVolume
              apply hPressurePath
              simpa [Set.uIcc_of_le (by norm_num : (3 / 10 : ℝ) ≤ 1)]
                using hAirVolume
      _ = 94920 := by
        calc
          (∫ airVolume : ℝ in (3 / 10)..1,
              (199300 - 98000 * airVolume)) =
              (∫ _airVolume : ℝ in (3 / 10)..1, (199300 : ℝ)) -
                (∫ airVolume : ℝ in (3 / 10)..1,
                  98000 * airVolume) := by
                    exact intervalIntegral.integral_sub
                      (continuous_const.intervalIntegrable _ _)
                      ((continuous_const.mul continuous_id).intervalIntegrable
                        _ _)
          _ = 94920 := by
            rw [intervalIntegral.integral_const,
              intervalIntegral.integral_const_mul, integral_id]
            norm_num
  have hInternalEnergy :
      energyInJoules setup.internalEnergyChangeOfAir = 125825 := by
    rw [hLaws.caloricallyPerfectAirInternalEnergy,
      hReference.idealDiatomicAirCvOverR,
      hFinalPressure, hFinalVolume,
      hInitialPressure, hReadouts.initialAirVolumeCubicMeters]
    norm_num
  rw [hLaws.closedSystemFirstLaw, hInternalEnergy, hBoundaryWork]
  norm_num

/-!
The model value is `220.745 kJ`, which is reported as `220.7 kJ` at the
precision of the choices and uniquely selects D.

This formalizes `thm:physics:phyx_mini_0457:target`.  No premise fixes a
numerical heat-transfer value or selects an answer choice.
-/
theorem problem_phyx_mini_0457
    (setup : WaterExpulsionSetup)
    (hScenario : MatchesWaterExpulsionScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedWaterPistonFigure setup)
    (hReference : UsesEngineeringReferenceData setup)
    (hPhysical : HasPhysicalWaterExpulsionParameters setup)
    (hEndpoint : AllWaterHasBeenPushedOut setup)
    (hLaws : SatisfiesWaterExpulsionLaws setup) :
    energyInJoules setup.heatTransferredToAir = 220745 ∧
      IsUniqueReportedHeatChoice setup .D := by
  have hHeat :=
    heatTransferredToAirInJoules_exact setup hReadouts hReference
      hPhysical hEndpoint hLaws
  refine ⟨hHeat, ?_⟩
  constructor
  · norm_num [IsReportedHeatChoice, energyInKilojoules,
      displayedHeatTransferInKilojoules, hHeat]
  · intro other hOther
    cases other with
    | A =>
        norm_num [IsReportedHeatChoice, energyInKilojoules,
          displayedHeatTransferInKilojoules, hHeat] at hOther
    | B =>
        norm_num [IsReportedHeatChoice, energyInKilojoules,
          displayedHeatTransferInKilojoules, hHeat] at hOther
    | C =>
        norm_num [IsReportedHeatChoice, energyInKilojoules,
          displayedHeatTransferInKilojoules, hHeat] at hOther
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0457
