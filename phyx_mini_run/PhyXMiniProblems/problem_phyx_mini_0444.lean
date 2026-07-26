import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0444

open Dimension

/-!
# Quality change during isothermal R-410A transfer between two rigid tanks

Two equal `200 L` tanks, labelled `A` and `B`, are joined by a valve. Tank
`A` initially contains saturated R-410A with `10%` of its volume liquid and
`90%` vapor, while tank `B` is evacuated. The valve is opened slowly, so
saturated vapor passes from `A` to `B` at `25 °C`, and is closed when the
pressures agree.

Mass, volume, specific volume, pressure, and absolute temperature retain
physical quantity types. Real numbers occur only as named SI or Celsius
readouts, dimensionless vapor quality, and the printed multiple-choice data.
The primary raster shows a valve (a circle with a cross), not the light bulb
suggested by the auxiliary caption.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of specific volume, `L³ M⁻¹`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- A nonnegative physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative thermodynamic specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in litres. -/
def volumeInLitres (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMetres volume

/-- Read a physical mass in coherent SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a specific volume in cubic metres per kilogram. -/
def specificVolumeInCubicMetresPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-!
Physlib represents absolute temperature in a zero-preserving unit. A Celsius
value is therefore retained as an instrument readout attached to the same
absolute temperature, with its affine calibration imposed below.
-/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ

/-- Read an absolute temperature in kelvins. -/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Tanks, phase inventories, valve process, and primary figure -/

/-- The two tank labels printed in the source image. -/
inductive TankLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The equilibrium endpoints of the transfer process. -/
inductive SystemStage where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- Liquid and vapor contributions to a tank inventory. -/
inductive RefrigerantPhase where
  | liquid
  | vapor
  deriving DecidableEq, Fintype, Repr

/-- Refrigerant identity, kept distinct from scalar property readouts. -/
inductive RefrigerantKind where
  | r410A
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic region occupied by the contents of one tank. -/
inductive TankContentsRegion where
  | evacuated
  | saturatedLiquidVapor
  | saturatedVapor
  | other
  deriving DecidableEq, Repr

/-- Operational position of the valve. -/
inductive ValvePosition where
  | closed
  | open
  deriving DecidableEq, Repr

/-- Direction of net refrigerant transfer through the connecting line. -/
inductive TransferDirection where
  | fromAToB
  | fromBToA
  deriving DecidableEq, Repr

/-- Slow-process idealization stated in the prose. -/
inductive TransferRegime where
  | quasistaticIsothermal
  | other
  deriving DecidableEq, Repr

/-- Rectangular tank outline visible in the supplied raster. -/
inductive TankShape where
  | rectangular
  deriving DecidableEq, Repr

/-- Physical state and phase inventory of one tank at one endpoint. -/
structure TankState where
  pressure : DimPressure
  temperature : MeasuredTemperature
  refrigerant : Option RefrigerantKind
  region : TankContentsRegion
  phaseMass : RefrigerantPhase → MassQuantity
  phaseVolume : RefrigerantPhase → VolumeQuantity

/-- The integrated stream that passes through the valve. -/
structure RefrigerantTransfer where
  refrigerant : RefrigerantKind
  phase : RefrigerantPhase
  direction : TransferDirection
  transferredMass : MassQuantity

/-!
Qualitative content of the primary raster. Horizontal coordinates encode only
left-to-right placement in the drawing, not physical lengths.
-/
structure SuppliedTwoTankFigure where
  tankShown : TankLabel → Bool
  tankLetterShown : TankLabel → Bool
  tankShape : TankLabel → TankShape
  tankHorizontalCoordinate : TankLabel → ℝ
  connectingLineShown : Bool
  centralValveSymbolShown : Bool
  valveCrossMarkShown : Bool
  liquidLayerShown : TankLabel → Bool
  liquidLayerAtBottom : TankLabel → Bool

/-!
An external equilibrium-property table for saturated R-410A. Its outputs are
physical pressure and specific volume rather than untyped scalars.
-/
structure R410APropertyTable where
  saturationPressureAt : Temperature → DimPressure
  saturatedSpecificVolumeAt :
    Temperature → RefrigerantPhase → SpecificVolumeQuantity

/-!
The complete experiment. Tank volume is stage-independent, expressing
rigidity. The transfer mass and endpoint states are independent observables
until the governing laws below are assumed.
-/
structure TwoTankR410AExperiment where
  figure : SuppliedTwoTankFigure
  propertyTable : R410APropertyTable
  tankVolume : TankLabel → VolumeQuantity
  stateAt : SystemStage → TankLabel → TankState
  maintainedTemperature : MeasuredTemperature
  temperatureStorageUnit : TemperatureUnit
  transfer : RefrigerantTransfer
  valvePositionAt : SystemStage → ValvePosition
  valveOpenedDuringTransfer : Bool
  tanksAreRigid : Bool
  transferRegime : TransferRegime

/-! ## Derived inventory and quality readouts -/

/-- Kilograms of one phase in a specified endpoint tank. -/
def phaseMassInKilograms
    (setup : TwoTankR410AExperiment) (stage : SystemStage)
    (tank : TankLabel) (phase : RefrigerantPhase) : ℝ :=
  massInKilograms ((setup.stateAt stage tank).phaseMass phase)

/-- Total refrigerant mass in one endpoint tank. -/
def totalMassInKilograms
    (setup : TwoTankR410AExperiment) (stage : SystemStage)
    (tank : TankLabel) : ℝ :=
  phaseMassInKilograms setup stage tank .liquid +
    phaseMassInKilograms setup stage tank .vapor

/-- Cubic metres occupied by one phase in a specified endpoint tank. -/
def phaseVolumeInCubicMetres
    (setup : TwoTankR410AExperiment) (stage : SystemStage)
    (tank : TankLabel) (phase : RefrigerantPhase) : ℝ :=
  volumeInCubicMetres ((setup.stateAt stage tank).phaseVolume phase)

/-- Total volume occupied by liquid and vapor in one endpoint tank. -/
def totalOccupiedVolumeInCubicMetres
    (setup : TwoTankR410AExperiment) (stage : SystemStage)
    (tank : TankLabel) : ℝ :=
  phaseVolumeInCubicMetres setup stage tank .liquid +
    phaseVolumeInCubicMetres setup stage tank .vapor

/-!
Thermodynamic quality is vapor mass divided by total refrigerant mass. This
definition contains no answer-choice value.
-/
def vaporQuality
    (setup : TwoTankR410AExperiment) (stage : SystemStage)
    (tank : TankLabel) : ℝ :=
  phaseMassInKilograms setup stage tank .vapor /
    totalMassInKilograms setup stage tank

/-- Final minus initial vapor quality in tank `A`. -/
def qualityChangeInTankA (setup : TwoTankR410AExperiment) : ℝ :=
  vaporQuality setup .final .A - vaporQuality setup .initial .A

/-! ## Figure/data readouts and governing-law assumptions -/

/-- Facts visible in the primary two-tank raster. -/
structure MatchesSuppliedTwoTankFigure
    (figure : SuppliedTwoTankFigure) : Prop where
  everyTankShown : ∀ tank, figure.tankShown tank = true
  everyTankLetterShown : ∀ tank, figure.tankLetterShown tank = true
  everyTankIsRectangular : ∀ tank, figure.tankShape tank = .rectangular
  tankAIsLeftOfTankB :
    figure.tankHorizontalCoordinate .A <
      figure.tankHorizontalCoordinate .B
  connectingLineIsShown : figure.connectingLineShown = true
  centralValveIsShown : figure.centralValveSymbolShown = true
  crossInsideValveIsShown : figure.valveCrossMarkShown = true
  liquidLayerShownOnlyInA :
    figure.liquidLayerShown .A = true ∧
      figure.liquidLayerShown .B = false
  liquidLayerAtBottomOfA : figure.liquidLayerAtBottom .A = true

/-!
Prose data and qualitative process facts. The final pressure equality is the
stated stopping condition. No field fixes either endpoint quality or its
change.
-/
structure MatchesR410ATankScenario
    (setup : TwoTankR410AExperiment) : Prop where
  tankAVolumeLitres : volumeInLitres (setup.tankVolume .A) = 200
  tankBVolumeLitres : volumeInLitres (setup.tankVolume .B) = 200
  rigidTanks : setup.tanksAreRigid = true
  initialValveClosed : setup.valvePositionAt .initial = .closed
  valveWasOpened : setup.valveOpenedDuringTransfer = true
  finalValveClosed : setup.valvePositionAt .final = .closed
  processIsSlowAndIsothermal :
    setup.transferRegime = .quasistaticIsothermal
  streamIsR410A : setup.transfer.refrigerant = .r410A
  streamIsSaturatedVapor : setup.transfer.phase = .vapor
  streamFlowsFromAToB : setup.transfer.direction = .fromAToB
  initialAContainsR410A :
    (setup.stateAt .initial .A).refrigerant = some .r410A
  initialAIsSaturatedMixture :
    (setup.stateAt .initial .A).region = .saturatedLiquidVapor
  initialBIsEvacuated :
    (setup.stateAt .initial .B).refrigerant = none ∧
      (setup.stateAt .initial .B).region = .evacuated
  finalAContainsR410A :
    (setup.stateAt .final .A).refrigerant = some .r410A
  finalAIsSaturatedMixture :
    (setup.stateAt .final .A).region = .saturatedLiquidVapor
  finalBContainsR410A :
    (setup.stateAt .final .B).refrigerant = some .r410A
  finalBIsSaturatedVapor :
    (setup.stateAt .final .B).region = .saturatedVapor
  maintainedTemperatureCelsius :
    setup.maintainedTemperature.degreesCelsius = 25
  everyEndpointAtMaintainedTemperature : ∀ stage tank,
    (setup.stateAt stage tank).temperature = setup.maintainedTemperature
  initialALiquidVolumeLitres :
    1000 * phaseVolumeInCubicMetres setup .initial .A .liquid = 20
  initialAVaporVolumeLitres :
    1000 * phaseVolumeInCubicMetres setup .initial .A .vapor = 180
  initialBHasNoPhaseMass : ∀ phase,
    phaseMassInKilograms setup .initial .B phase = 0
  initialBHasNoOccupiedPhaseVolume : ∀ phase,
    phaseVolumeInCubicMetres setup .initial .B phase = 0
  initialBVacuumPressure :
    pressureInPascals (setup.stateAt .initial .B).pressure = 0
  finalBHasNoLiquidMass :
    phaseMassInKilograms setup .final .B .liquid = 0
  finalBHasNoLiquidVolume :
    phaseVolumeInCubicMetres setup .final .B .liquid = 0
  finalPressuresAgree :
    (setup.stateAt .final .A).pressure =
      (setup.stateAt .final .B).pressure

/-!
Calibrated saturation-table readouts at `25 °C`. The rounded values
`v_f = 0.0009444 m³/kg` and `v_g = 0.015164 m³/kg` are constitutive R-410A
property data, not the requested quality change.
-/
structure MatchesReferenceR410APropertyData
    (setup : TwoTankR410AExperiment) : Prop where
  saturatedLiquidSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
        (setup.propertyTable.saturatedSpecificVolumeAt
          setup.maintainedTemperature.absoluteTemperature .liquid) =
      2361 / 2500000
  saturatedVaporSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
        (setup.propertyTable.saturatedSpecificVolumeAt
          setup.maintainedTemperature.absoluteTemperature .vapor) =
      3791 / 250000

/-- Positivity and nondegeneracy of the physical state parameters. -/
structure HasPhysicalR410AParameters
    (setup : TwoTankR410AExperiment) : Prop where
  everyTankVolumePositive : ∀ tank,
    0 < volumeInCubicMetres (setup.tankVolume tank)
  everyPhaseMassNonnegative : ∀ stage tank phase,
    0 ≤ phaseMassInKilograms setup stage tank phase
  everyPhaseVolumeNonnegative : ∀ stage tank phase,
    0 ≤ phaseVolumeInCubicMetres setup stage tank phase
  relevantTankMassesPositive :
    0 < totalMassInKilograms setup .initial .A ∧
      0 < totalMassInKilograms setup .final .A ∧
      0 < totalMassInKilograms setup .final .B
  transferredMassPositive :
    0 < massInKilograms setup.transfer.transferredMass
  maintainedAbsoluteTemperaturePositive :
    0 < temperatureInKelvin setup.temperatureStorageUnit
      setup.maintainedTemperature.absoluteTemperature
  saturatedSpecificVolumesPositive : ∀ phase,
    0 < specificVolumeInCubicMetresPerKilogram
      (setup.propertyTable.saturatedSpecificVolumeAt
        setup.maintainedTemperature.absoluteTemperature phase)
  liquidSpecificVolumeLessThanVapor :
    specificVolumeInCubicMetresPerKilogram
        (setup.propertyTable.saturatedSpecificVolumeAt
          setup.maintainedTemperature.absoluteTemperature .liquid) <
      specificVolumeInCubicMetresPerKilogram
        (setup.propertyTable.saturatedSpecificVolumeAt
          setup.maintainedTemperature.absoluteTemperature .vapor)

/-!
The governing endpoint physics:

* Celsius and kelvin readouts refer to the same absolute temperature;
* each saturated phase obeys `V_phase = m_phase v_phase`;
* non-evacuated contents fill their rigid tank;
* their pressure is the saturation pressure at their temperature;
* the integrated vapor stream is exactly the mass lost by `A` and gained by
  initially evacuated `B`.

These laws are uniform physical relations and contain no numerical quality.
-/
structure SatisfiesIsothermalSaturatedTransferLaws
    (setup : TwoTankR410AExperiment) : Prop where
  celsiusKelvinCalibration :
    temperatureInKelvin setup.temperatureStorageUnit
        setup.maintainedTemperature.absoluteTemperature =
      setup.maintainedTemperature.degreesCelsius + 5463 / 20
  saturatedPhaseMassVolumeLaw : ∀ stage tank phase,
    (setup.stateAt stage tank).region ≠ .evacuated →
      phaseVolumeInCubicMetres setup stage tank phase =
        phaseMassInKilograms setup stage tank phase *
          specificVolumeInCubicMetresPerKilogram
            (setup.propertyTable.saturatedSpecificVolumeAt
              (setup.stateAt stage tank).temperature.absoluteTemperature
              phase)
  nonEvacuatedContentsFillTank : ∀ stage tank,
    (setup.stateAt stage tank).region ≠ .evacuated →
      totalOccupiedVolumeInCubicMetres setup stage tank =
        volumeInCubicMetres (setup.tankVolume tank)
  saturatedPressureLaw : ∀ stage tank,
    (setup.stateAt stage tank).region ≠ .evacuated →
      (setup.stateAt stage tank).pressure =
        setup.propertyTable.saturationPressureAt
          (setup.stateAt stage tank).temperature.absoluteTemperature
  tankAMassLossIsTransferredMass :
    totalMassInKilograms setup .initial .A =
      totalMassInKilograms setup .final .A +
        massInKilograms setup.transfer.transferredMass
  tankBMassGainIsTransferredMass :
    totalMassInKilograms setup .final .B =
      totalMassInKilograms setup .initial .B +
        massInKilograms setup.transfer.transferredMass

/-! ## Displayed answers and current target -/

/-- Labels of the four printed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless quality changes printed beside the answer labels. -/
def displayedQualityChange : AnswerChoice → ℝ
  | .A => 2 / 125
  | .B => 1 / 2
  | .C => 159 / 1000
  | .D => 283 / 1000

/-- The dataset's recorded label, retained only as answer metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement with a three-decimal display: the exact modeled change lies within
half of one unit in the last printed decimal place.
-/
def IsReportedQualityChange
    (setup : TwoTankR410AExperiment) (choice : AnswerChoice) : Prop :=
  |qualityChangeInTankA setup - displayedQualityChange choice| <
    (1 / 2000 : ℝ)

/-!
The phase-volume law and the `20 L`/`180 L` initial split determine the
initial phase masses. Filling the equal `200 L` tank `B` with saturated vapor
determines the transferred mass; the two directional mass balances then
determine the final mass and quality in `A`. With the calibrated R-410A
specific volumes the quality increase is approximately `0.282664`, which
rounds uniquely to `0.283`, answer `D`.

Blueprint: `thm:physics:phyx_mini_0444:target`.
-/
theorem quality_change_in_tank_A_is_choice_D
    (setup : TwoTankR410AExperiment)
    (hFigure : MatchesSuppliedTwoTankFigure setup.figure)
    (hScenario : MatchesR410ATankScenario setup)
    (hReferenceData : MatchesReferenceR410APropertyData setup)
    (hPhysical : HasPhysicalR410AParameters setup)
    (hLaws : SatisfiesIsothermalSaturatedTransferLaws setup) :
    |qualityChangeInTankA setup - (283 / 1000 : ℝ)| < (1 / 2000 : ℝ) ∧
      ∀ choice : AnswerChoice,
        IsReportedQualityChange setup choice ↔ choice = .D := by
  have hInitialANonEvacuated :
      (setup.stateAt .initial .A).region ≠ .evacuated := by
    rw [hScenario.initialAIsSaturatedMixture]
    simp
  have hFinalANonEvacuated :
      (setup.stateAt .final .A).region ≠ .evacuated := by
    rw [hScenario.finalAIsSaturatedMixture]
    simp
  have hFinalBNonEvacuated :
      (setup.stateAt .final .B).region ≠ .evacuated := by
    rw [hScenario.finalBIsSaturatedVapor]
    simp
  have hInitialATemperature :
      (setup.stateAt .initial .A).temperature.absoluteTemperature =
        setup.maintainedTemperature.absoluteTemperature :=
    congrArg MeasuredTemperature.absoluteTemperature
      (hScenario.everyEndpointAtMaintainedTemperature .initial .A)
  have hFinalATemperature :
      (setup.stateAt .final .A).temperature.absoluteTemperature =
        setup.maintainedTemperature.absoluteTemperature :=
    congrArg MeasuredTemperature.absoluteTemperature
      (hScenario.everyEndpointAtMaintainedTemperature .final .A)
  have hFinalBTemperature :
      (setup.stateAt .final .B).temperature.absoluteTemperature =
        setup.maintainedTemperature.absoluteTemperature :=
    congrArg MeasuredTemperature.absoluteTemperature
      (hScenario.everyEndpointAtMaintainedTemperature .final .B)
  have hTankAVolume :
      volumeInCubicMetres (setup.tankVolume .A) = (1 / 5 : ℝ) := by
    have h := hScenario.tankAVolumeLitres
    unfold volumeInLitres at h
    norm_num at h ⊢
    linarith
  have hTankBVolume :
      volumeInCubicMetres (setup.tankVolume .B) = (1 / 5 : ℝ) := by
    have h := hScenario.tankBVolumeLitres
    unfold volumeInLitres at h
    norm_num at h ⊢
    linarith
  have hInitialLiquidVolume :
      phaseVolumeInCubicMetres setup .initial .A .liquid =
        (1 / 50 : ℝ) := by
    have h := hScenario.initialALiquidVolumeLitres
    norm_num at h ⊢
    linarith
  have hInitialVaporVolume :
      phaseVolumeInCubicMetres setup .initial .A .vapor =
        (9 / 50 : ℝ) := by
    have h := hScenario.initialAVaporVolumeLitres
    norm_num at h ⊢
    linarith
  have hInitialLiquidLaw :=
    hLaws.saturatedPhaseMassVolumeLaw .initial .A .liquid
      hInitialANonEvacuated
  have hInitialVaporLaw :=
    hLaws.saturatedPhaseMassVolumeLaw .initial .A .vapor
      hInitialANonEvacuated
  rw [hInitialATemperature,
    hReferenceData.saturatedLiquidSpecificVolume] at hInitialLiquidLaw
  rw [hInitialATemperature,
    hReferenceData.saturatedVaporSpecificVolume] at hInitialVaporLaw
  have hInitialLiquidMass :
      phaseMassInKilograms setup .initial .A .liquid =
        (50000 / 2361 : ℝ) := by
    norm_num at hInitialLiquidLaw hInitialLiquidVolume ⊢
    linarith
  have hInitialVaporMass :
      phaseMassInKilograms setup .initial .A .vapor =
        (45000 / 3791 : ℝ) := by
    norm_num at hInitialVaporLaw hInitialVaporVolume ⊢
    linarith
  have hInitialTotalMass :
      totalMassInKilograms setup .initial .A =
        (295795000 / 8950551 : ℝ) := by
    rw [totalMassInKilograms, hInitialLiquidMass, hInitialVaporMass]
    norm_num
  have hFinalBFill :=
    hLaws.nonEvacuatedContentsFillTank .final .B hFinalBNonEvacuated
  have hFinalBVaporVolume :
      phaseVolumeInCubicMetres setup .final .B .vapor =
        (1 / 5 : ℝ) := by
    rw [totalOccupiedVolumeInCubicMetres,
      hScenario.finalBHasNoLiquidVolume, hTankBVolume] at hFinalBFill
    simpa using hFinalBFill
  have hFinalBVaporLaw :=
    hLaws.saturatedPhaseMassVolumeLaw .final .B .vapor
      hFinalBNonEvacuated
  rw [hFinalBTemperature,
    hReferenceData.saturatedVaporSpecificVolume] at hFinalBVaporLaw
  have hFinalBVaporMass :
      phaseMassInKilograms setup .final .B .vapor =
        (50000 / 3791 : ℝ) := by
    norm_num at hFinalBVaporLaw hFinalBVaporVolume ⊢
    linarith
  have hInitialBTotalMass :
      totalMassInKilograms setup .initial .B = 0 := by
    rw [totalMassInKilograms, hScenario.initialBHasNoPhaseMass .liquid,
      hScenario.initialBHasNoPhaseMass .vapor]
    norm_num
  have hFinalBTotalMass :
      totalMassInKilograms setup .final .B =
        (50000 / 3791 : ℝ) := by
    rw [totalMassInKilograms, hScenario.finalBHasNoLiquidMass,
      hFinalBVaporMass]
    norm_num
  have hTransferredMass :
      massInKilograms setup.transfer.transferredMass =
        (50000 / 3791 : ℝ) := by
    have h := hLaws.tankBMassGainIsTransferredMass
    rw [hFinalBTotalMass, hInitialBTotalMass] at h
    linarith
  have hFinalATotalMass :
      totalMassInKilograms setup .final .A =
        (177745000 / 8950551 : ℝ) := by
    have h := hLaws.tankAMassLossIsTransferredMass
    rw [hInitialTotalMass, hTransferredMass] at h
    norm_num at h ⊢
    linarith
  have hFinalAFill :=
    hLaws.nonEvacuatedContentsFillTank .final .A hFinalANonEvacuated
  rw [totalOccupiedVolumeInCubicMetres, hTankAVolume] at hFinalAFill
  have hFinalALiquidLaw :=
    hLaws.saturatedPhaseMassVolumeLaw .final .A .liquid
      hFinalANonEvacuated
  have hFinalAVaporLaw :=
    hLaws.saturatedPhaseMassVolumeLaw .final .A .vapor
      hFinalANonEvacuated
  rw [hFinalATemperature,
    hReferenceData.saturatedLiquidSpecificVolume] at hFinalALiquidLaw
  rw [hFinalATemperature,
    hReferenceData.saturatedVaporSpecificVolume] at hFinalAVaporLaw
  have hFinalAVaporMass :
      phaseMassInKilograms setup .final .A .vapor =
        (1717755000 / 134766259 : ℝ) := by
    have hMass := hFinalATotalMass
    rw [totalMassInKilograms] at hMass
    norm_num at hFinalAFill hFinalALiquidLaw hFinalAVaporLaw hMass ⊢
    linarith
  constructor
  · simp only [qualityChangeInTankA, vaporQuality]
    rw [hFinalAVaporMass, hFinalATotalMass, hInitialVaporMass,
      hInitialTotalMass]
    norm_num [abs_lt]
  · intro choice
    cases choice <;>
      simp only [IsReportedQualityChange, displayedQualityChange,
        qualityChangeInTankA, vaporQuality]
    all_goals
      rw [hFinalAVaporMass, hFinalATotalMass, hInitialVaporMass,
        hInitialTotalMass]
      norm_num [abs_lt]
    all_goals decide

end PhyXMiniProblems.ProblemPhyXMini0444
