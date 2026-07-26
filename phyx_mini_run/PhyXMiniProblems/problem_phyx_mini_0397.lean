import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0397

open Dimension

/-!
# Final specific volume after opening a valve between two rigid water tanks

Tank `A` initially has pressure `200 kPa`, specific volume `0.5 m³/kg`,
and volume `1 m³`. Tank `B` initially contains `3.5 kg` of water at
`0.5 MPa` and `400 °C`. Opening the valve produces one uniform final state
in the closed pair of rigid tanks.

Physical volumes, masses, specific volumes, pressures, and absolute
temperatures are represented by unit-independent Physlib quantities. Real
numbers occur only as calibrated readouts in the units printed in the source
and in the displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of specific volume, `L³ M⁻¹`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- A nonnegative, unit-independent physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent thermodynamic specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-- Read a physical volume in the cube of the selected length unit. -/
def volumeReadout
    (lengthUnit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := lengthUnit}).val : ℝ)

/-- Read a physical mass in the selected mass unit. -/
def massReadout (massUnit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := massUnit}).val : ℝ)

/--
Read a specific volume in cubic selected-length-units per selected mass unit.
-/
def specificVolumeReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Cubic-metre readout used by the problem statement. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Kilogram readout used by the problem statement. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Cubic-metre-per-kilogram readout used by the answer choices. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  specificVolumeReadout MassUnit.kilograms LengthUnit.meters specificVolume

/-- Read a dimensionful pressure in coherent SI units (pascals). -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used for both initial pressures. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-!
Physlib supplies an absolute nonnegative `Temperature`, but not an affine
Celsius measurement API. This interface attaches a Celsius readout to the
same absolute physical temperature and records the affine calibration.
-/
structure CelsiusTemperatureReading where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ
  celsiusKelvinCalibration :
    absoluteTemperature.toReal = degreesCelsius + 5463 / 20

/-! ## Water states, tanks, valve process, and supplied figure -/

/-- The two tank labels printed in the raster. -/
inductive TankLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The substance occupying either tank. -/
inductive FluidSubstance where
  | water
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic region of a water state. -/
inductive WaterRegion where
  | compressedLiquid
  | saturatedMixture
  | superheatedVapor
  | other
  deriving DecidableEq, Repr

/-- Closed or open status of the valve joining the tanks. -/
inductive ValveStatus where
  | closed
  | open
  deriving DecidableEq, Repr

/-- An equilibrium thermodynamic state of the tank contents. -/
structure ThermodynamicState where
  pressure : DimPressure
  temperature : CelsiusTemperatureReading
  specificVolume : SpecificVolumeQuantity
  waterRegion : WaterRegion

/-- One rigid tank together with its independent initial observables. -/
structure RigidTank where
  printedLabel : TankLabel
  contents : FluidSubstance
  internalVolume : VolumeQuantity
  initialMass : MassQuantity
  initialState : ThermodynamicState

/-- Objects visibly present in the supplied two-tank raster. -/
inductive FigureObject where
  | rectangularTankA
  | rectangularTankB
  | horizontalConnectingPipe
  | centralCircularValve
  | valveCrossMark
  | blueTankContents
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative geometry of the primary figure. It contains no numerical
specific-volume answer or thermodynamic property-table entry.
-/
structure SuppliedTwoTankFigure where
  tankLabelShown : TankLabel → Bool
  objectShown : FigureObject → Bool
  tankAIsLeftOfTankB : Bool
  pipeConnectsAAndB : Bool
  valveLiesBetweenTanks : Bool

/--
An external equilibrium-water property table. The lookup returns a physical
specific volume from physical pressure and absolute temperature inputs.
-/
structure WaterPropertyTable where
  specificVolumeAt :
    DimPressure → Temperature → SpecificVolumeQuantity

/-!
The combined final condition has one thermodynamic state shared by both tanks.
Its total mass, total occupied volume, and specific volume are independent
physical fields until the governing conservation laws are assumed below.
-/
structure UniformFinalCondition where
  state : ThermodynamicState
  totalMass : MassQuantity
  totalOccupiedVolume : VolumeQuantity
  sameStateInBothTanks : Bool

/-- The complete two-rigid-tank valve-opening experiment. -/
structure TwoTankValveSetup where
  tank : TankLabel → RigidTank
  figure : SuppliedTwoTankFigure
  waterTable : WaterPropertyTable
  initialValveStatus : ValveStatus
  finalValveStatus : ValveStatus
  pairIsClosedToMassTransfer : Bool
  bothTankWallsAreRigid : Bool
  finalCondition : UniformFinalCondition

/-! ## Assumptions: scenario, figure, readouts, reference data, and laws -/

/-- Qualitative facts stated by the physical scenario. -/
structure MatchesTwoTankWaterScenario (setup : TwoTankValveSetup) : Prop where
  tankLabelsMatch : ∀ label, (setup.tank label).printedLabel = label
  bothTanksContainWater :
    ∀ label, (setup.tank label).contents = .water
  valveInitiallyClosed : setup.initialValveStatus = .closed
  valveOpened : setup.finalValveStatus = .open
  closedCombinedSystem : setup.pairIsClosedToMassTransfer = true
  rigidTankPair : setup.bothTankWallsAreRigid = true
  uniformFinalState : setup.finalCondition.sameStateInBothTanks = true

/-- Qualitative labels, objects, and left-to-right geometry read from the image. -/
structure MatchesSuppliedTwoTankFigure
    (figure : SuppliedTwoTankFigure) : Prop where
  everyTankLabelShown : ∀ label, figure.tankLabelShown label = true
  everyDepictedObjectShown : ∀ object, figure.objectShown object = true
  tankAIsOnTheLeft : figure.tankAIsLeftOfTankB = true
  pipeJoinsTheTanks : figure.pipeConnectsAAndB = true
  centralValveBetweenTanks : figure.valveLiesBetweenTanks = true

/-!
The six numerical readouts explicitly stated in the problem. In particular,
the mass of tank `A` and volume of tank `B` are not supplied here.
-/
structure MatchesProblemReadouts (setup : TwoTankValveSetup) : Prop where
  tankAPressureKilopascals :
    pressureInKilopascals (setup.tank .A).initialState.pressure = 200
  tankASpecificVolumeCubicMetersPerKilogram :
    specificVolumeInCubicMetersPerKilogram
      (setup.tank .A).initialState.specificVolume = 1 / 2
  tankAVolumeCubicMeters :
    volumeInCubicMeters (setup.tank .A).internalVolume = 1
  tankBMassKilograms :
    massInKilograms (setup.tank .B).initialMass = 7 / 2
  tankBPressureKilopascals :
    pressureInKilopascals (setup.tank .B).initialState.pressure = 500
  tankBTemperatureDegreesCelsius :
    (setup.tank .B).initialState.temperature.degreesCelsius = 400

/-!
Physical interpretation of the `0.5 MPa`, `400 °C` water state: it is in the
superheated-vapor region and its specific volume is obtained from the water
property table. This is a constitutive state relation, not the requested
final combined specific volume.
-/
structure SatisfiesTankBWaterPropertyModel
    (setup : TwoTankValveSetup) : Prop where
  tankBIsSuperheatedWater :
    (setup.tank .B).initialState.waterRegion = .superheatedVapor
  tankBSpecificVolumeFromTable :
    (setup.tank .B).initialState.specificVolume =
      setup.waterTable.specificVolumeAt
        (setup.tank .B).initialState.pressure
        (setup.tank .B).initialState.temperature.absoluteTemperature

/-!
Reference property-table readout needed to make the numerical problem
determinate: superheated water at `0.5 MPa` and `400 °C` has specific volume
`0.6173 m³/kg` at the precision used by the source exercise.
-/
structure MatchesReferenceWaterPropertyData
    (setup : TwoTankValveSetup) : Prop where
  tankBTableSpecificVolumeCubicMetersPerKilogram :
    specificVolumeInCubicMetersPerKilogram
      (setup.waterTable.specificVolumeAt
        (setup.tank .B).initialState.pressure
        (setup.tank .B).initialState.temperature.absoluteTemperature) =
      6173 / 10000

/-- Positivity conditions selecting physically meaningful tank states. -/
structure HasPhysicalTwoTankParameters
    (setup : TwoTankValveSetup) : Prop where
  initialPressurePositive :
    ∀ label, 0 < pressureInPascals (setup.tank label).initialState.pressure
  initialVolumePositive :
    ∀ label, 0 < volumeInCubicMeters (setup.tank label).internalVolume
  initialMassPositive :
    ∀ label, 0 < massInKilograms (setup.tank label).initialMass
  initialSpecificVolumePositive :
    ∀ label,
      0 < specificVolumeInCubicMetersPerKilogram
        (setup.tank label).initialState.specificVolume
  initialAbsoluteTemperaturePositive :
    ∀ label,
      0 < (setup.tank label).initialState.temperature.absoluteTemperature.toReal
  finalMassPositive :
    0 < massInKilograms setup.finalCondition.totalMass
  finalVolumePositive :
    0 < volumeInCubicMeters setup.finalCondition.totalOccupiedVolume
  finalSpecificVolumePositive :
    0 < specificVolumeInCubicMetersPerKilogram
      setup.finalCondition.state.specificVolume

/-!
Governing laws for opening a valve between two closed rigid tanks:

* each tank obeys `V = m v` in any coherent mass/length units;
* rigidity makes the final occupied volume the sum of tank volumes;
* total water mass is conserved;
* the uniform final state also obeys `V_total = m_total v_final`.

No field mentions an answer choice or the requested numerical final value.
-/
structure SatisfiesRigidTankMassVolumeLaws
    (setup : TwoTankValveSetup) : Prop where
  initialTankMassVolumeLaw :
    ∀ (label : TankLabel) (massUnit : MassUnit)
        (lengthUnit : LengthUnit),
      volumeReadout lengthUnit (setup.tank label).internalVolume =
        massReadout massUnit (setup.tank label).initialMass *
          specificVolumeReadout massUnit lengthUnit
            (setup.tank label).initialState.specificVolume
  rigidTotalVolumeLaw :
    ∀ lengthUnit : LengthUnit,
      volumeReadout lengthUnit setup.finalCondition.totalOccupiedVolume =
        volumeReadout lengthUnit (setup.tank .A).internalVolume +
          volumeReadout lengthUnit (setup.tank .B).internalVolume
  totalMassConservationLaw :
    ∀ massUnit : MassUnit,
      massReadout massUnit setup.finalCondition.totalMass =
        massReadout massUnit (setup.tank .A).initialMass +
          massReadout massUnit (setup.tank .B).initialMass
  finalMassVolumeLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      volumeReadout lengthUnit setup.finalCondition.totalOccupiedVolume =
        massReadout massUnit setup.finalCondition.totalMass *
          specificVolumeReadout massUnit lengthUnit
            setup.finalCondition.state.specificVolume

/-! ## Answer metadata and current target -/

/-- Labels printed beside the four candidate final specific volumes. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Specific volume in `m³/kg` printed beside each answer label. -/
def displayedSpecificVolumeInCubicMetersPerKilogram : AnswerChoice → ℝ
  | .A => 5963 / 10000
  | .B => 2873 / 5000
  | .C => 314 / 625
  | .D => 5123 / 10000

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
A choice agrees with the physical final specific volume when both are reported
to the four decimal places used by the answer list.
-/
def IsReportedSpecificVolumeChoice
    (setup : TwoTankValveSetup) (choice : AnswerChoice) : Prop :=
  round
      (10000 * specificVolumeInCubicMetersPerKilogram
        setup.finalCondition.state.specificVolume) =
    round
      (10000 * displayedSpecificVolumeInCubicMetersPerKilogram choice)

/-!
Tank `A` initially contains `2 kg`. The reference table gives tank `B`
volume `3.5 * 0.6173 = 2.16055 m³`. Thus the closed rigid pair has total
volume `3.16055 m³`, total mass `5.5 kg`, and final specific volume

`v_f = 63211 / 110000 m³/kg = 0.574645... m³/kg`.

This rounds to the displayed `0.5746 m³/kg`, uniquely answer choice B.

Blueprint: `thm:physics:phyx_mini_0397:target`.
-/
theorem final_specific_volume_after_opening_valve
    (setup : TwoTankValveSetup)
    (hScenario : MatchesTwoTankWaterScenario setup)
    (hFigure : MatchesSuppliedTwoTankFigure setup.figure)
    (hReadouts : MatchesProblemReadouts setup)
    (hWaterModel : SatisfiesTankBWaterPropertyModel setup)
    (hReferenceData : MatchesReferenceWaterPropertyData setup)
    (hPhysical : HasPhysicalTwoTankParameters setup)
    (hLaws : SatisfiesRigidTankMassVolumeLaws setup) :
    specificVolumeInCubicMetersPerKilogram
        setup.finalCondition.state.specificVolume = 63211 / 110000 ∧
      IsReportedSpecificVolumeChoice setup .B ∧
      ∀ choice : AnswerChoice,
        IsReportedSpecificVolumeChoice setup choice → choice = .B := by
  have hTankAVolumeLaw :=
    hLaws.initialTankMassVolumeLaw
      .A MassUnit.kilograms LengthUnit.meters
  have hTankBVolumeLaw :=
    hLaws.initialTankMassVolumeLaw
      .B MassUnit.kilograms LengthUnit.meters
  have hRigidTotalVolume :=
    hLaws.rigidTotalVolumeLaw LengthUnit.meters
  have hTotalMass :=
    hLaws.totalMassConservationLaw MassUnit.kilograms
  have hFinalMassVolume :=
    hLaws.finalMassVolumeLaw
      MassUnit.kilograms LengthUnit.meters
  have hTankBSpecificVolume :
      specificVolumeInCubicMetersPerKilogram
          (setup.tank .B).initialState.specificVolume =
        6173 / 10000 := by
    rw [hWaterModel.tankBSpecificVolumeFromTable]
    exact hReferenceData.tankBTableSpecificVolumeCubicMetersPerKilogram
  have hTankAVolume :
      volumeReadout LengthUnit.meters
          (setup.tank .A).internalVolume = 1 := by
    simpa [volumeInCubicMeters] using hReadouts.tankAVolumeCubicMeters
  have hTankASpecificVolume :
      specificVolumeReadout MassUnit.kilograms LengthUnit.meters
          (setup.tank .A).initialState.specificVolume = 1 / 2 := by
    simpa [specificVolumeInCubicMetersPerKilogram] using
      hReadouts.tankASpecificVolumeCubicMetersPerKilogram
  have hTankBMass :
      massReadout MassUnit.kilograms
          (setup.tank .B).initialMass = 7 / 2 := by
    simpa [massInKilograms] using hReadouts.tankBMassKilograms
  have hTankBSpecificVolumeReadout :
      specificVolumeReadout MassUnit.kilograms LengthUnit.meters
          (setup.tank .B).initialState.specificVolume = 6173 / 10000 := by
    simpa [specificVolumeInCubicMetersPerKilogram] using
      hTankBSpecificVolume
  have hTankAMass :
      massReadout MassUnit.kilograms
          (setup.tank .A).initialMass = 2 := by
    nlinarith [hTankAVolumeLaw, hTankAVolume, hTankASpecificVolume]
  have hTankBVolume :
      volumeReadout LengthUnit.meters
          (setup.tank .B).internalVolume = 43211 / 20000 := by
    nlinarith [hTankBVolumeLaw, hTankBMass,
      hTankBSpecificVolumeReadout]
  have hFinalTotalVolume :
      volumeReadout LengthUnit.meters
          setup.finalCondition.totalOccupiedVolume = 63211 / 20000 := by
    nlinarith [hRigidTotalVolume, hTankAVolume, hTankBVolume]
  have hFinalTotalMass :
      massReadout MassUnit.kilograms
          setup.finalCondition.totalMass = 11 / 2 := by
    nlinarith [hTotalMass, hTankAMass, hTankBMass]
  have hFinalSpecificVolume :
      specificVolumeInCubicMetersPerKilogram
          setup.finalCondition.state.specificVolume =
        63211 / 110000 := by
    simp only [specificVolumeInCubicMetersPerKilogram]
    nlinarith [hFinalMassVolume, hFinalTotalVolume, hFinalTotalMass]
  refine ⟨hFinalSpecificVolume, ?_, ?_⟩
  · norm_num [IsReportedSpecificVolumeChoice,
      displayedSpecificVolumeInCubicMetersPerKilogram, hFinalSpecificVolume]
  · intro choice hChoice
    cases choice with
    | A =>
        norm_num [IsReportedSpecificVolumeChoice,
          displayedSpecificVolumeInCubicMetersPerKilogram,
          hFinalSpecificVolume] at hChoice
    | B =>
        rfl
    | C =>
        norm_num [IsReportedSpecificVolumeChoice,
          displayedSpecificVolumeInCubicMetersPerKilogram,
          hFinalSpecificVolume] at hChoice
    | D =>
        norm_num [IsReportedSpecificVolumeChoice,
          displayedSpecificVolumeInCubicMetersPerKilogram,
          hFinalSpecificVolume] at hChoice

end PhyXMiniProblems.ProblemPhyXMini0397
