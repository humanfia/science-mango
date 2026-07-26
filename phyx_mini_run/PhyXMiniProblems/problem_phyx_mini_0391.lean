import Mathlib
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0391

open Dimension

/-!
# Pressure drop measured by a mercury U-tube manometer

Air flows from left to right through an apparatus containing an orifice. A
mercury U-tube connected across the orifice shows a `200 mm` difference between
its liquid levels. The apparatus is at `5 °C`, and the local gravitational
acceleration is `9.5 m/s²`.

Physical length, temperature, mass density, acceleration, and pressure are
represented by unit-independent Physlib quantities. Real numbers occur only as
readouts in explicitly named units or as displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the readout unit. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative absolute temperature, independent of the readout unit. -/
abbrev TemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a mass density in a selected mass unit per selected length unit cubed. -/
def densityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : MassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read an acceleration in selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Millimeter readout of a physical length. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Kelvin readout of an absolute temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/-- Celsius readout obtained from the coherent Kelvin readout. -/
def temperatureInDegreesCelsius (temperature : TemperatureQuantity) : ℝ :=
  temperatureInKelvins temperature - (27315 / 100 : ℝ)

/-- Kilogram-per-cubic-meter readout of a mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  densityReadout MassUnit.kilograms LengthUnit.meters density

/-- Meter-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Pascal readout of a pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout of a pressure difference. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Apparatus, figure labels, and physical roles -/

/-- The sides of the orifice at which air pressure is sampled. -/
inductive PressureTap where
  | upstream
  | downstream
  deriving DecidableEq, Fintype, Repr

/-- The two arms visible in the U-tube drawing. -/
inductive ManometerArm where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Fluids relevant to the apparatus. -/
inductive ApparatusFluid where
  | air
  | mercury
  | other
  deriving DecidableEq, Repr

/-- Literal text labels visible in the supplied bitmap. -/
inductive FigureTextLabel where
  | air
  | g
  deriving DecidableEq, Fintype, Repr

/-- Direction of the arrows drawn in the air passage. -/
inductive AirflowDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-!
The geometric and qualitative evidence visible in the supplied bitmap. The
height difference is a dimensionful quantity but receives its numerical
`200 mm` readout separately from the problem statement.
-/
structure OrificeManometerFigure where
  labelShown : FigureTextLabel → Bool
  airflowDirection : AirflowDirection
  uTubeShown : Bool
  unequalLiquidLevelsShown : Bool
  higherLiquidLevelArm : ManometerArm
  lowerLiquidLevelArm : ManometerArm
  liquidLevelHeightDifference : LengthQuantity
  verticalProbeShown : Bool
  gravityArrowPointsDownward : Bool

/-!
Independent physical quantities and apparatus roles. In particular, the
pressure drop is an independent pressure quantity: it is not defined from the
recorded answer or from the hydrostatic formula.
-/
structure OrificeManometerSetup where
  figure : OrificeManometerFigure
  flowingFluid : ApparatusFluid
  manometerFluid : ApparatusFluid
  pressureAtTap : PressureTap → DimPressure
  pressureDrop : DimPressure
  armConnectedToTap : PressureTap → ManometerArm
  heightDifference : LengthQuantity
  ambientTemperature : TemperatureQuantity
  manometerFluidMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  orificePresent : Bool
  neglectFlowingFluidColumnWeight : Bool

/-! ## Figure/data readouts and governing laws -/

/-- Evidence read directly from the primary bitmap `phyx_data/test_image/391.png`. -/
structure MatchesPrimaryFigure (setup : OrificeManometerSetup) : Prop where
  airLabelShown : setup.figure.labelShown .air = true
  gravityLabelShown : setup.figure.labelShown .g = true
  airFlowsLeftToRight : setup.figure.airflowDirection = .leftToRight
  uTubeIsVisible : setup.figure.uTubeShown = true
  liquidLevelsAreUnequal : setup.figure.unequalLiquidLevelsShown = true
  rightLevelIsHigher : setup.figure.higherLiquidLevelArm = .right
  leftLevelIsLower : setup.figure.lowerLiquidLevelArm = .left
  figureHeightIsMeasuredHeight :
    setup.figure.liquidLevelHeightDifference = setup.heightDifference
  probeIsVisible : setup.figure.verticalProbeShown = true
  gravityArrowIsDownward : setup.figure.gravityArrowPointsDownward = true

/-!
Textual apparatus roles and numerical readouts supplied in the problem. The
two pressure taps lie on opposite sides of the orifice; the higher upstream
pressure depresses the mercury in the left arm in the pictured orientation.
-/
structure MatchesProblemData (setup : OrificeManometerSetup) : Prop where
  flowingFluidIsAir : setup.flowingFluid = .air
  manometerFluidIsMercury : setup.manometerFluid = .mercury
  apparatusContainsOrifice : setup.orificePresent = true
  upstreamTapUsesLeftArm : setup.armConnectedToTap .upstream = .left
  downstreamTapUsesRightArm : setup.armConnectedToTap .downstream = .right
  measuredHeightInMillimeters :
    lengthInMillimeters setup.heightDifference = 200
  localGravityReadout :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 95 / 10
  gasColumnWeightIsNeglected : setup.neglectFlowingFluidColumnWeight = true

/-!
Mercury property-table calibration at the stated operating temperature. The
density value is a material-data readout, not the requested pressure answer.
-/
structure UsesMercuryPropertyDataAtFiveDegrees
    (setup : OrificeManometerSetup) : Prop where
  ambientTemperatureReadout :
    temperatureInDegreesCelsius setup.ambientTemperature = 5
  mercuryDensityReadout :
    densityInKilogramsPerCubicMeter setup.manometerFluidMassDensity = 13600

/-!
The apparatus-specific governing laws, expressed in coherent SI readouts.
The second field is the U-tube hydrostatic balance `Δp = ρ g h` under the
stated heavy-manometer-liquid approximation.
-/
structure SatisfiesOrificeManometerLaws
    (setup : OrificeManometerSetup) : Prop where
  pressureDropIsUpstreamMinusDownstream :
    pressureInPascals setup.pressureDrop =
      pressureInPascals (setup.pressureAtTap .upstream) -
        pressureInPascals (setup.pressureAtTap .downstream)
  hydrostaticBalance :
    pressureInPascals setup.pressureDrop =
      densityInKilogramsPerCubicMeter setup.manometerFluidMassDensity *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters setup.heightDifference

/-! ## Multiple-choice presentation and theorem targets -/

/-- The four answer choices in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed pressure-drop values, in kilopascals. -/
def displayedPressureInKilopascals : AnswerChoice → ℝ
  | .A => 490
  | .B => 2584 / 100
  | .C => 154
  | .D => 102 / 10

/-- Dataset metadata; this declaration is not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A choice matches the pressure drop derived for the setup. -/
def MatchesDisplayedPressure
    (setup : OrificeManometerSetup) (choice : AnswerChoice) : Prop :=
  pressureInKilopascals setup.pressureDrop =
    displayedPressureInKilopascals choice

/-- A choice is the unique displayed value matching the derived pressure drop. -/
def IsUniqueMatchingDisplayedPressure
    (setup : OrificeManometerSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPressure setup choice ∧
    ∀ other, MatchesDisplayedPressure setup other → other = choice

/-!
The requested answer: the pressure drop is `25.84 kPa`, and choice B is the
unique displayed answer that agrees with the physical model.

Corresponds to blueprint label `thm:physics:phyx_mini_0391:target`.
-/
theorem problem_phyx_mini_0391
    (setup : OrificeManometerSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hData : MatchesProblemData setup)
    (hMercury : UsesMercuryPropertyDataAtFiveDegrees setup)
    (hLaws : SatisfiesOrificeManometerLaws setup) :
    pressureInKilopascals setup.pressureDrop = 2584 / 100 ∧
      IsUniqueMatchingDisplayedPressure setup .B := by
  have millimeters_eq_meters (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    have hunit := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
    have hval := congrArg WithDim.val hunit
    have hval_real := congrArg (fun value : NNReal => (value : ℝ)) hval
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.millimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hval_real ⊢
    exact hval_real
  have hHeight :
      lengthInMeters setup.heightDifference = (1 : ℝ) / 5 := by
    nlinarith only [hData.measuredHeightInMillimeters,
      millimeters_eq_meters setup.heightDifference]
  have hPressurePa :
      pressureInPascals setup.pressureDrop = 25840 := by
    rw [hLaws.hydrostaticBalance, hMercury.mercuryDensityReadout,
      hData.localGravityReadout, hHeight]
    norm_num
  have hPressureKPa :
      pressureInKilopascals setup.pressureDrop = 2584 / 100 := by
    rw [pressureInKilopascals, hPressurePa]
    norm_num
  refine ⟨hPressureKPa, ?_⟩
  constructor
  · simpa [MatchesDisplayedPressure, displayedPressureInKilopascals] using
      hPressureKPa
  · intro other hOther
    change pressureInKilopascals setup.pressureDrop =
      displayedPressureInKilopascals other at hOther
    rw [hPressureKPa] at hOther
    cases other with
    | A => norm_num [displayedPressureInKilopascals] at hOther
    | B => rfl
    | C => norm_num [displayedPressureInKilopascals] at hOther
    | D => norm_num [displayedPressureInKilopascals] at hOther

end PhyXMiniProblems.ProblemPhyXMini0391
