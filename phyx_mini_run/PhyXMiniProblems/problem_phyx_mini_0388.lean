import Mathlib
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0388

open Dimension

/-!
# Absolute pressure in a light-oil pipe from a two-fluid manometer

The primary image shows a pipe carrying light oil connected to the left arm of
a U-tube.  The oil lies above water in that arm, while the right arm contains
water and is open to an atmosphere labelled `P₀ = 101 kPa`.  With the bottom
of the U-tube as datum, the pipe tap and oil--water interface are respectively
`0.3 m` and `0.1 m` high.  The right water surface is `0.7 m` above that
interface.

Physical lengths, mass densities, acceleration, and pressures are represented
by unit-independent Physlib quantities.  Real numbers occur only as coherent
SI readouts and as the displayed multiple-choice data.  The image does not
supply either fluid density or a numerical value of gravitational acceleration,
so the source-supported result below leaves those quantities as parameters.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Absolute pressure, represented using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Kilogram-per-cubic-metre readout of a physical mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout of an absolute pressure. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Apparatus roles and primary-figure transcription -/

/-- The two arms of the U-tube, named by their boundary conditions. -/
inductive ManometerArm where
  | pipeConnected
  | openToAtmosphere
  deriving DecidableEq, Fintype, Repr

/-- Fluids named in the problem and primary image. -/
inductive ManometerFluid where
  | lightOil
  | water
  deriving DecidableEq, Fintype, Repr

/-- The three vertical dimensions printed in the image. -/
inductive FigureHeightLabel where
  | pipeTapAboveDatum
  | oilWaterInterfaceAboveDatum
  | rightWaterSurfaceAboveInterface
  deriving DecidableEq, Fintype, Repr

/-!
Structured transcription of image `388.png`.  The `0.7 m` arrow extends from
the oil--water interface level to the right free surface; it is not measured
from the bottom datum.
-/
structure PrimaryManometerFigure where
  pipeConnectedArm : ManometerArm
  atmosphereOpenArm : ManometerArm
  upperFluid : ManometerArm → ManometerFluid
  lowerUFluid : ManometerFluid
  heightLabel : FigureHeightLabel → LengthQuantity
  pressureLabelP₀ : PressureQuantity
  showsUShapedTube : Bool
  showsPipeFlowArrow : Bool
  showsOilWaterInterface : Bool

/-!
The apparatus and its independent physical observables.  The pressure at the
oil--water interface is explicit so that hydrostatics can be imposed once
through each fluid column.  No requested pressure value is defined here.
-/
structure PipeManometerSetup where
  figure : PrimaryManometerFigure
  pipeFluid : ManometerFluid
  lowerManometerFluid : ManometerFluid
  pipeTapElevation : LengthQuantity
  oilWaterInterfaceElevation : LengthQuantity
  rightWaterSurfaceRiseAboveInterface : LengthQuantity
  lightOilMassDensity : MassDensityQuantity
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  atmosphericAbsolutePressure : PressureQuantity
  pipeAbsolutePressure : PressureQuantity
  oilWaterInterfaceAbsolutePressure : PressureQuantity

/-!
Qualitative assignments and scalar readouts taken directly from the primary
image.  In particular, the atmosphere label is an absolute pressure.  This
predicate contains no pipe-pressure answer.
-/
structure MatchesPrimaryFigure (setup : PipeManometerSetup) : Prop where
  pipeCarriesLightOil : setup.pipeFluid = .lightOil
  lowerFluidIsWater : setup.lowerManometerFluid = .water
  pipeArmAssignment : setup.figure.pipeConnectedArm = .pipeConnected
  openArmAssignment : setup.figure.atmosphereOpenArm = .openToAtmosphere
  upperFluidOnPipeSide :
    setup.figure.upperFluid .pipeConnected = .lightOil
  upperFluidOnOpenSide :
    setup.figure.upperFluid .openToAtmosphere = .water
  lowerFigureFluid : setup.figure.lowerUFluid = .water
  uTubeShown : setup.figure.showsUShapedTube = true
  pipeFlowArrowShown : setup.figure.showsPipeFlowArrow = true
  oilWaterInterfaceShown : setup.figure.showsOilWaterInterface = true
  pipeTapMarkerMatches :
    setup.figure.heightLabel .pipeTapAboveDatum = setup.pipeTapElevation
  interfaceMarkerMatches :
    setup.figure.heightLabel .oilWaterInterfaceAboveDatum =
      setup.oilWaterInterfaceElevation
  rightSurfaceMarkerMatches :
    setup.figure.heightLabel .rightWaterSurfaceAboveInterface =
      setup.rightWaterSurfaceRiseAboveInterface
  pressureLabelMatches :
    setup.figure.pressureLabelP₀ = setup.atmosphericAbsolutePressure
  pipeTapElevationMeters : lengthInMeters setup.pipeTapElevation = 3 / 10
  interfaceElevationMeters :
    lengthInMeters setup.oilWaterInterfaceElevation = 1 / 10
  rightSurfaceRiseMeters :
    lengthInMeters setup.rightWaterSurfaceRiseAboveInterface = 7 / 10
  atmosphericPressurePascals :
    pressureInPascals setup.atmosphericAbsolutePressure = 101000

/-- Positivity and geometric ordering required for the static-fluid model. -/
structure HasPhysicalManometerParameters
    (setup : PipeManometerSetup) : Prop where
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericAbsolutePressure
  pipePressurePositive :
    0 < pressureInPascals setup.pipeAbsolutePressure
  interfacePressurePositive :
    0 < pressureInPascals setup.oilWaterInterfaceAbsolutePressure
  lightOilDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.lightOilMassDensity
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterMassDensity
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  interfaceBelowPipeTap :
    lengthInMeters setup.oilWaterInterfaceElevation <
      lengthInMeters setup.pipeTapElevation
  rightSurfaceAboveInterface :
    0 < lengthInMeters setup.rightWaterSurfaceRiseAboveInterface

/-! ## Governing hydrostatic laws -/

/-!
For a static fluid, pressure increases by `ρ g Δh` when descending.  Applied
from the pipe tap through the oil and from the open free surface through the
water, both routes reach the same oil--water interface pressure.  These are
governing relations, not the solved pipe-pressure formula.
-/
structure SatisfiesTwoFluidHydrostaticLaws
    (setup : PipeManometerSetup) : Prop where
  interfacePressureFromOilColumn :
    pressureInPascals setup.oilWaterInterfaceAbsolutePressure =
      pressureInPascals setup.pipeAbsolutePressure +
        densityInKilogramsPerCubicMeter setup.lightOilMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (lengthInMeters setup.pipeTapElevation -
            lengthInMeters setup.oilWaterInterfaceElevation)
  interfacePressureFromWaterColumn :
    pressureInPascals setup.oilWaterInterfaceAbsolutePressure =
      pressureInPascals setup.atmosphericAbsolutePressure +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.rightWaterSurfaceRiseAboveInterface

/-! ## Derived pressure and displayed-answer metadata -/

/-!
Eliminating the common interface pressure gives the signed two-fluid
manometer relation for the unknown pipe pressure.
-/
lemma pipe_pressure_from_column_balance
    (setup : PipeManometerSetup)
    (hLaws : SatisfiesTwoFluidHydrostaticLaws setup) :
    pressureInPascals setup.pipeAbsolutePressure =
      pressureInPascals setup.atmosphericAbsolutePressure +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.rightWaterSurfaceRiseAboveInterface -
        densityInKilogramsPerCubicMeter setup.lightOilMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (lengthInMeters setup.pipeTapElevation -
            lengthInMeters setup.oilWaterInterfaceElevation) := by
  sorry

/-!
The strongest pressure relation determined by the primary image and the
hydrostatic laws alone.  It specializes the atmospheric pressure and three
figure heights while leaving the omitted fluid densities and gravitational
acceleration as physical parameters.
-/
lemma pipe_pressure_from_primary_figure
    (setup : PipeManometerSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hLaws : SatisfiesTwoFluidHydrostaticLaws setup) :
    pressureInPascals setup.pipeAbsolutePressure =
      101000 +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration * (7 / 10) -
        densityInKilogramsPerCubicMeter setup.lightOilMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration * ((3 / 10) - (1 / 10)) := by
  sorry

/-- Labels of the four pressure choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Absolute-pressure value in kilopascals displayed beside each choice.  The
dataset records choice B, whose displayed value is `532 / 5 = 106.4`; this
table is source metadata and is not used to determine the physical pressure.
-/
def displayedAbsolutePressureKilopascals : AnswerChoice → ℝ
  | .A => 490
  | .B => 532 / 5
  | .C => 154
  | .D => 51 / 5

/-!
The absolute pipe pressure satisfies the source-supported two-fluid column
balance after substituting all readouts present in the primary image.  The
omitted fluid densities and gravitational acceleration remain physical
parameters, so no displayed numerical answer is asserted.

This formalizes blueprint label `thm:physics:phyx_mini_0388:target`.
-/
theorem problem_phyx_mini_0388
    (setup : PipeManometerSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalManometerParameters setup)
    (hLaws : SatisfiesTwoFluidHydrostaticLaws setup) :
    pressureInPascals setup.pipeAbsolutePressure =
      101000 +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration * (7 / 10) -
        densityInKilogramsPerCubicMeter setup.lightOilMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration * ((3 / 10) - (1 / 10)) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0388
