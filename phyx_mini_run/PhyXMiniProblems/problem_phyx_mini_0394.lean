import Mathlib
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Pump pressure for a tall-building waterline

A water main and underground pump lie `5 m` below the ground datum.  The
outlet marked `H` is on the top floor, `150 m` above ground, so the water rises
through `155 m`.  The main supplies water at `600 kPa` gauge pressure, and the
required top-floor pressure is `200 kPa` gauge pressure.

Lengths, elevations, mass density, acceleration, and pressure are represented
by dimensionful physical quantities.  Real numbers below are explicitly named
coherent-SI readouts, displayed answer values, or qualitative figure data.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0394

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical elevation relative to the ground datum. -/
abbrev ElevationQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative mass density, with dimension mass per volume. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Coherent-SI metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre readout of a signed elevation. -/
def elevationInMeters (elevation : ElevationQuantity) : ℝ :=
  (elevation UnitChoices.SI).val

/-- Coherent-SI kilogram-per-cubic-metre readout of a mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used by the prose and displayed answer choices. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Apparatus roles and primary-figure vocabulary -/

/-- Fluid transported from the main to the top-floor outlet. -/
inductive PipelineFluid where
  | water
  deriving DecidableEq, Repr

/-- Common reference convention for every line-pressure readout. -/
inductive PressureReference where
  | gaugeRelativeToAtmosphere
  deriving DecidableEq, Repr

/-- Hydraulic locations distinguished by the supplied building diagram. -/
inductive HydraulicLocation where
  | waterMain
  | pumpInlet
  | pumpOutlet
  | groundDatum
  | topFloorOutletH
  deriving DecidableEq, Fintype, Repr

/-- Text and symbol labels printed in the primary figure. -/
inductive FigureLabel where
  | waterMain
  | pump
  | ground
  | topFloor
  | H
  deriving DecidableEq, Fintype, Repr

/-- The two visible pipe connections in the primary figure. -/
inductive PipeSegment where
  | mainToPump
  | pumpToTopFloor
  deriving DecidableEq, Fintype, Repr

/--
Structured transcription of image `394.png`.  Elevations and dimensioned
markers are physical quantities; the Boolean fields retain qualitative visual
evidence that is not needed in the final arithmetic.
-/
structure TallBuildingWaterlineFigure where
  elevationAt : HydraulicLocation → ElevationQuantity
  buildingHeightMarker : LengthQuantity
  belowGroundDepthMarker : LengthQuantity
  labelVisible : FigureLabel → Bool
  labelAt : FigureLabel → HydraulicLocation
  pipeSegmentEndpoints : PipeSegment → HydraulicLocation × HydraulicLocation
  showsUpwardFlowFromPump : Bool
  showsMultipleBuildingFloors : Bool

/-- Idealization used for the school-level pump calculation. -/
inductive WaterlineRegime where
  | steadyIncompressibleNegligibleVelocityAndFrictionLosses
  deriving DecidableEq, Repr

/-! ## Independent physical setup -/

/--
The building waterline and its independent physical observables.

In particular, `pumpAddedPressure` is an independent pressure increment.  It
is not defined to be any answer-choice value; the governing laws below relate
it to the main, discharge, and top-floor pressures.
-/
structure TallBuildingWaterlineSetup where
  fluid : PipelineFluid
  pressureReference : PressureReference
  regime : WaterlineRegime
  figure : TallBuildingWaterlineFigure
  waterMainPressure : PressureQuantity
  pumpAddedPressure : PressureQuantity
  pumpDischargePressure : PressureQuantity
  topFloorPressure : PressureQuantity
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  totalVerticalLift : LengthQuantity

/-! ## Figure/data readouts and physical assumptions -/

/-- Pressure values stated in the prose and the named working fluid. -/
structure MatchesStatedProblemData
    (setup : TallBuildingWaterlineSetup) : Prop where
  fluidIsWater : setup.fluid = .water
  commonGaugeReference :
    setup.pressureReference = .gaugeRelativeToAtmosphere
  mainPressureKilopascals :
    pressureInKilopascals setup.waterMainPressure = 600
  requestedTopFloorPressureKilopascals :
    pressureInKilopascals setup.topFloorPressure = 200

/--
Primary-image evidence: ground is the zero datum, the water main and pump are
`5 m` below it, and the outlet marked `H` is `150 m` above it.  The pipe runs
from the main through the pump and upward to `H`.
-/
structure MatchesPrimaryBuildingFigure
    (setup : TallBuildingWaterlineSetup) : Prop where
  waterMainElevationMeters :
    elevationInMeters (setup.figure.elevationAt .waterMain) = -5
  pumpInletElevationMeters :
    elevationInMeters (setup.figure.elevationAt .pumpInlet) = -5
  pumpOutletElevationMeters :
    elevationInMeters (setup.figure.elevationAt .pumpOutlet) = -5
  groundElevationMeters :
    elevationInMeters (setup.figure.elevationAt .groundDatum) = 0
  topFloorOutletElevationMeters :
    elevationInMeters (setup.figure.elevationAt .topFloorOutletH) = 150
  buildingHeightMarkerMeters :
    lengthInMeters setup.figure.buildingHeightMarker = 150
  belowGroundDepthMarkerMeters :
    lengthInMeters setup.figure.belowGroundDepthMarker = 5
  waterMainLabelShown : setup.figure.labelVisible .waterMain = true
  pumpLabelShown : setup.figure.labelVisible .pump = true
  groundLabelShown : setup.figure.labelVisible .ground = true
  topFloorLabelShown : setup.figure.labelVisible .topFloor = true
  outletSymbolShown : setup.figure.labelVisible .H = true
  waterMainLabelLocation :
    setup.figure.labelAt .waterMain = .waterMain
  pumpLabelLocation : setup.figure.labelAt .pump = .pumpOutlet
  groundLabelLocation : setup.figure.labelAt .ground = .groundDatum
  topFloorLabelLocation :
    setup.figure.labelAt .topFloor = .topFloorOutletH
  outletSymbolLocation : setup.figure.labelAt .H = .topFloorOutletH
  mainToPumpConnection :
    setup.figure.pipeSegmentEndpoints .mainToPump =
      (.waterMain, .pumpInlet)
  pumpToTopFloorConnection :
    setup.figure.pipeSegmentEndpoints .pumpToTopFloor =
      (.pumpOutlet, .topFloorOutletH)
  upwardFlowShown : setup.figure.showsUpwardFlowFromPump = true
  multipleFloorsShown : setup.figure.showsMultipleBuildingFloors = true

/--
The standard room-temperature water density and school-level terrestrial
gravity calibration that reproduce the precision of the recorded answer.
-/
structure UsesStandardWaterAndGravity
    (setup : TallBuildingWaterlineSetup) : Prop where
  waterDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.waterMassDensity = 998
  terrestrialGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5

/-- Positivity conditions expressing that the pump adds, rather than removes, pressure. -/
structure HasPhysicalWaterlineParameters
    (setup : TallBuildingWaterlineSetup) : Prop where
  densityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterMassDensity
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  liftPositive : 0 < lengthInMeters setup.totalVerticalLift
  mainPressurePositive : 0 < pressureInPascals setup.waterMainPressure
  topFloorPressurePositive : 0 < pressureInPascals setup.topFloorPressure
  pumpAddsNonnegativePressure :
    0 ≤ pressureInPascals setup.pumpAddedPressure

/-! ## Geometry and governing hydraulic laws -/

/-- The stored lift is the elevation difference from the main to outlet `H`. -/
structure SatisfiesFigureLiftGeometry
    (setup : TallBuildingWaterlineSetup) : Prop where
  liftIsTopMinusMainElevation :
    lengthInMeters setup.totalVerticalLift =
      elevationInMeters (setup.figure.elevationAt .topFloorOutletH) -
        elevationInMeters (setup.figure.elevationAt .waterMain)

/-- The pump discharge pressure is the supply pressure plus the pump increment. -/
structure SatisfiesIdealPumpPressureRiseLaw
    (setup : TallBuildingWaterlineSetup) : Prop where
  idealRegime :
    setup.regime =
      .steadyIncompressibleNegligibleVelocityAndFrictionLosses
  dischargePressureBalance :
    pressureInPascals setup.pumpDischargePressure =
      pressureInPascals setup.waterMainPressure +
        pressureInPascals setup.pumpAddedPressure

/--
Hydrostatic pressure balance along the lossless vertical riser: pressure at
the top equals discharge pressure minus `rho * g * Δz`.
-/
structure SatisfiesHydrostaticRiserLaw
    (setup : TallBuildingWaterlineSetup) : Prop where
  topFloorPressureBalance :
    pressureInPascals setup.topFloorPressure =
      pressureInPascals setup.pumpDischargePressure -
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.totalVerticalLift

/-! ## Derived lift and pump requirement -/

/-- The figure geometry gives a total rise of `150 - (-5) = 155 m`. -/
lemma totalVerticalLiftInMeters
    (setup : TallBuildingWaterlineSetup)
    (h_figure : MatchesPrimaryBuildingFigure setup)
    (h_geometry : SatisfiesFigureLiftGeometry setup) :
    lengthInMeters setup.totalVerticalLift = 155 := by
  rw [h_geometry.liftIsTopMinusMainElevation,
    h_figure.topFloorOutletElevationMeters,
    h_figure.waterMainElevationMeters]
  norm_num

/--
Substitution in the two pressure-balance laws gives the unrounded pump
increment `1,115,962 Pa = 1,115.962 kPa`.
-/
lemma requiredPumpAddedPressureInPascals
    (setup : TallBuildingWaterlineSetup)
    (h_data : MatchesStatedProblemData setup)
    (h_figure : MatchesPrimaryBuildingFigure setup)
    (h_standard : UsesStandardWaterAndGravity setup)
    (h_geometry : SatisfiesFigureLiftGeometry setup)
    (h_pump : SatisfiesIdealPumpPressureRiseLaw setup)
    (h_hydrostatic : SatisfiesHydrostaticRiserLaw setup) :
    pressureInPascals setup.pumpAddedPressure = 1115962 := by
  have h_lift : lengthInMeters setup.totalVerticalLift = 155 :=
    totalVerticalLiftInMeters setup h_figure h_geometry
  have h_main :
      pressureInPascals setup.waterMainPressure = 600000 := by
    have h_main_kPa := h_data.mainPressureKilopascals
    unfold pressureInKilopascals at h_main_kPa
    linarith
  have h_top :
      pressureInPascals setup.topFloorPressure = 200000 := by
    have h_top_kPa := h_data.requestedTopFloorPressureKilopascals
    unfold pressureInKilopascals at h_top_kPa
    linarith
  have h_balance := h_hydrostatic.topFloorPressureBalance
  rw [h_top, h_pump.dischargePressureBalance, h_main,
    h_standard.waterDensityKilogramsPerCubicMeter,
    h_standard.terrestrialGravityMetersPerSecondSquared,
    h_lift] at h_balance
  norm_num at h_balance
  linarith

/-! ## Display precision and answer choices -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilopascal value printed beside each displayed answer label. -/
def displayedPressureKilopascals : AnswerChoice → ℝ
  | .A => 490
  | .B => 1116
  | .C => 154
  | .D => 51 / 5

/-- Answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A pressure readout rounds to a displayed whole-kilopascal value. -/
def RoundsToNearestKilopascal
    (pressure : PressureQuantity) (displayed : ℝ) : Prop :=
  displayed - 1 / 2 ≤ pressureInKilopascals pressure ∧
    pressureInKilopascals pressure < displayed + 1 / 2

/-!
The required pump addition is `1,115,962 Pa`, which rounds to `1116 kPa` and
therefore selects recorded answer B.

Blueprint: `thm:physics:phyx_mini_0394:target`.
-/
theorem problem_phyx_mini_0394
    (setup : TallBuildingWaterlineSetup)
    (h_data : MatchesStatedProblemData setup)
    (h_figure : MatchesPrimaryBuildingFigure setup)
    (h_standard : UsesStandardWaterAndGravity setup)
    (h_physical : HasPhysicalWaterlineParameters setup)
    (h_geometry : SatisfiesFigureLiftGeometry setup)
    (h_pump : SatisfiesIdealPumpPressureRiseLaw setup)
    (h_hydrostatic : SatisfiesHydrostaticRiserLaw setup) :
    lengthInMeters setup.totalVerticalLift = 155 ∧
      pressureInPascals setup.pumpAddedPressure = 1115962 ∧
      RoundsToNearestKilopascal setup.pumpAddedPressure
        (displayedPressureKilopascals recordedAnswerChoice) ∧
      displayedPressureKilopascals recordedAnswerChoice = 1116 := by
  have h_lift : lengthInMeters setup.totalVerticalLift = 155 :=
    totalVerticalLiftInMeters setup h_figure h_geometry
  have h_pressure :
      pressureInPascals setup.pumpAddedPressure = 1115962 :=
    requiredPumpAddedPressureInPascals setup h_data h_figure h_standard
      h_geometry h_pump h_hydrostatic
  refine ⟨h_lift, h_pressure, ?_, by rfl⟩
  unfold RoundsToNearestKilopascal pressureInKilopascals
  rw [h_pressure]
  norm_num [displayedPressureKilopascals, recordedAnswerChoice]

end PhyXMiniProblems.ProblemPhyXMini0394
