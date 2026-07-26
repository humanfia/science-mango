import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0487

open Dimension

/-!
# Heat loss through a brick-and-insulation wall

The wall is modeled as two plane layers in series. The supplied figure puts
brick (`R₁`) on the cold, left side and insulation (`R₂`) on the hot, right
side, with heat flowing from the boundary marked `T₁` to that marked `T₂`.

Physical lengths, areas, heat-current magnitudes, and areal thermal
resistances use Physlib's dimension-tagged quantities. Fahrenheit values are
kept as affine instrument readouts alongside Physlib's absolute
`Temperature`.
-/

/-! ## Dimensionful quantities and US-customary readouts -/

/-- A nonnegative physical length, independent of the selected unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical area, using Physlib's existing area quantity. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative heat-transfer rate, carrying the dimension of power. -/
abbrev HeatCurrentQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Areal thermal resistance (an insulation `R`-value), whose dimension is
area times temperature divided by power. -/
abbrev ArealThermalResistanceQuantity : Type :=
  Dimensionful
    (WithDim (Θ𝓭 * T𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Inch readout of a physical length. -/
def lengthInInches (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.inches length

/-- Square-foot readout of a physical area. -/
def areaInSquareFeet (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.feet area

/-- SI watt readout of a physical heat current. -/
def heatCurrentInWatts (heatCurrent : HeatCurrentQuantity) : ℝ :=
  ((heatCurrent UnitChoices.SI).val : ℝ)

/-- The international-table British thermal unit, in joules. -/
def internationalTableBtuInJoules : ℝ :=
  52752792631 / 50000000

/-- Btu-per-hour readout of a physical heat current. -/
def heatCurrentInBtuPerHour (heatCurrent : HeatCurrentQuantity) : ℝ :=
  heatCurrentInWatts heatCurrent * 3600 / internationalTableBtuInJoules

/-- SI square-meter-kelvin-per-watt readout of an areal thermal resistance. -/
def arealThermalResistanceInSquareMeterKelvinPerWatt
    (resistance : ArealThermalResistanceQuantity) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-!
One US insulation R-value, `1 h ft² °F / Btu`, is
`9290304000 / 52752792631 m² K / W`, using exact foot, hour, Fahrenheit-degree,
and international-table-Btu conversions.
-/
def oneImperialRValueInSquareMeterKelvinPerWatt : ℝ :=
  9290304000 / 52752792631

/-- US insulation R-value readout, in `h ft² °F / Btu`. -/
def arealThermalResistanceInImperialRValue
    (resistance : ArealThermalResistanceQuantity) : ℝ :=
  arealThermalResistanceInSquareMeterKelvinPerWatt resistance /
    oneImperialRValueInSquareMeterKelvinPerWatt

/-!
Fahrenheit is affine, whereas Physlib's temperature units preserve absolute
zero. We therefore retain both a physical absolute temperature and the
thermometer readout. Only a temperature difference enters the heat law.
-/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  fahrenheitReadout : ℝ

/-! ## Wall, layer, direction, and primary-figure vocabulary -/

/-- The two wall layers identified by the labels `R₁` and `R₂`. -/
inductive WallLayer where
  | brickR1
  | insulationR2
  deriving DecidableEq, Repr

/-- The material occupying each layer. -/
inductive WallMaterial where
  | brick
  | insulation
  deriving DecidableEq, Repr

/-- The two boundary locations labeled in the figure. -/
inductive WallBoundary where
  | leftColdT2
  | rightHotT1
  deriving DecidableEq, Repr

/-- Direction assigned to the positive heat-loss magnitude. -/
inductive HeatFlowDirection where
  | fromT1ToT2
  | fromT2ToT1
  deriving DecidableEq, Repr

/-- Thermal regime used by the plane-wall model. -/
inductive ConductionRegime where
  | steadyOneDimensional
  | transientOrMultidimensional
  deriving DecidableEq, Repr

/-- Heat-transfer path retained in the stated approximation. -/
inductive DominantHeatTransferPath where
  | throughBrickAndInsulation
  | other
  deriving DecidableEq, Repr

/-- Text labels visible in the supplied primary image. -/
inductive FigureLabel where
  | brickR1
  | insulationR2
  | temperatureT1
  | temperatureT2
  | heatFlow
  deriving DecidableEq, Repr

/-!
Qualitative information transcribed from the primary image. The arrow tail is
on the right at `T₁` and its head is on the left at `T₂`. The raster contains
no numerical or answer readout.
-/
structure CompositeWallFigure where
  showsLabel : FigureLabel → Bool
  leftLayer : WallLayer
  rightLayer : WallLayer
  leftBoundary : WallBoundary
  rightBoundary : WallBoundary
  heatArrowTail : WallBoundary
  heatArrowHead : WallBoundary
  containsNumericalReadout : Bool
  containsAnswerReadout : Bool

/-! ## Independent setup and assumption interfaces -/

/-!
Independent physical data for the wall. Neither `totalHeatLossRate` nor
`totalArealThermalResistance` is defined from an answer choice; the governing
laws below constrain these observables.
-/
structure CompositeWallSetup where
  layerMaterial : WallLayer → WallMaterial
  layerThickness : WallLayer → LengthQuantity
  layerArealThermalResistance :
    WallLayer → ArealThermalResistanceQuantity
  totalArealThermalResistance : ArealThermalResistanceQuantity
  totalWallArea : AreaQuantity
  boundaryTemperature : WallBoundary → MeasuredTemperature
  totalHeatLossRate : HeatCurrentQuantity
  positiveHeatFlowDirection : HeatFlowDirection
  conductionRegime : ConductionRegime
  dominantHeatTransferPath : DominantHeatTransferPath
  figure : CompositeWallFigure

/-- Categorical facts stated by the prose and the adopted sign convention. -/
structure MatchesCompositeWallScenario (setup : CompositeWallSetup) : Prop where
  brickLayerMaterial : setup.layerMaterial .brickR1 = .brick
  insulationLayerMaterial : setup.layerMaterial .insulationR2 = .insulation
  positiveDirectionIsHotToCold :
    setup.positiveHeatFlowDirection = .fromT1ToT2
  steadyConduction : setup.conductionRegime = .steadyOneDimensional
  modeledPath :
    setup.dominantHeatTransferPath = .throughBrickAndInsulation

/-- Evidence read directly from the supplied primary raster. -/
structure MatchesSuppliedFigure (setup : CompositeWallSetup) : Prop where
  everyPrintedLabelShown : ∀ label, setup.figure.showsLabel label = true
  brickDrawnOnLeft : setup.figure.leftLayer = .brickR1
  insulationDrawnOnRight : setup.figure.rightLayer = .insulationR2
  t2LabelsLeftBoundary : setup.figure.leftBoundary = .leftColdT2
  t1LabelsRightBoundary : setup.figure.rightBoundary = .rightHotT1
  heatArrowStartsAtT1 : setup.figure.heatArrowTail = .rightHotT1
  heatArrowEndsAtT2 : setup.figure.heatArrowHead = .leftColdT2
  noNumericalReadoutInRaster : setup.figure.containsNumericalReadout = false
  noAnswerReadoutInRaster : setup.figure.containsAnswerReadout = false

/-- Numerical data explicitly supplied in the prose. The requested heat-loss
rate and the brick resistance are deliberately absent. -/
structure MatchesProblemReadouts (setup : CompositeWallSetup) : Prop where
  brickThicknessInches :
    lengthInInches (setup.layerThickness .brickR1) = 4
  insulationR19 :
    arealThermalResistanceInImperialRValue
      (setup.layerArealThermalResistance .insulationR2) = 19
  totalAreaSquareFeet : areaInSquareFeet setup.totalWallArea = 195
  temperatureDifferenceFahrenheit :
    (setup.boundaryTemperature .rightHotT1).fahrenheitReadout -
      (setup.boundaryTemperature .leftColdT2).fahrenheitReadout = 35

/-!
The extracted prompt omits the material table needed to convert four inches
of brick into an R-value. The recorded answer uses the textbook calibration
`R = 0.20` per inch for common brick, giving `R₁ = 0.80`. This material datum
is exposed separately rather than hidden in a target or definition.
-/
structure UsesTextbookFourInchBrickResistance
    (setup : CompositeWallSetup) : Prop where
  brickRValue :
    arealThermalResistanceInImperialRValue
      (setup.layerArealThermalResistance .brickR1) = (4 / 5 : ℝ)

/-- Positivity and hot-to-cold ordering for the physical model. No field fixes
the heat current to the requested numerical value. -/
structure HasPhysicalCompositeWallParameters
    (setup : CompositeWallSetup) : Prop where
  everyLayerThicknessPositive :
    ∀ layer, 0 < lengthInInches (setup.layerThickness layer)
  wallAreaPositive : 0 < areaInSquareFeet setup.totalWallArea
  everyLayerResistancePositive :
    ∀ layer,
      0 < arealThermalResistanceInImperialRValue
        (setup.layerArealThermalResistance layer)
  totalResistancePositive :
    0 < arealThermalResistanceInImperialRValue
      setup.totalArealThermalResistance
  heatLossPositive : 0 < heatCurrentInBtuPerHour setup.totalHeatLossRate
  t1HotterThanT2 :
    (setup.boundaryTemperature .leftColdT2).fahrenheitReadout <
      (setup.boundaryTemperature .rightHotT1).fahrenheitReadout

/-! Areal thermal resistances of plane layers in series add. -/
structure SatisfiesSeriesArealResistanceLaw
    (setup : CompositeWallSetup) : Prop where
  totalResistanceIsSeriesSum :
    ∀ units,
      ((setup.totalArealThermalResistance units).val : ℝ) =
        ((setup.layerArealThermalResistance .brickR1 units).val : ℝ) +
          ((setup.layerArealThermalResistance .insulationR2 units).val : ℝ)

/-!
Steady one-dimensional heat loss through a plane wall expressed using areal
resistance: `heat-loss rate = area * (T₁ - T₂) / total R-value`.
This governing law contains no numerical heat-current conclusion.
-/
structure SatisfiesSteadySeriesWallHeatLaw
    (setup : CompositeWallSetup) : Prop where
  heatLossThroughSeriesWall :
    heatCurrentInBtuPerHour setup.totalHeatLossRate =
      areaInSquareFeet setup.totalWallArea *
        ((setup.boundaryTemperature .rightHotT1).fahrenheitReadout -
          (setup.boundaryTemperature .leftColdT2).fahrenheitReadout) /
        arealThermalResistanceInImperialRValue
          setup.totalArealThermalResistance

/-! ## Derived resistance, heat-loss rate, and multiple-choice conclusion -/

/-- The two layer resistances give a total wall R-value of `19.8`. -/
theorem totalArealThermalResistance_exact
    (setup : CompositeWallSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hBrick : UsesTextbookFourInchBrickResistance setup)
    (hSeries : SatisfiesSeriesArealResistanceLaw setup) :
    arealThermalResistanceInImperialRValue
      setup.totalArealThermalResistance = (99 / 5 : ℝ) := by
  have hSeriesSI := hSeries.totalResistanceIsSeriesSum UnitChoices.SI
  have hBrickValue := hBrick.brickRValue
  have hInsulationValue := hReadouts.insulationR19
  unfold arealThermalResistanceInImperialRValue at hBrickValue hInsulationValue
  unfold arealThermalResistanceInImperialRValue
  unfold arealThermalResistanceInSquareMeterKelvinPerWatt at hBrickValue hInsulationValue
  unfold arealThermalResistanceInSquareMeterKelvinPerWatt
  norm_num [oneImperialRValueInSquareMeterKelvinPerWatt] at hBrickValue hInsulationValue
  norm_num [oneImperialRValueInSquareMeterKelvinPerWatt]
  linarith

/-! The unrounded prediction is `11375/33 Btu/h`, approximately `344.7`. -/
theorem totalHeatLossRate_exact
    (setup : CompositeWallSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hBrick : UsesTextbookFourInchBrickResistance setup)
    (hPhysical : HasPhysicalCompositeWallParameters setup)
    (hSeries : SatisfiesSeriesArealResistanceLaw setup)
    (hHeat : SatisfiesSteadySeriesWallHeatLaw setup) :
    heatCurrentInBtuPerHour setup.totalHeatLossRate =
      (11375 / 33 : ℝ) := by
  rw [hHeat.heatLossThroughSeriesWall, hReadouts.totalAreaSquareFeet,
    hReadouts.temperatureDifferenceFahrenheit,
    totalArealThermalResistance_exact setup hReadouts hBrick hSeries]
  norm_num

/-- Labels of the four supplied answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Btu-per-hour value printed beside each answer choice. -/
def displayedHeatLossInBtuPerHour : AnswerChoice → ℝ
  | .A => 200
  | .B => 250
  | .C => 300
  | .D => 350

/-- Dataset metadata recording the supplied answer label. This definition is
not used to establish the physical theorem. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with rounding a Btu-per-hour rate to the nearest `50 Btu/h`. -/
def RoundsToNearestFiftyBtuPerHour
    (heatCurrent : HeatCurrentQuantity) (displayedRate : ℝ) : Prop :=
  |heatCurrentInBtuPerHour heatCurrent - displayedRate| < 25

/-- The physical heat-loss rate rounds to the rate printed for a choice. -/
def MatchesAnswerChoice
    (setup : CompositeWallSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestFiftyBtuPerHour setup.totalHeatLossRate
    (displayedHeatLossInBtuPerHour choice)

/-!
The exact prediction lies within `25 Btu/h` of `350` and no other displayed
rate, uniquely selecting choice D.

This is the formal target corresponding to
`thm:physics:phyx_mini_0487:target`.
-/
theorem problem_phyx_mini_0487
    (setup : CompositeWallSetup)
    (hScenario : MatchesCompositeWallScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hBrick : UsesTextbookFourInchBrickResistance setup)
    (hPhysical : HasPhysicalCompositeWallParameters setup)
    (hSeries : SatisfiesSeriesArealResistanceLaw setup)
    (hHeat : SatisfiesSteadySeriesWallHeatLaw setup) :
    heatCurrentInBtuPerHour setup.totalHeatLossRate =
        (11375 / 33 : ℝ) ∧
      MatchesAnswerChoice setup .D ∧
      ∀ choice, MatchesAnswerChoice setup choice → choice = .D := by
  have hExact :=
    totalHeatLossRate_exact setup hReadouts hBrick hPhysical hSeries hHeat
  refine ⟨hExact, ?_, ?_⟩
  · simp only [MatchesAnswerChoice, RoundsToNearestFiftyBtuPerHour,
      displayedHeatLossInBtuPerHour, hExact]
    norm_num [abs_of_nonpos, abs_of_nonneg]
  · intro choice hChoice
    cases choice with
    | A =>
        norm_num [MatchesAnswerChoice, RoundsToNearestFiftyBtuPerHour,
          displayedHeatLossInBtuPerHour, hExact, abs_of_nonpos,
          abs_of_nonneg] at hChoice
    | B =>
        norm_num [MatchesAnswerChoice, RoundsToNearestFiftyBtuPerHour,
          displayedHeatLossInBtuPerHour, hExact, abs_of_nonpos,
          abs_of_nonneg] at hChoice
    | C =>
        norm_num [MatchesAnswerChoice, RoundsToNearestFiftyBtuPerHour,
          displayedHeatLossInBtuPerHour, hExact, abs_of_nonpos,
          abs_of_nonneg] at hChoice
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0487
