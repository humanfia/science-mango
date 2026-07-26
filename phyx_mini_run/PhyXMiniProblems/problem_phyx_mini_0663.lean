import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0663

open Dimension

/-!
# Highest pressure in the water of a layered cylinder

A vertical steel cylinder contains, from bottom to top, `0.5 m` of water,
`1 m` of gasoline, and air filling the rest of its `2.5 m` height.  The
cylinder has cross-sectional area `1.5 m²`, and the gasoline surface is exposed
through the air layer to an atmosphere at `101 kPa`.  The highest water
pressure is the absolute pressure at the cylinder bottom.

Lengths, area, pressure, mass density, and acceleration remain dimensionful
physical quantities.  Real numbers occur only as readouts in named coherent
units, dimensionless ordering data, and displayed answer values.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length independent of the readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read pressure in the coherent unit induced by selected base units. -/
def pressureReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (pressure : DimPressure) : ℝ :=
  (pressure {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Read density in a selected mass unit per selected length unit cubed. -/
def densityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : MassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read acceleration in selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  pressureReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds pressure

/-- Kilopascal readout used by the answer choices. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Kilogram-per-cubic-metre readout of a mass density. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  densityReadout MassUnit.kilograms LengthUnit.meters density

/-- Metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Physical setup and figure vocabulary -/

/-- The three material layers in physical bottom-to-top order. -/
inductive CylinderLayer where
  | water
  | gasoline
  | air
  deriving DecidableEq, Fintype, Repr

/-- Distinguished vertical locations needed by the pressure model. -/
inductive VerticalLocation where
  | cylinderBottom
  | waterGasolineInterface
  | gasolineSurface
  | cylinderTop
  deriving DecidableEq, Fintype, Repr

/-- Material named for the container wall. -/
inductive ContainerMaterial where
  | steel
  | other
  deriving DecidableEq, Repr

/-- Orientation of the cylinder axis. -/
inductive CylinderOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Literal material and pressure labels visible in the supplied bitmap. -/
inductive FigureLabel where
  | pZero
  | air
  | gasoline
  | h2o
  deriving DecidableEq, Fintype, Repr

/-- Height annotations represented by the prose and figure. -/
inductive FigureHeightMark where
  | totalCylinderHeight
  | gasolineLayerHeight
  | waterLayerHeight
  deriving DecidableEq, Fintype, Repr

/-!
Independent evidence read from the primary figure.  Indices `0`, `1`, and `2`
mean bottom, middle, and top.  No pressure answer is stored here.
-/
structure LayeredCylinderFigure where
  layerFromBottom : Fin 3 → CylinderLayer
  showsLabel : FigureLabel → Bool
  markedHeight : FigureHeightMark → LengthQuantity
  pressureSymbolLocation : VerticalLocation
  cylinderSidesStraight : Bool
  heightArrowsVertical : Bool

/-!
The physical observables and model parameters.  Pressures at distinguished
points and throughout the water are stored independently; neither is defined
from an answer choice or desired numerical result.
-/
structure LayeredCylinderSetup where
  containerMaterial : ContainerMaterial
  orientation : CylinderOrientation
  totalHeight : LengthQuantity
  crossSectionalArea : AreaQuantity
  layerHeight : CylinderLayer → LengthQuantity
  atmosphericPressure : DimPressure
  waterMassDensity : MassDensityQuantity
  gasolineMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  absolutePressureAt : VerticalLocation → DimPressure
  waterPressureAtDepthBelowInterface : LengthQuantity → DimPressure
  gasolineSurfaceOpenToAir : Bool
  figure : LayeredCylinderFigure

/-! ## Assumptions: scenario, readouts, figure evidence, and laws -/

/-- Qualitative facts stated in the problem prose. -/
structure MatchesLayeredCylinderScenario
    (setup : LayeredCylinderSetup) : Prop where
  containerIsSteel : setup.containerMaterial = .steel
  cylinderIsVertical : setup.orientation = .vertical
  gasolineSurfaceIsOpen : setup.gasolineSurfaceOpenToAir = true

/-- Numerical values stated in the prose, excluding the requested pressure. -/
structure MatchesProblemReadouts (setup : LayeredCylinderSetup) : Prop where
  totalHeightMeters : lengthInMeters setup.totalHeight = 5 / 2
  crossSectionalAreaSquareMeters :
    areaInSquareMeters setup.crossSectionalArea = 3 / 2
  waterHeightMeters : lengthInMeters (setup.layerHeight .water) = 1 / 2
  gasolineHeightMeters : lengthInMeters (setup.layerHeight .gasoline) = 1
  atmosphericPressurePascals :
    pressureInPascals setup.atmosphericPressure = 101000

/-!
Primary-raster evidence: water, gasoline, and air appear bottom to top; the
height annotations denote the setup quantities; and `P₀` is at the open top.
The fill equation also records the unmarked air layer inside the `2.5 m`
cylinder.
-/
structure MatchesSuppliedFigure (setup : LayeredCylinderSetup) : Prop where
  bottomLayerIsWater : setup.figure.layerFromBottom 0 = .water
  middleLayerIsGasoline : setup.figure.layerFromBottom 1 = .gasoline
  topLayerIsAir : setup.figure.layerFromBottom 2 = .air
  everyLiteralLabelShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  totalHeightMarkMatchesSetup :
    setup.figure.markedHeight .totalCylinderHeight = setup.totalHeight
  gasolineHeightMarkMatchesSetup :
    setup.figure.markedHeight .gasolineLayerHeight =
      setup.layerHeight .gasoline
  waterHeightMarkMatchesSetup :
    setup.figure.markedHeight .waterLayerHeight = setup.layerHeight .water
  pressurePZeroIsAtTop :
    setup.figure.pressureSymbolLocation = .cylinderTop
  straightCylinderSides : setup.figure.cylinderSidesStraight = true
  verticalHeightArrows : setup.figure.heightArrowsVertical = true
  layersFillCylinder :
    lengthInMeters (setup.layerHeight .water) +
        lengthInMeters (setup.layerHeight .gasoline) +
        lengthInMeters (setup.layerHeight .air) =
      lengthInMeters setup.totalHeight

/-- Positivity needed for the hydrostatic maximum argument. -/
structure HasPhysicalLayerParameters (setup : LayeredCylinderSetup) : Prop where
  totalHeightPositive : 0 < lengthInMeters setup.totalHeight
  crossSectionalAreaPositive : 0 < areaInSquareMeters setup.crossSectionalArea
  eachLayerHeightPositive :
    ∀ layer : CylinderLayer, 0 < lengthInMeters (setup.layerHeight layer)
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterMassDensity
  gasolineDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.gasolineMassDensity
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericPressure

/-!
The layered hydrostatic model in arbitrary coherent base units:

* the open top is at atmospheric pressure;
* air-weight variation is neglected between the top and gasoline surface;
* pressure rises by `ρ g h` through the gasoline;
* pressure at water depth `d` rises by `ρ_water g d` from the interface;
* full water depth is the cylinder bottom.

No numeric bottom pressure or selected answer occurs in these laws.
-/
structure SatisfiesLayeredHydrostaticLaws
    (setup : LayeredCylinderSetup) : Prop where
  openTopPressureIsAtmospheric :
    setup.absolutePressureAt .cylinderTop = setup.atmosphericPressure
  airPressureVariationNeglected :
    setup.absolutePressureAt .gasolineSurface =
      setup.absolutePressureAt .cylinderTop
  gasolineHydrostaticPressure :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      pressureReadout massUnit lengthUnit timeUnit
          (setup.absolutePressureAt .waterGasolineInterface) =
        pressureReadout massUnit lengthUnit timeUnit
            (setup.absolutePressureAt .gasolineSurface) +
          densityReadout massUnit lengthUnit setup.gasolineMassDensity *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit (setup.layerHeight .gasoline)
  waterHydrostaticPressure :
    ∀ (depth : LengthQuantity) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      0 ≤ lengthReadout lengthUnit depth →
      lengthReadout lengthUnit depth ≤
          lengthReadout lengthUnit (setup.layerHeight .water) →
      pressureReadout massUnit lengthUnit timeUnit
          (setup.waterPressureAtDepthBelowInterface depth) =
        pressureReadout massUnit lengthUnit timeUnit
            (setup.absolutePressureAt .waterGasolineInterface) +
          densityReadout massUnit lengthUnit setup.waterMassDensity *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit depth
  bottomIsAtFullWaterDepth :
    setup.absolutePressureAt .cylinderBottom =
      setup.waterPressureAtDepthBelowInterface (setup.layerHeight .water)

/-!
A candidate is a highest absolute water pressure if it occurs at a physical
depth between interface and bottom and dominates every other such depth.  The
predicate does not select a depth or assign a numerical value by definition.
-/
def IsHighestPressureInWater
    (setup : LayeredCylinderSetup) (candidate : DimPressure) : Prop :=
  (∃ depth : LengthQuantity,
      0 ≤ lengthInMeters depth ∧
      lengthInMeters depth ≤ lengthInMeters (setup.layerHeight .water) ∧
      candidate = setup.waterPressureAtDepthBelowInterface depth) ∧
    ∀ depth : LengthQuantity,
      0 ≤ lengthInMeters depth →
      lengthInMeters depth ≤ lengthInMeters (setup.layerHeight .water) →
      pressureInPascals (setup.waterPressureAtDepthBelowInterface depth) ≤
        pressureInPascals candidate

/-! ## Displayed answers and formal targets -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Absolute pressure in kilopascals printed beside each answer label. -/
def displayedPressureInKilopascals : AnswerChoice → ℝ
  | .A => 217 / 2
  | .B => 116
  | .C => 101
  | .D => 566 / 5

/-- Dataset answer metadata, deliberately not used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement with a pressure displayed to the nearest tenth of a kilopascal.
The half-unit-in-the-last-place bound records only the display precision; it
does not claim that any choice follows from the available physical data.
-/
def MatchesDisplayedPressureToNearestTenth
    (pressure : DimPressure) (choice : AnswerChoice) : Prop :=
  |pressureInKilopascals pressure -
      displayedPressureInKilopascals choice| ≤ 1 / 20

/-- The hydrostatic laws make the bottom pressure maximal throughout water. -/
lemma bottomPressureIsHighestInWater
    (setup : LayeredCylinderSetup)
    (hPhysical : HasPhysicalLayerParameters setup)
    (hLaws : SatisfiesLayeredHydrostaticLaws setup) :
    IsHighestPressureInWater setup
      (setup.absolutePressureAt .cylinderBottom) := by
  sorry

/-!
The stated readouts and layered hydrostatic laws determine the bottom pressure
symbolically.  The source does not supply numerical values for either liquid's
density or for gravitational acceleration, so they remain physical parameters.
-/
lemma bottomPressureInKilopascals_eq
    (setup : LayeredCylinderSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hLaws : SatisfiesLayeredHydrostaticLaws setup) :
    pressureInKilopascals
        (setup.absolutePressureAt .cylinderBottom) =
      (101000 +
          densityInKilogramsPerCubicMeter setup.gasolineMassDensity *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration +
          densityInKilogramsPerCubicMeter setup.waterMassDensity *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration * (1 / 2)) / 1000 := by
  sorry

/-!
The bottom is the highest-pressure point in the water, and its absolute
pressure obeys the source-supported symbolic layered-fluid formula.  The
source omits liquid densities and gravitational acceleration, so no numerical
choice is asserted.  The declaration name is retained for its existing
blueprint pin; choice D appears only in `recordedDatasetAnswer` metadata.

Blueprint label: `thm:physics:phyx_mini_0663:target`.
-/
theorem highestPressureInWater_matches_choiceD
    (setup : LayeredCylinderSetup)
    (hScenario : MatchesLayeredCylinderScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPhysical : HasPhysicalLayerParameters setup)
    (hLaws : SatisfiesLayeredHydrostaticLaws setup) :
    IsHighestPressureInWater setup
        (setup.absolutePressureAt .cylinderBottom) ∧
      pressureInKilopascals
          (setup.absolutePressureAt .cylinderBottom) =
        (101000 +
            densityInKilogramsPerCubicMeter setup.gasolineMassDensity *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration +
            densityInKilogramsPerCubicMeter setup.waterMassDensity *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration * (1 / 2)) / 1000 := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0663
