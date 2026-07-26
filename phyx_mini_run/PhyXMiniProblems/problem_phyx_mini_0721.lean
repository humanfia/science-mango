import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0721

open Dimension

/-!
# Pressure at the sealed top of a water-filled U-tube

The left arm of the U-tube is open and its water surface is `100 cm` above
the common bottom datum. Water reaches a closed end in the right arm at
`40 cm` above the same datum. Thus the closed-end water is below the open
surface, and hydrostatic equilibrium makes its absolute pressure exceed
atmospheric pressure by the head of a `60 cm` water column.

Pressure, length, mass density, and acceleration are represented by
unit-independent Physlib quantities. Real numbers below are only readouts in
named units. In particular, the pressure at the closed end is an independent
field of the setup; it is not defined from the recorded answer.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration magnitude, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure as a multiple of one standard atmosphere. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Read mass density in kilograms per cubic metre. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Physical setup and primary-figure data -/

/-- The three water locations needed to interpret the supplied figure. -/
inductive TubeLocation where
  | commonBottom
  | leftOpenFreeSurface
  | rightClosedTop
  deriving DecidableEq, Fintype, Repr

/-- The two vertical dimensions printed beside the tube. -/
inductive FigureHeightLabel where
  | leftOneHundredCentimeters
  | rightFortyCentimeters
  deriving DecidableEq, Fintype, Repr

/-- Boundary types distinguished by the open and closed arm tops. -/
inductive TubeBoundaryCondition where
  | interiorBend
  | openToAtmosphere
  | closedEnd
  deriving DecidableEq, Repr

/-- The qualitative shape visible in the raster. -/
inductive TubeShape where
  | uShaped
  | other
  deriving DecidableEq, Repr

/-- The fluid named in the problem statement. -/
inductive TubeFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-- The mechanical regime used for the pressure calculation. -/
inductive FluidRegime where
  | staticEquilibrium
  | moving
  deriving DecidableEq, Repr

/-- Whether the water in the two arms belongs to one connected column. -/
inductive ColumnConnectivity where
  | connected
  | disconnected
  deriving DecidableEq, Repr

/-!
Figure-only information: height marks and endpoints, open/closed boundary
labels, the water fill, the U-shape, and the dashed reference level. This
structure contains no pressure formula and no answer value.
-/
structure UTubeFigure where
  shape : TubeShape
  heightMark : FigureHeightLabel → LengthQuantity
  heightArrowLowerEndpoint : FigureHeightLabel → TubeLocation
  heightArrowUpperEndpoint : FigureHeightLabel → TubeLocation
  boundaryAt : TubeLocation → TubeBoundaryCondition
  waterShownAt : TubeLocation → Bool
  dashedReferencePassesThroughRightClosedTop : Bool
  leftSurfaceDrawnAboveRightClosedTop : Bool

/-!
The independent physical data for the problem. Most importantly,
`pressureAt .rightClosedTop` is the unknown requested by the question.
-/
structure ClosedUTubeSetup where
  figure : UTubeFigure
  fluid : TubeFluid
  regime : FluidRegime
  connectivity : ColumnConnectivity
  elevationAt : TubeLocation → LengthQuantity
  pressureAt : TubeLocation → DimPressure
  ambientPressure : DimPressure
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity

/-!
Evidence read from the primary raster: both arrows start at the common bottom,
the left free surface is at `100 cm`, the sealed right top is at `40 cm`, the
left arm is open, and water reaches the closed right end. None of these fields
constrains the requested pressure.
-/
structure MatchesPrimaryFigure (setup : ClosedUTubeSetup) : Prop where
  tubeIsUShaped : setup.figure.shape = .uShaped
  leftArrowStartsAtBottom :
    setup.figure.heightArrowLowerEndpoint .leftOneHundredCentimeters =
      .commonBottom
  leftArrowEndsAtFreeSurface :
    setup.figure.heightArrowUpperEndpoint .leftOneHundredCentimeters =
      .leftOpenFreeSurface
  rightArrowStartsAtBottom :
    setup.figure.heightArrowLowerEndpoint .rightFortyCentimeters =
      .commonBottom
  rightArrowEndsAtClosedTop :
    setup.figure.heightArrowUpperEndpoint .rightFortyCentimeters =
      .rightClosedTop
  leftHeightMarkCentimeters :
    lengthInCentimeters
        (setup.figure.heightMark .leftOneHundredCentimeters) = 100
  rightHeightMarkCentimeters :
    lengthInCentimeters
        (setup.figure.heightMark .rightFortyCentimeters) = 40
  commonBottomElevationMeters :
    lengthInMeters (setup.elevationAt .commonBottom) = 0
  leftMarkMatchesElevationDifference :
    lengthInMeters
        (setup.figure.heightMark .leftOneHundredCentimeters) =
      lengthInMeters (setup.elevationAt .leftOpenFreeSurface) -
        lengthInMeters (setup.elevationAt .commonBottom)
  rightMarkMatchesElevationDifference :
    lengthInMeters
        (setup.figure.heightMark .rightFortyCentimeters) =
      lengthInMeters (setup.elevationAt .rightClosedTop) -
        lengthInMeters (setup.elevationAt .commonBottom)
  bottomIsInteriorBend :
    setup.figure.boundaryAt .commonBottom = .interiorBend
  leftTopIsOpen :
    setup.figure.boundaryAt .leftOpenFreeSurface = .openToAtmosphere
  rightTopIsClosed :
    setup.figure.boundaryAt .rightClosedTop = .closedEnd
  waterShownThroughout :
    ∀ location : TubeLocation, setup.figure.waterShownAt location = true
  dashedReferenceAtClosedTop :
    setup.figure.dashedReferencePassesThroughRightClosedTop = true
  leftSurfaceIsDrawnHigher :
    setup.figure.leftSurfaceDrawnAboveRightClosedTop = true

/-- Written-scenario and modeling information that is not a numerical answer. -/
structure MatchesWaterFilledStaticScenario
    (setup : ClosedUTubeSetup) : Prop where
  fluidIsWater : setup.fluid = .water
  waterIsStatic : setup.regime = .staticEquilibrium
  oneConnectedWaterColumn : setup.connectivity = .connected

/-!
Standard textbook calibrations used to interpret the answer choices:
`ρ_water = 1000 kg/m³`, `g = 9.8 m/s²`, and ambient absolute pressure is one
standard atmosphere. These are physical data, not the closed-end answer.
-/
structure UsesStandardWaterGravityAndAtmosphere
    (setup : ClosedUTubeSetup) : Prop where
  waterDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.waterMassDensity = 1000
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5
  ambientPressureIsOneAtmosphere :
    setup.ambientPressure = DimPressure.standardAtmosphere

/-- Positivity conditions selecting the physical branch of the model. -/
structure HasPhysicalParameters (setup : ClosedUTubeSetup) : Prop where
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterMassDensity
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  ambientPressurePositive :
    0 < pressureInPascals setup.ambientPressure
  pressurePositive :
    ∀ location : TubeLocation,
      0 < pressureInPascals (setup.pressureAt location)

/-!
The open water surface is exposed to ambient absolute pressure. This is a
boundary condition at the left surface, not a statement about the unknown
pressure at the closed right top.
-/
structure SatisfiesOpenSurfaceBoundaryCondition
    (setup : ClosedUTubeSetup) : Prop where
  openSurfacePressureIsAmbient :
    setup.pressureAt .leftOpenFreeSurface = setup.ambientPressure

/-!
General hydrostatic equilibrium for any two named points in the connected
water column. Pressure plus `ρ g` times elevation is constant. The law is
uniform over all point pairs and does not single out a numerical answer.
-/
structure SatisfiesHydrostaticEquilibrium
    (setup : ClosedUTubeSetup) : Prop where
  pressureDifferenceLaw :
    ∀ upper lower : TubeLocation,
      pressureInPascals (setup.pressureAt lower) =
        pressureInPascals (setup.pressureAt upper) +
          densityInKilogramsPerCubicMeter setup.waterMassDensity *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            (lengthInMeters (setup.elevationAt upper) -
              lengthInMeters (setup.elevationAt lower))

/-! ## Requested pressure and answer choices -/

/-- Labels of the four pressure answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The absolute pressure, in atmospheres, displayed beside each answer. -/
def displayedPressureInAtmospheres : AnswerChoice → ℝ
  | .A => 51 / 50
  | .B => 28 / 25
  | .C => 53 / 50
  | .D => 57 / 50

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A displayed answer is uniquely closest to the independently modeled
closed-end pressure. This accommodates the two-decimal rounding in the
printed choices without identifying the unknown pressure by definition.
-/
def IsUniqueClosestDisplayedPressure
    (setup : ClosedUTubeSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |pressureInAtmospheres (setup.pressureAt .rightClosedTop) -
        displayedPressureInAtmospheres choice| <
      |pressureInAtmospheres (setup.pressureAt .rightClosedTop) -
        displayedPressureInAtmospheres other|

/-!
The two height marks put the open surface `3/5 m` above the closed right top.
This is a geometry consequence only; it contains no pressure conclusion.
-/
lemma openSurface_minus_closedTop_elevation_eq_three_fifths
    (setup : ClosedUTubeSetup)
    (hFigure : MatchesPrimaryFigure setup) :
    lengthInMeters (setup.elevationAt .leftOpenFreeSurface) -
        lengthInMeters (setup.elevationAt .rightClosedTop) = 3 / 5 := by
  have hLeftHeight := hFigure.leftHeightMarkCentimeters
  have hRightHeight := hFigure.rightHeightMarkCentimeters
  simp only [lengthInCentimeters] at hLeftHeight hRightHeight
  nlinarith [hFigure.commonBottomElevationMeters,
    hFigure.leftMarkMatchesElevationDifference,
    hFigure.rightMarkMatchesElevationDifference]

/-!
The open-surface boundary condition and the general hydrostatic law give the
closed-top pressure as ambient pressure plus the `60 cm` water head. The
requested pressure remains on the conclusion side of this lemma.
-/
lemma closedTopPressure_eq_ambient_add_waterHead
    (setup : ClosedUTubeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hScenario : MatchesWaterFilledStaticScenario setup)
    (hBoundary : SatisfiesOpenSurfaceBoundaryCondition setup)
    (hHydrostatic : SatisfiesHydrostaticEquilibrium setup) :
    pressureInPascals (setup.pressureAt .rightClosedTop) =
      pressureInPascals setup.ambientPressure +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (lengthInMeters (setup.elevationAt .leftOpenFreeSurface) -
            lengthInMeters (setup.elevationAt .rightClosedTop)) := by
  simpa [hBoundary.openSurfacePressureIsAmbient] using
    hHydrostatic.pressureDifferenceLaw
      TubeLocation.leftOpenFreeSurface TubeLocation.rightClosedTop

/-!
With the figure dimensions and standard textbook data, the exact ideal-model
pressure is `1021/965 atm ≈ 1.058 atm`, which rounds to `1.06 atm`. Therefore
choice C is uniquely closest among the four displayed pressures.

This formalizes blueprint label `thm:physics:phyx_mini_0721:target`.
-/
theorem problem_phyx_mini_0721
    (setup : ClosedUTubeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hScenario : MatchesWaterFilledStaticScenario setup)
    (hCalibration : UsesStandardWaterGravityAndAtmosphere setup)
    (hPhysical : HasPhysicalParameters setup)
    (hBoundary : SatisfiesOpenSurfaceBoundaryCondition setup)
    (hHydrostatic : SatisfiesHydrostaticEquilibrium setup) :
    (pressureInPascals (setup.pressureAt .rightClosedTop) =
      pressureInPascals setup.ambientPressure +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (lengthInMeters (setup.elevationAt .leftOpenFreeSurface) -
            lengthInMeters (setup.elevationAt .rightClosedTop))) ∧
      pressureInAtmospheres (setup.pressureAt .rightClosedTop) =
        1021 / 965 ∧
      IsUniqueClosestDisplayedPressure setup .C := by
  have hPressure :=
    closedTopPressure_eq_ambient_add_waterHead setup hFigure hScenario
      hBoundary hHydrostatic
  have hElevation :=
    openSurface_minus_closedTop_elevation_eq_three_fifths setup hFigure
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have hAmbientPressure :
      pressureInPascals setup.ambientPressure = 101325 := by
    rw [hCalibration.ambientPressureIsOneAtmosphere]
    exact hStandardAtmosphere
  have hClosedPressure :
      pressureInPascals (setup.pressureAt .rightClosedTop) = 107205 := by
    rw [hCalibration.waterDensityKilogramsPerCubicMeter,
      hCalibration.gravityMetersPerSecondSquared, hElevation,
      hAmbientPressure] at hPressure
    norm_num at hPressure ⊢
    exact hPressure
  have hPressureInAtmospheres :
      pressureInAtmospheres (setup.pressureAt .rightClosedTop) =
        1021 / 965 := by
    rw [pressureInAtmospheres, hClosedPressure, hStandardAtmosphere]
    norm_num
  refine ⟨closedTopPressure_eq_ambient_add_waterHead setup hFigure hScenario
    hBoundary hHydrostatic, hPressureInAtmospheres, ?_⟩
  unfold IsUniqueClosestDisplayedPressure
  intro other hOther
  rw [hPressureInAtmospheres]
  fin_cases other
  · norm_num [displayedPressureInAtmospheres]
  · norm_num [displayedPressureInAtmospheres]
  · exact (hOther rfl).elim
  · norm_num [displayedPressureInAtmospheres]

end PhyXMiniProblems.ProblemPhyXMini0721
