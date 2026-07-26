import Mathlib
import Physlib.Units.WithDim.Pressure
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Inlet-pressure deficit in a hydroelectric penstock

Water flows from a reservoir through a `1.00 m`-diameter intake at point 2,
which is `50 m` below the free surface at point 1.  It then descends `200 m`
to a `0.50 m`-diameter nozzle at point 3, immediately before the turbine.

The supplied figure fixes the elevations `y₁ = 250 m`, `y₂ = 200 m`, and
`y₃ = 0 m`.  The ideal-flow model uses continuity and Bernoulli's equation,
with the free surface and nozzle at atmospheric pressure and negligible free-
surface speed.  The requested quantity is the amount by which the flowing
inlet pressure lies below the hydrostatic pressure at the same depth.

Pressure and speed use Physlib's unit-independent dimensional quantities.
The other physical magnitudes use the same `Dimensionful`/`WithDim`
infrastructure.  Real numbers occur only in explicitly named coherent-SI
readouts and dimensionless answer-choice comparisons.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0725

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical length, independent of a choice of units. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative mass density carrying dimension `M L⁻³`. -/
abbrev DensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude carrying dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical mass density in kilograms per cubic metre. -/
def densityInKilogramsPerCubicMeter (density : DensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read a physical acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in coherent-SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Apparatus and primary-figure vocabulary -/

/-- The three numbered points marked on the supplied dam-to-turbine figure. -/
inductive FlowPoint where
  | reservoirSurface
  | intake
  | nozzle
  deriving DecidableEq, Fintype, Repr

/-- Physical objects explicitly visible in the supplied raster. -/
inductive FigureObject where
  | dam
  | reservoirWater
  | intakeTube
  | penstockStreamline
  | nozzle
  | turbine
  deriving DecidableEq, Fintype, Repr

/-- Literal labels or readout annotations explicitly visible in the raster. -/
inductive FigureLabel where
  | pointOne
  | pointTwo
  | pointThree
  | dam
  | streamline
  | turbine
  | yAxisMeters
  | intakeDiameter100cm
  | nozzleDiameter50cm
  deriving DecidableEq, Fintype, Repr

/-- Geometry and qualitative content transcribed from the primary figure. -/
structure DamTurbineFigure where
  showsPoint : FlowPoint → Bool
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  elevation : FlowPoint → LengthQuantity
  intakeTubeDiameter : LengthQuantity
  nozzleDiameter : LengthQuantity
  pointOneIsReservoirSurface : Bool
  pointTwoIsIntake : Bool
  pointThreeIsNozzle : Bool
  streamlineConnectsAllThreePoints : Bool
  nozzleLeadsIntoTurbine : Bool

/-- The liquid named by the problem. -/
inductive WorkingFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-!
The independent quantities and idealizations of the hydroelectric setup.
Neither `hydrostaticPressureAtIntake` nor the flowing inlet pressure is
defined from an answer choice.
-/
structure HydroelectricSetup where
  figure : DamTurbineFigure
  workingFluid : WorkingFluid
  intakeDepthBelowSurface : LengthQuantity
  verticalDropFromIntakeToNozzle : LengthQuantity
  waterDensity : DensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  atmosphericPressure : DimPressure
  pressureAt : FlowPoint → DimPressure
  speedAt : FlowPoint → DimSpeed
  hydrostaticPressureAtIntake : DimPressure
  flowIsSteady : Bool
  waterIsIncompressible : Bool
  viscosityAndMechanicalLossesNegligible : Bool
  reservoirIsOpenToAtmosphere : Bool
  nozzleDischargesAtAtmosphericPressure : Bool
  reservoirAreaIsLargeComparedWithIntake : Bool

/-! ## Scalar expressions for the physical laws and requested difference -/

/-- Bernoulli energy density at one labelled point, read in pascals. -/
def bernoulliEnergyDensityInPascals
    (setup : HydroelectricSetup) (point : FlowPoint) : ℝ :=
  pressureInPascals (setup.pressureAt point) +
    densityInKilogramsPerCubicMeter setup.waterDensity / 2 *
      (speedInMetersPerSecond (setup.speedAt point)) ^ 2 +
    densityInKilogramsPerCubicMeter setup.waterDensity *
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
      lengthInMeters (setup.figure.elevation point)

/--
The pressure predicted at the intake by a static water column measured from
the open reservoir surface.
-/
def hydrostaticReferencePressureInPascals
    (setup : HydroelectricSetup) : ℝ :=
  pressureInPascals (setup.pressureAt .reservoirSurface) +
    densityInKilogramsPerCubicMeter setup.waterDensity *
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
      lengthInMeters setup.intakeDepthBelowSurface

/-- The hydrostatic-minus-flowing inlet pressure difference, in pascals. -/
def inletPressureDeficitInPascals (setup : HydroelectricSetup) : ℝ :=
  pressureInPascals setup.hydrostaticPressureAtIntake -
    pressureInPascals (setup.pressureAt .intake)

/-- The same pressure deficit expressed in standard atmospheres. -/
def inletPressureDeficitInAtmospheres (setup : HydroelectricSetup) : ℝ :=
  inletPressureDeficitInPascals setup /
    pressureInPascals setup.atmosphericPressure

/-! ## Scenario, figure/data readouts, boundary conditions, and laws -/

/-- Qualitative idealizations stated or conventionally used by the model. -/
structure MatchesHydroelectricScenario
    (setup : HydroelectricSetup) : Prop where
  workingFluidIsWater : setup.workingFluid = .water
  steadyFlow : setup.flowIsSteady = true
  incompressibleWater : setup.waterIsIncompressible = true
  negligibleLosses : setup.viscosityAndMechanicalLossesNegligible = true
  openReservoir : setup.reservoirIsOpenToAtmosphere = true
  atmosphericNozzle :
    setup.nozzleDischargesAtAtmosphericPressure = true
  largeReservoir : setup.reservoirAreaIsLargeComparedWithIntake = true

/-!
Primary-image evidence and the compatible dimensions stated in the prose.
The figure places points 1, 2, and 3 at `250 m`, `200 m`, and `0 m`, labels
the intake and nozzle diameters as `100 cm` and `50 cm`, and shows one
streamline leading from the reservoir through the dam to the turbine.
-/
structure MatchesSuppliedDamTurbineFigure
    (setup : HydroelectricSetup) : Prop where
  everyPointShown :
    ∀ point : FlowPoint, setup.figure.showsPoint point = true
  everyObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyLabelShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  pointOneAtSurface : setup.figure.pointOneIsReservoirSurface = true
  pointTwoAtIntake : setup.figure.pointTwoIsIntake = true
  pointThreeAtNozzle : setup.figure.pointThreeIsNozzle = true
  connectedStreamline :
    setup.figure.streamlineConnectsAllThreePoints = true
  nozzleFeedsTurbine : setup.figure.nozzleLeadsIntoTurbine = true
  pointOneElevationMeters :
    lengthInMeters (setup.figure.elevation .reservoirSurface) = 250
  pointTwoElevationMeters :
    lengthInMeters (setup.figure.elevation .intake) = 200
  pointThreeElevationMeters :
    lengthInMeters (setup.figure.elevation .nozzle) = 0
  intakeDiameterMeters :
    lengthInMeters setup.figure.intakeTubeDiameter = 1
  nozzleDiameterMeters :
    lengthInMeters setup.figure.nozzleDiameter = 1 / 2

/-- The two vertical distances explicitly stated in the problem prose. -/
structure MatchesProblemDistanceReadouts
    (setup : HydroelectricSetup) : Prop where
  intakeDepthMeters :
    lengthInMeters setup.intakeDepthBelowSurface = 50
  intakeToNozzleDropMeters :
    lengthInMeters setup.verticalDropFromIntakeToNozzle = 200
  surfaceToIntakeGeometry :
    lengthInMeters (setup.figure.elevation .reservoirSurface) =
      lengthInMeters (setup.figure.elevation .intake) +
        lengthInMeters setup.intakeDepthBelowSurface
  intakeToNozzleGeometry :
    lengthInMeters (setup.figure.elevation .intake) =
      lengthInMeters (setup.figure.elevation .nozzle) +
        lengthInMeters setup.verticalDropFromIntakeToNozzle

/-!
Standard reference values used for the elementary numerical estimate:
liquid-water density `1000 kg/m³`, `g = 9.8 m/s²`, and one standard
atmosphere `101325 Pa`.
-/
structure UsesStandardReferenceData
    (setup : HydroelectricSetup) : Prop where
  waterDensitySI :
    densityInKilogramsPerCubicMeter setup.waterDensity = 1000
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5
  atmosphericPressurePascals :
    pressureInPascals setup.atmosphericPressure = 101325

/-! Boundary conditions at the large free surface and the nozzle outlet. -/
structure SatisfiesReservoirAndNozzleBoundaryConditions
    (setup : HydroelectricSetup) : Prop where
  freeSurfaceAtAtmosphericPressure :
    pressureInPascals (setup.pressureAt .reservoirSurface) =
      pressureInPascals setup.atmosphericPressure
  nozzleAtAtmosphericPressure :
    pressureInPascals (setup.pressureAt .nozzle) =
      pressureInPascals setup.atmosphericPressure
  negligibleFreeSurfaceSpeed :
    speedInMetersPerSecond (setup.speedAt .reservoirSurface) = 0

/-!
Governing laws for steady, incompressible, inviscid flow:

* circular-tube continuity after cancellation of the common factor `π/4`;
* equality of Bernoulli energy density along the shown streamline; and
* the usual hydrostatic pressure law for the no-flow reference pressure.

No numerical pressure deficit or answer choice occurs in these laws.
-/
structure SatisfiesIdealHydroelectricFlowLaws
    (setup : HydroelectricSetup) : Prop where
  steadyIncompressibleContinuity :
    (lengthInMeters setup.figure.intakeTubeDiameter) ^ 2 *
        speedInMetersPerSecond (setup.speedAt .intake) =
      (lengthInMeters setup.figure.nozzleDiameter) ^ 2 *
        speedInMetersPerSecond (setup.speedAt .nozzle)
  bernoulliAlongShownStreamline :
    ∀ pointA pointB : FlowPoint,
      bernoulliEnergyDensityInPascals setup pointA =
        bernoulliEnergyDensityInPascals setup pointB
  hydrostaticReferenceLaw :
    pressureInPascals setup.hydrostaticPressureAtIntake =
      hydrostaticReferencePressureInPascals setup

/-! ## Displayed choices and current target -/

/-- Labels of the four pressure-difference choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The four displayed pressure differences, expressed in atmospheres. -/
def displayedPressureDifferenceInAtmospheres : AnswerChoice → ℝ
  | .A => 11 / 10
  | .B => 13 / 10
  | .C => 3 / 2
  | .D => 17 / 10

/-- The calculated deficit rounds to a displayed tenth of an atmosphere. -/
def RoundsToDisplayedTenthAtmosphere
    (setup : HydroelectricSetup) (displayed : ℝ) : Prop :=
  displayed - 1 / 20 ≤ inletPressureDeficitInAtmospheres setup ∧
    inletPressureDeficitInAtmospheres setup < displayed + 1 / 20

/-- A displayed choice is at least as close as every alternative. -/
def IsNearestDisplayedPressureDifference
    (setup : HydroelectricSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |inletPressureDeficitInAtmospheres setup -
        displayedPressureDifferenceInAtmospheres choice| ≤
      |inletPressureDeficitInAtmospheres setup -
        displayedPressureDifferenceInAtmospheres other|

/-!
Continuity gives `v₃ = 4 v₂`.  Bernoulli between the free surface and
the atmospheric nozzle gives `v₃² = 2 g (250 m)`, hence
`v₂² = 306.25 m²/s²`.  The flowing inlet pressure is below its
hydrostatic reference by the dynamic pressure
`(1/2) ρ v₂² = 153125 Pa ≈ 1.51 atm`, which rounds to `1.5 atm`.

This formalizes `thm:physics:phyx_mini_0725:target` and leaves the exact
deficit, rounding statement, and unique selection of choice C entirely on the
conclusion side.
-/
theorem problem_phyx_mini_0725
    (setup : HydroelectricSetup)
    (hScenario : MatchesHydroelectricScenario setup)
    (hFigure : MatchesSuppliedDamTurbineFigure setup)
    (hDistances : MatchesProblemDistanceReadouts setup)
    (hReference : UsesStandardReferenceData setup)
    (hBoundary : SatisfiesReservoirAndNozzleBoundaryConditions setup)
    (hFlow : SatisfiesIdealHydroelectricFlowLaws setup) :
    inletPressureDeficitInPascals setup = 153125 ∧
      RoundsToDisplayedTenthAtmosphere setup
        (displayedPressureDifferenceInAtmospheres .C) ∧
      IsNearestDisplayedPressureDifference setup .C ∧
      ∀ choice : AnswerChoice,
        IsNearestDisplayedPressureDifference setup choice → choice = .C := by
  have hContinuity := hFlow.steadyIncompressibleContinuity
  have hBernoulli13 :=
    hFlow.bernoulliAlongShownStreamline
      FlowPoint.reservoirSurface FlowPoint.nozzle
  have hBernoulli12 :=
    hFlow.bernoulliAlongShownStreamline
      FlowPoint.reservoirSurface FlowPoint.intake
  have hHydrostatic := hFlow.hydrostaticReferenceLaw
  norm_num [hFigure.intakeDiameterMeters, hFigure.nozzleDiameterMeters]
    at hContinuity
  norm_num [bernoulliEnergyDensityInPascals,
    hBoundary.freeSurfaceAtAtmosphericPressure,
    hBoundary.nozzleAtAtmosphericPressure,
    hBoundary.negligibleFreeSurfaceSpeed,
    hReference.waterDensitySI,
    hReference.gravitationalAccelerationSI,
    hFigure.pointOneElevationMeters,
    hFigure.pointThreeElevationMeters] at hBernoulli13
  have hvNozzleSq :
      speedInMetersPerSecond (setup.speedAt .nozzle) ^ 2 = 4900 := by
    nlinarith [hBernoulli13]
  have hvIntakeSq :
      speedInMetersPerSecond (setup.speedAt .intake) ^ 2 = 1225 / 4 := by
    rw [hContinuity]
    nlinarith [hvNozzleSq]
  norm_num [bernoulliEnergyDensityInPascals,
    hBoundary.freeSurfaceAtAtmosphericPressure,
    hBoundary.negligibleFreeSurfaceSpeed,
    hReference.waterDensitySI,
    hReference.gravitationalAccelerationSI,
    hFigure.pointOneElevationMeters,
    hFigure.pointTwoElevationMeters] at hBernoulli12
  norm_num [hydrostaticReferencePressureInPascals,
    hBoundary.freeSurfaceAtAtmosphericPressure,
    hReference.waterDensitySI,
    hReference.gravitationalAccelerationSI,
    hDistances.intakeDepthMeters] at hHydrostatic
  have hDeficit : inletPressureDeficitInPascals setup = 153125 := by
    rw [inletPressureDeficitInPascals]
    nlinarith [hBernoulli12]
  refine ⟨hDeficit, ?_, ?_, ?_⟩
  · rw [RoundsToDisplayedTenthAtmosphere,
      inletPressureDeficitInAtmospheres, hDeficit,
      hReference.atmosphericPressurePascals]
    norm_num [displayedPressureDifferenceInAtmospheres]
  · intro other
    rw [inletPressureDeficitInAtmospheres, hDeficit,
      hReference.atmosphericPressurePascals]
    fin_cases other <;>
      norm_num [displayedPressureDifferenceInAtmospheres,
        abs_of_nonneg, abs_of_nonpos]
  · intro choice hChoice
    fin_cases choice
    · exfalso
      have h := hChoice AnswerChoice.C
      rw [inletPressureDeficitInAtmospheres, hDeficit,
        hReference.atmosphericPressurePascals] at h
      norm_num [displayedPressureDifferenceInAtmospheres,
        abs_of_nonneg, abs_of_nonpos] at h
    · exfalso
      have h := hChoice AnswerChoice.C
      rw [inletPressureDeficitInAtmospheres, hDeficit,
        hReference.atmosphericPressurePascals] at h
      norm_num [displayedPressureDifferenceInAtmospheres,
        abs_of_nonneg, abs_of_nonpos] at h
    · rfl
    · exfalso
      have h := hChoice AnswerChoice.C
      rw [inletPressureDeficitInAtmospheres, hDeficit,
        hReference.atmosphericPressurePascals] at h
      norm_num [displayedPressureDifferenceInAtmospheres,
        abs_of_nonneg, abs_of_nonpos] at h

end PhyXMiniProblems.ProblemPhyXMini0725
