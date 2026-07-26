import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0662

open Dimension

/-!
# Water pressure required to lift a piston

The intended source scenario is a vertical piston of cross-sectional area
`0.01 m²` and mass `100 kg`, initially resting on stops.  Water acts on its
lower face and an outside atmosphere at `100 kPa` acts on its upper face.  At
incipient lift the water-pressure force balances the atmospheric-pressure
force and the piston's weight.

The supplied raster is inconsistent with that scenario: it is an optics
diagram carrying the labels `θ₁` and `n_g`.  The declarations below preserve
that primary-image evidence separately from the intended piston model instead
of inventing piston labels that are not visible in the file.

Physical magnitudes use Physlib's unit-independent dimension system.  Real
numbers occur only as coherent-SI readouts, schematic data, and displayed
multiple-choice values.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative physical mass, independent of a choice of units. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude carrying dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude carrying dimension `M L T⁻²`. -/
abbrev ForceMagnitude : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical force magnitude in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Normal force in newtons exerted by a uniform pressure on the piston face. -/
def pressureForceInNewtons (pressure : DimPressure) (area : DimArea) : ℝ :=
  pressureInPascals pressure * areaInSquareMeters area

/-- Downward piston weight in newtons. -/
def weightInNewtons
    (mass : MassQuantity) (acceleration : AccelerationQuantity) : ℝ :=
  massInKilograms mass *
    accelerationInMetersPerSecondSquared acceleration

/-! ## Intended piston apparatus and operating state -/

/-- Fluid acting on the lower piston face. -/
inductive WorkingFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-- Mechanically distinguished phases around the start of piston motion. -/
inductive PistonPhase where
  | restingOnStops
  | incipientLift
  | movingUpward
  deriving DecidableEq, Repr

/-- Vertical directions relevant to the force balance. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Regions on opposite sides of the piston. -/
inductive PistonFaceRegion where
  | waterBelow
  | outsideAtmosphereAbove
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative content of the intended piston/cylinder schematic described by the
source metadata.  Numerical quantities remain independent fields of the setup.
-/
structure IntendedPistonDiagram where
  showsVerticalCylinder : Bool
  showsPiston : Bool
  showsLowerStops : Bool
  showsWaterBelowPiston : Bool
  showsOutsideAtmosphereAbovePiston : Bool
  regionForLowerFace : PistonFaceRegion
  regionForUpperFace : PistonFaceRegion

/-! ## Literal vocabulary of the actually supplied optics raster -/

/-- Labels visibly printed in the supplied, mismatched raster. -/
inductive RasterLabel where
  | thetaOne
  | nSubG
  deriving DecidableEq, Fintype, Repr

/-- Ray-like lines visible in the supplied raster. -/
inductive RasterRay where
  | incident
  | reflected
  | refracted
  | dashedNormal
  deriving DecidableEq, Fintype, Repr

/-- Schematic arrow directions in image coordinates. -/
inductive RasterDirection where
  | downwardRight
  | upwardRight
  | vertical
  deriving DecidableEq, Repr

/-!
Primary-image evidence retained independently of the piston calculation.  The
negative fields make the source-asset mismatch explicit rather than silently
treating the optics picture as a piston diagram.
-/
structure SuppliedOpticsRaster where
  showsLabel : RasterLabel → Bool
  showsRay : RasterRay → Bool
  rayDirection : RasterRay → RasterDirection
  showsHorizontalInterface : Bool
  showsShadedRectangularMedium : Bool
  showsRightAngleMarkerAtInterface : Bool
  showsPiston : Bool
  showsPressureReadout : Bool
  showsAreaReadout : Bool
  showsMassReadout : Bool

/-!
The independent physical apparatus.  The unknown water pressure is a genuine
field: it is not defined from the answer choices or from the target value.
-/
structure PistonLiftSetup where
  intendedDiagram : IntendedPistonDiagram
  suppliedRaster : SuppliedOpticsRaster
  fluid : WorkingFluid
  initialPistonPhase : PistonPhase
  thresholdPistonPhase : PistonPhase
  liftDirection : VerticalDirection
  pistonCrossSectionalArea : DimArea
  pistonMass : MassQuantity
  outsideAtmosphericPressure : DimPressure
  waterPressureAtIncipientLift : DimPressure
  gravitationalAcceleration : AccelerationQuantity
  stopReactionAtIncipientLift : ForceMagnitude
  pressureIsUniformOnEachPistonFace : Bool
  pressureActsNormallyOnPiston : Bool
  pistonFrictionIsNegligible : Bool

/-! ## Scenario, figure/data readouts, and governing laws -/

/-- Qualitative apparatus assumptions of the intended piston problem. -/
structure MatchesIntendedPistonScenario
    (setup : PistonLiftSetup) : Prop where
  workingFluidIsWater : setup.fluid = .water
  initiallyRestingOnStops : setup.initialPistonPhase = .restingOnStops
  stateIsIncipientLift : setup.thresholdPistonPhase = .incipientLift
  requestedMotionIsUpward : setup.liftDirection = .upward
  verticalCylinderShown : setup.intendedDiagram.showsVerticalCylinder = true
  pistonShown : setup.intendedDiagram.showsPiston = true
  lowerStopsShown : setup.intendedDiagram.showsLowerStops = true
  waterShownBelow : setup.intendedDiagram.showsWaterBelowPiston = true
  atmosphereShownAbove :
    setup.intendedDiagram.showsOutsideAtmosphereAbovePiston = true
  lowerFaceTouchesWater :
    setup.intendedDiagram.regionForLowerFace = .waterBelow
  upperFaceTouchesAtmosphere :
    setup.intendedDiagram.regionForUpperFace = .outsideAtmosphereAbove

/-!
Transcription of the actual primary raster.  It records no piston pressure,
mass, area, acceleration, or answer-choice value.
-/
structure MatchesSuppliedOpticsRaster
    (setup : PistonLiftSetup) : Prop where
  everyOpticsLabelShown :
    ∀ label : RasterLabel, setup.suppliedRaster.showsLabel label = true
  everyRayShown :
    ∀ ray : RasterRay, setup.suppliedRaster.showsRay ray = true
  incidentRayDirection :
    setup.suppliedRaster.rayDirection .incident = .downwardRight
  reflectedRayDirection :
    setup.suppliedRaster.rayDirection .reflected = .upwardRight
  refractedRayDirection :
    setup.suppliedRaster.rayDirection .refracted = .downwardRight
  normalDirection :
    setup.suppliedRaster.rayDirection .dashedNormal = .vertical
  horizontalInterfaceShown :
    setup.suppliedRaster.showsHorizontalInterface = true
  shadedMediumShown :
    setup.suppliedRaster.showsShadedRectangularMedium = true
  rightAngleMarkerShown :
    setup.suppliedRaster.showsRightAngleMarkerAtInterface = true
  noPistonShown : setup.suppliedRaster.showsPiston = false
  noPressureReadoutShown : setup.suppliedRaster.showsPressureReadout = false
  noAreaReadoutShown : setup.suppliedRaster.showsAreaReadout = false
  noMassReadoutShown : setup.suppliedRaster.showsMassReadout = false

/-!
Numerical information supplied by the intended scenario and question.  The
unknown water pressure and the recorded answer do not occur here.
-/
structure MatchesPistonProblemReadouts
    (setup : PistonLiftSetup) : Prop where
  pistonAreaSquareMeters :
    areaInSquareMeters setup.pistonCrossSectionalArea = 1 / 100
  pistonMassKilograms : massInKilograms setup.pistonMass = 100
  outsidePressureKilopascals :
    pressureInKilopascals setup.outsideAtmosphericPressure = 100

/-!
Near-Earth gravity used by the recorded multiple-choice answer.  This is an
independent environmental calibration, not a pressure conclusion.
-/
structure UsesNearEarthGravity
    (setup : PistonLiftSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-- Positivity conditions selecting the nondegenerate physical branch. -/
structure HasPhysicalPistonParameters
    (setup : PistonLiftSetup) : Prop where
  pistonAreaPositive :
    0 < areaInSquareMeters setup.pistonCrossSectionalArea
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  outsidePressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressure
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-!
Idealizations used by the elementary threshold calculation.  They contain no
numerical water-pressure conclusion.
-/
structure MatchesIdealPistonLiftModel
    (setup : PistonLiftSetup) : Prop where
  uniformFacePressures : setup.pressureIsUniformOnEachPistonFace = true
  pressureNormalToFaces : setup.pressureActsNormallyOnPiston = true
  negligiblePistonFriction : setup.pistonFrictionIsNegligible = true

/-!
Governing mechanics at incipient lift:

* the supporting stop reaction has just fallen to zero; and
* upward water-pressure force plus the stop reaction balances downward
  atmospheric-pressure force plus piston weight.

This is a generic force law and contains none of the supplied numerical data
or displayed pressure choices.
-/
structure SatisfiesIncipientLiftForceLaws
    (setup : PistonLiftSetup) : Prop where
  stopReactionVanishesAtLift :
    forceInNewtons setup.stopReactionAtIncipientLift = 0
  verticalForceBalance :
    pressureForceInNewtons setup.waterPressureAtIncipientLift
          setup.pistonCrossSectionalArea +
        forceInNewtons setup.stopReactionAtIncipientLift =
      pressureForceInNewtons setup.outsideAtmosphericPressure
          setup.pistonCrossSectionalArea +
        weightInNewtons setup.pistonMass
          setup.gravitationalAcceleration

/-! ## Displayed answer choices and current target -/

/-- Labels printed beside the four proposed water pressures. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Water-pressure readout in kilopascals printed beside each answer label. -/
def displayedPressureInKilopascals : AnswerChoice → ℝ
  | .A => 208
  | .B => 98
  | .C => 100
  | .D => 198

/-- A displayed choice agrees with the independently determined pressure. -/
def SelectsDisplayedPressure
    (setup : PistonLiftSetup) (choice : AnswerChoice) : Prop :=
  pressureInKilopascals setup.waterPressureAtIncipientLift =
    displayedPressureInKilopascals choice

/-!
The pressure increment needed to carry the piston weight is
`m g / A = 98 kPa`.  Adding the `100 kPa` outside atmospheric pressure gives
an absolute water pressure of `198 kPa`, so the selected answer is D.

This formalizes `thm:physics:phyx_mini_0662:target`.
-/
theorem problem_phyx_mini_0662
    (setup : PistonLiftSetup)
    (hScenario : MatchesIntendedPistonScenario setup)
    (hRaster : MatchesSuppliedOpticsRaster setup)
    (hReadouts : MatchesPistonProblemReadouts setup)
    (hGravity : UsesNearEarthGravity setup)
    (hPhysical : HasPhysicalPistonParameters setup)
    (hIdealModel : MatchesIdealPistonLiftModel setup)
    (hForceLaws : SatisfiesIncipientLiftForceLaws setup) :
    pressureInKilopascals setup.waterPressureAtIncipientLift = 198 ∧
      SelectsDisplayedPressure setup .D := by
  rcases hReadouts with ⟨hArea, hMass, hOutside⟩
  rcases hGravity with ⟨hAccel⟩
  rcases hForceLaws with ⟨hStop, hBalance⟩
  have hPressure :
      pressureInKilopascals setup.waterPressureAtIncipientLift = 198 := by
    simp only [pressureForceInNewtons, weightInNewtons] at hBalance
    rw [hStop, hArea, hMass, hAccel] at hBalance
    norm_num [pressureInKilopascals] at hOutside ⊢
    nlinarith [hBalance]
  refine ⟨hPressure, ?_⟩
  simpa [SelectsDisplayedPressure, displayedPressureInKilopascals]
    using hPressure

end PhyXMiniProblems.ProblemPhyXMini0662
