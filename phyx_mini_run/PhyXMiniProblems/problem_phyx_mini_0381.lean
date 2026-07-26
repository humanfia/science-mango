import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0381

open Dimension

/-!
# Upward push of a hydraulic piston rod

The cylinder bore has diameter `0.1 m`; the rod has diameter `0.01 m`; the
piston--rod assembly has mass `25 kg`; the pressure below the piston is
`250 kPa`; and the atmosphere above it is at `101 kPa`.  The supplied raster
labels the two pressure regions by `P_cyl` and `P₀`, labels the rod
cross-section by `A_rod`, and shows the reaction load `F` directed downward on
the top of the rod.

Physlib dimensionful quantities are used for every physical magnitude.  Real
numbers occur below only as named-unit readouts, schematic coordinates, or
displayed answer values.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical length, independent of a choice of units. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude, with SI unit newton. -/
abbrev ForceQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a physical force magnitude in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-! ## Apparatus roles and primary-raster vocabulary -/

/-- Material or component visible in the supplied hydraulic-cylinder raster. -/
inductive FigureObject where
  | cylinderBody
  | hydraulicFluid
  | piston
  | rod
  | sidePort
  deriving DecidableEq, Fintype, Repr

/-- The two pressure regions distinguished in the drawing. -/
inductive FigureRegion where
  | atmosphereAbovePiston
  | cylinderFluidBelowPiston
  deriving DecidableEq, Fintype, Repr

/-- Literal pressure labels printed in the drawing. -/
inductive FigurePressureLabel where
  | P0
  | Pcyl
  deriving DecidableEq, Fintype, Repr

/-- The area label printed next to the circular rod cross-section. -/
inductive FigureAreaLabel where
  | Arod
  deriving DecidableEq, Fintype, Repr

/-- The force label printed above the rod. -/
inductive FigureForceLabel where
  | F
  deriving DecidableEq, Fintype, Repr

/-- Surfaces that enter the piston force balance. -/
inductive LoadedSurface where
  | fullLowerPistonFace
  | exposedUpperAnnulus
  | rodEndCrossSection
  deriving DecidableEq, Fintype, Repr

/-- Vertical orientation in the figure and in the requested output. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Static, idealized operating regime used by the elementary force balance. -/
inductive OperatingRegime where
  | staticEquilibrium
  deriving DecidableEq, Repr

/-!
Qualitative and schematic information transcribed from the primary raster.
Coordinates are diagram readouts only; they are not physical lengths.
-/
structure SuppliedHydraulicPistonFigure where
  showsObject : FigureObject → Bool
  showsPressureLabel : FigurePressureLabel → Bool
  pressureLabelRegion : FigurePressureLabel → FigureRegion
  showsAreaLabel : FigureAreaLabel → Bool
  areaLabelSurface : FigureAreaLabel → LoadedSurface
  showsForceLabel : FigureForceLabel → Bool
  forceArrowDirection : FigureForceLabel → VerticalDirection
  forceArrowSurface : FigureForceLabel → LoadedSurface
  schematicVerticalCoordinate : FigureObject → ℝ

/-!
Physical apparatus and observables.  In particular, neither force field is
defined from an answer choice: the downward contact load on the assembly and
the upward force exerted by the rod are independent physical quantities until
the action--reaction law below relates their magnitudes.
-/
structure HydraulicPistonSetup where
  figure : SuppliedHydraulicPistonFigure
  operatingRegime : OperatingRegime
  pistonMotionDirection : VerticalDirection
  requestedRodPushDirection : VerticalDirection
  cylinderBoreDiameter : LengthQuantity
  rodDiameter : LengthQuantity
  pistonRodAssemblyMass : MassQuantity
  pistonLowerFaceArea : DimArea
  rodCrossSectionArea : DimArea
  exposedUpperAnnularArea : DimArea
  outsideAtmosphericPressure : DimPressure
  insideCylinderPressure : DimPressure
  gravitationalAcceleration : AccelerationQuantity
  downwardContactLoadOnRod : ForceQuantity
  upwardForceExertedByRod : ForceQuantity
  pistonIsFrictionless : Bool

/-! ## Scenario data, raster evidence, geometry, and governing laws -/

/-!
Numerical data stated in the problem.  No force value or answer choice occurs
in this structure.
-/
structure MatchesStatedHydraulicData
    (setup : HydraulicPistonSetup) : Prop where
  cylinderDiameterMeters :
    lengthInMeters setup.cylinderBoreDiameter = 1 / 10
  rodDiameterMeters :
    lengthInMeters setup.rodDiameter = 1 / 100
  assemblyMassKilograms :
    massInKilograms setup.pistonRodAssemblyMass = 25
  outsidePressureKilopascals :
    pressureInKilopascals setup.outsideAtmosphericPressure = 101
  insidePressureKilopascals :
    pressureInKilopascals setup.insideCylinderPressure = 250

/-!
Primary-image evidence: `P₀` lies above the piston, `P_cyl` lies in the
hydraulic fluid below it, `A_rod` marks the rod end, and the arrow `F` is the
downward reaction load on that end.
-/
structure MatchesPrimaryHydraulicFigure
    (setup : HydraulicPistonSetup) : Prop where
  everyComponentShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyPressureLabelShown :
    ∀ label : FigurePressureLabel,
      setup.figure.showsPressureLabel label = true
  outsidePressureLabelPlacement :
    setup.figure.pressureLabelRegion .P0 = .atmosphereAbovePiston
  cylinderPressureLabelPlacement :
    setup.figure.pressureLabelRegion .Pcyl = .cylinderFluidBelowPiston
  rodAreaLabelShown : setup.figure.showsAreaLabel .Arod = true
  rodAreaLabelPlacement :
    setup.figure.areaLabelSurface .Arod = .rodEndCrossSection
  forceLabelShown : setup.figure.showsForceLabel .F = true
  displayedForcePointsDownward :
    setup.figure.forceArrowDirection .F = .downward
  displayedForceActsOnRodEnd :
    setup.figure.forceArrowSurface .F = .rodEndCrossSection
  hydraulicFluidBelowPiston :
    setup.figure.schematicVerticalCoordinate .hydraulicFluid <
      setup.figure.schematicVerticalCoordinate .piston
  rodAbovePiston :
    setup.figure.schematicVerticalCoordinate .piston <
      setup.figure.schematicVerticalCoordinate .rod

/-- Idealizations implicit in the elementary static piston calculation. -/
structure MatchesHydraulicOperatingScenario
    (setup : HydraulicPistonSetup) : Prop where
  staticOperatingPoint : setup.operatingRegime = .staticEquilibrium
  pistonAxisIsVertical : setup.pistonMotionDirection = .upward
  requestedPushIsUpward : setup.requestedRodPushDirection = .upward
  frictionlessPiston : setup.pistonIsFrictionless = true

/-!
Circular-face and annular-face geometry.  Atmospheric pressure acts on the
exposed upper annulus; the contacted rod end is represented separately by the
downward load `F` shown in the raster.
-/
structure SatisfiesPistonGeometry
    (setup : HydraulicPistonSetup) : Prop where
  lowerFaceIsCircular :
    areaInSquareMeters setup.pistonLowerFaceArea =
      Real.pi * (lengthInMeters setup.cylinderBoreDiameter / 2) ^ 2
  rodCrossSectionIsCircular :
    areaInSquareMeters setup.rodCrossSectionArea =
      Real.pi * (lengthInMeters setup.rodDiameter / 2) ^ 2
  exposedUpperFaceIsAnnular :
    areaInSquareMeters setup.exposedUpperAnnularArea =
      areaInSquareMeters setup.pistonLowerFaceArea -
        areaInSquareMeters setup.rodCrossSectionArea

/-! Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalHydraulicParameters
    (setup : HydraulicPistonSetup) : Prop where
  cylinderDiameterPositive :
    0 < lengthInMeters setup.cylinderBoreDiameter
  rodDiameterPositive : 0 < lengthInMeters setup.rodDiameter
  rodNarrowerThanCylinder :
    lengthInMeters setup.rodDiameter <
      lengthInMeters setup.cylinderBoreDiameter
  assemblyMassPositive : 0 < massInKilograms setup.pistonRodAssemblyMass
  lowerFaceAreaPositive : 0 < areaInSquareMeters setup.pistonLowerFaceArea
  rodAreaPositive : 0 < areaInSquareMeters setup.rodCrossSectionArea
  annularAreaPositive : 0 < areaInSquareMeters setup.exposedUpperAnnularArea
  outsidePressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressure
  insidePressurePositive :
    0 < pressureInPascals setup.insideCylinderPressure
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-!
The standard near-Earth acceleration used by the recorded numerical answer.
This is a physical calibration, not a force conclusion.
-/
structure UsesTerrestrialGravityCalibration
    (setup : HydraulicPistonSetup) : Prop where
  standardGravitySI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 981 / 100

/-!
Elementary mechanics of the idealized hydraulic piston:

* pressure force has magnitude `p A` on each loaded face;
* the assembly weight has magnitude `m g`;
* at static equilibrium, the upward cylinder-pressure force balances the
  atmospheric force on the exposed annulus, the weight, and the downward rod
  contact load;
* the upward rod push and downward contact load form an action--reaction pair.

None of these laws prescribes the numerical value of the unknown rod force.
-/
structure SatisfiesHydraulicForceLaws
    (setup : HydraulicPistonSetup) : Prop where
  staticVerticalForceBalance :
    pressureInPascals setup.insideCylinderPressure *
        areaInSquareMeters setup.pistonLowerFaceArea =
      pressureInPascals setup.outsideAtmosphericPressure *
          areaInSquareMeters setup.exposedUpperAnnularArea +
        massInKilograms setup.pistonRodAssemblyMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration +
        forceInNewtons setup.downwardContactLoadOnRod
  rodContactActionReaction :
    forceInNewtons setup.upwardForceExertedByRod =
      forceInNewtons setup.downwardContactLoadOnRod

/-! ## Displayed answers and current target -/

/-- Labels of the four force choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Newton value displayed beside each answer label. -/
def displayedForceInNewtons : AnswerChoice → ℝ
  | .A => 490
  | .B => 9329 / 10
  | .C => 154
  | .D => 51 / 5

/-- Distance between the physical upward push and a displayed force choice. -/
def distanceFromDisplayedForce
    (setup : HydraulicPistonSetup) (choice : AnswerChoice) : ℝ :=
  |forceInNewtons setup.upwardForceExertedByRod -
    displayedForceInNewtons choice|

/-- A displayed answer is strictly closer than every other listed force. -/
def IsUniqueClosestDisplayedForce
    (setup : HydraulicPistonSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    other ≠ choice →
      distanceFromDisplayedForce setup choice <
        distanceFromDisplayedForce setup other

/-- The physical newton readout rounds to the stated value at one decimal. -/
def RoundsToNearestTenthOfNewton
    (setup : HydraulicPistonSetup) (reportedNewtons : ℝ) : Prop :=
  |forceInNewtons setup.upwardForceExertedByRod - reportedNewtons| < 1 / 20

/-!
Blueprint label: `thm:physics:phyx_mini_0381:target`.

The stated dimensions, pressures, mass, standard gravity, circular/annular
geometry, and static force balance make the rod's upward push round to
`932.9 N`; this is uniquely closest to displayed answer B.
-/
theorem hydraulicRod_upwardPushForce
    (setup : HydraulicPistonSetup)
    (hScenario : MatchesHydraulicOperatingScenario setup)
    (hData : MatchesStatedHydraulicData setup)
    (hFigure : MatchesPrimaryHydraulicFigure setup)
    (hGeometry : SatisfiesPistonGeometry setup)
    (hPhysical : HasPhysicalHydraulicParameters setup)
    (hGravity : UsesTerrestrialGravityCalibration setup)
    (hForces : SatisfiesHydraulicForceLaws setup) :
    RoundsToNearestTenthOfNewton setup (9329 / 10) ∧
      IsUniqueClosestDisplayedForce setup .B := by
  have hOutsidePa :
      pressureInPascals setup.outsideAtmosphericPressure = 101000 := by
    have h := hData.outsidePressureKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hInsidePa :
      pressureInPascals setup.insideCylinderPressure = 250000 := by
    have h := hData.insidePressureKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hLowerArea :
      areaInSquareMeters setup.pistonLowerFaceArea = Real.pi / 400 := by
    rw [hGeometry.lowerFaceIsCircular, hData.cylinderDiameterMeters]
    ring
  have hRodArea :
      areaInSquareMeters setup.rodCrossSectionArea = Real.pi / 40000 := by
    rw [hGeometry.rodCrossSectionIsCircular, hData.rodDiameterMeters]
    ring
  have hAnnularArea :
      areaInSquareMeters setup.exposedUpperAnnularArea =
        99 * Real.pi / 40000 := by
    rw [hGeometry.exposedUpperFaceIsAnnular, hLowerArea, hRodArea]
    ring
  have hPush :
      forceInNewtons setup.upwardForceExertedByRod =
        15001 * Real.pi / 40 - 981 / 4 := by
    have hBalance := hForces.staticVerticalForceBalance
    rw [hForces.rodContactActionReaction]
    rw [hInsidePa, hOutsidePa, hLowerArea, hAnnularArea,
      hData.assemblyMassKilograms, hGravity.standardGravitySI]
      at hBalance
    linarith [hBalance]
  have hPiLower : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hPiUpper : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  constructor
  · unfold RoundsToNearestTenthOfNewton
    rw [hPush]
    rw [abs_lt]
    constructor <;>
      norm_num at hPiLower hPiUpper ⊢ <;>
      linarith [hPiLower, hPiUpper]
  · intro other hOther
    fin_cases other
    · unfold distanceFromDisplayedForce
      simp only [displayedForceInNewtons]
      rw [hPush]
      norm_num at hPiLower hPiUpper ⊢
      rw [abs_of_pos, abs_of_pos] <;>
        linarith [hPiLower, hPiUpper]
    · exact (hOther rfl).elim
    · unfold distanceFromDisplayedForce
      simp only [displayedForceInNewtons]
      rw [hPush]
      norm_num at hPiLower hPiUpper ⊢
      rw [abs_of_pos, abs_of_pos] <;>
        linarith [hPiLower, hPiUpper]
    · unfold distanceFromDisplayedForce
      simp only [displayedForceInNewtons]
      rw [hPush]
      norm_num at hPiLower hPiUpper ⊢
      rw [abs_of_pos, abs_of_pos] <;>
        linarith [hPiLower, hPiUpper]

end PhyXMiniProblems.ProblemPhyXMini0381
