import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0722

open Dimension

/-!
# Tension holding a wooden cube underwater

A `10 cm × 10 cm × 10 cm` wooden block of density `700 kg/m³` is fully
submerged in water and held at rest by a string tied to the container bottom.
The supplied figure shows buoyancy upward and both gravity and string tension
downward.

Physlib's `Dimensionful` and `WithDim` types distinguish the physical
quantities from their coherent real-valued unit readouts.  In particular, the
string tension is an independent quantity in the setup rather than a
definition containing the recorded answer.
-/

/-! ## Dimensions, physical quantities, and unit readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative unit-independent physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative unit-independent physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative unit-independent physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative unit-independent physical force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical volume in the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read density in a selected mass unit per selected length unit cubed. -/
def densityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : MassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read force in coherent selected mass, length, and time units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Cubic-meter readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Kilogram-per-cubic-meter readout of a mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  densityReadout MassUnit.kilograms LengthUnit.meters density

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  forceReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-! ## Physical setup and supplied-figure vocabulary -/

/-- The material of the submerged block. -/
inductive BlockMaterial where
  | wood
  | other
  deriving DecidableEq, Repr

/-- The liquid surrounding the block. -/
inductive FluidKind where
  | water
  | other
  deriving DecidableEq, Repr

/-- Whether the block displaces its full geometric volume. -/
inductive ImmersionState where
  | fullySubmerged
  | partiallySubmerged
  deriving DecidableEq, Repr

/-- The anchoring geometry of the string. -/
inductive StringAttachment where
  | blockToContainerBottom
  | other
  deriving DecidableEq, Repr

/-- The translational state relevant to the force balance. -/
inductive MotionState where
  | heldAtRest
  | accelerating
  deriving DecidableEq, Repr

/-- Vertical directions used by the force arrows in image 722. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Physical objects and graphical elements visible in image 722. -/
inductive FigureObject where
  | container
  | waterRegion
  | woodBlock
  | string
  | buoyantForceArrow
  | gravitationalForceArrow
  | tensionArrow
  | buoyancyAnnotationLeader
  deriving DecidableEq, Fintype, Repr

/-- Text and force-symbol labels visible in image 722. -/
inductive FigureLabel where
  | blockOfWoodText
  | stringText
  | buoyantForceFB
  | gravitationalForceFG
  | tensionT
  | buoyantForcePushesUpText
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from the primary raster.  The image contains
force labels and directions but no numerical value of the requested tension.
-/
structure SuppliedSubmergedBlockFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  buoyantForceArrowDirection : VerticalDirection
  gravitationalForceArrowDirection : VerticalDirection
  tensionArrowDirection : VerticalDirection
  blockIsBelowWaterSurface : Bool
  stringJoinsBlockToContainerBottom : Bool
  containsNumericalTensionResult : Bool

/-!
Independent quantities and observables of the submerged-block experiment.
None of the force fields is defined from an answer choice.
-/
structure SubmergedWoodBlockSetup where
  material : BlockMaterial
  surroundingFluid : FluidKind
  immersionState : ImmersionState
  stringAttachment : StringAttachment
  motionState : MotionState
  sideLengthX : LengthQuantity
  sideLengthY : LengthQuantity
  sideLengthZ : LengthQuantity
  blockVolume : VolumeQuantity
  displacedWaterVolume : VolumeQuantity
  woodDensity : MassDensityQuantity
  waterDensity : MassDensityQuantity
  blockMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  buoyantForce : ForceQuantity
  gravitationalForce : ForceQuantity
  stringTension : ForceQuantity
  figure : SuppliedSubmergedBlockFigure

/-! ## Scenario, data readouts, and governing laws -/

/-- Categorical facts stated by the prose and shown in the figure. -/
structure MatchesSubmergedWoodBlockScenario
    (setup : SubmergedWoodBlockSetup) : Prop where
  blockIsWood : setup.material = .wood
  fluidIsWater : setup.surroundingFluid = .water
  blockIsFullySubmerged : setup.immersionState = .fullySubmerged
  stringIsTiedToBottom :
    setup.stringAttachment = .blockToContainerBottom
  blockIsHeldAtRest : setup.motionState = .heldAtRest

/-- Objects, labels, and force directions read from the primary image. -/
structure MatchesSuppliedSubmergedBlockFigure
    (setup : SubmergedWoodBlockSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  buoyancyPointsUp :
    setup.figure.buoyantForceArrowDirection = .upward
  gravityPointsDown :
    setup.figure.gravitationalForceArrowDirection = .downward
  tensionPointsDown : setup.figure.tensionArrowDirection = .downward
  blockBelowSurface : setup.figure.blockIsBelowWaterSurface = true
  stringGeometryShown :
    setup.figure.stringJoinsBlockToContainerBottom = true
  figureDoesNotContainAnswer :
    setup.figure.containsNumericalTensionResult = false

/-!
Numerical readouts explicitly given in the problem.  Keeping all three side
lengths preserves the `10 cm × 10 cm × 10 cm` geometry.
-/
structure MatchesSubmergedBlockProblemReadouts
    (setup : SubmergedWoodBlockSetup) : Prop where
  sideLengthXCentimeters : lengthInCentimeters setup.sideLengthX = 10
  sideLengthYCentimeters : lengthInCentimeters setup.sideLengthY = 10
  sideLengthZCentimeters : lengthInCentimeters setup.sideLengthZ = 10
  woodDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.woodDensity = 700

/-!
Textbook calibrations implicit in the recorded answer: freshwater density is
`1000 kg/m³` and near-Earth gravitational acceleration is `9.8 m/s²`.  They
are kept separate from the values printed in the question.
-/
structure UsesStandardWaterAndGravity
    (setup : SubmergedWoodBlockSetup) : Prop where
  waterDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.waterDensity = 1000
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-- Positivity and nondegeneracy conditions for the physical setup. -/
structure HasPhysicalSubmergedBlockParameters
    (setup : SubmergedWoodBlockSetup) : Prop where
  sideLengthXPositive : 0 < lengthInMeters setup.sideLengthX
  sideLengthYPositive : 0 < lengthInMeters setup.sideLengthY
  sideLengthZPositive : 0 < lengthInMeters setup.sideLengthZ
  blockVolumePositive : 0 < volumeInCubicMeters setup.blockVolume
  displacedVolumePositive :
    0 < volumeInCubicMeters setup.displacedWaterVolume
  woodDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.woodDensity
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterDensity
  blockMassPositive : 0 < massInKilograms setup.blockMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-!
Cube-volume and full-submersion displacement laws, stated in every coherent
length unit.  These laws do not mention any force result.
-/
structure SatisfiesCubeAndDisplacementLaws
    (setup : SubmergedWoodBlockSetup) : Prop where
  blockVolumeIsProductOfSides :
    ∀ unit : LengthUnit,
      volumeReadout unit setup.blockVolume =
        lengthReadout unit setup.sideLengthX *
          lengthReadout unit setup.sideLengthY *
            lengthReadout unit setup.sideLengthZ
  fullSubmersionDisplacesBlockVolume :
    ∀ unit : LengthUnit,
      volumeReadout unit setup.displacedWaterVolume =
        volumeReadout unit setup.blockVolume

/-!
The governing hydrostatic and statics laws: mass from density and volume,
weight from mass and gravity, Archimedes' buoyant-force law, and the vertical
force balance for a block held at rest.  None contains the requested tension
or an answer-choice number.
-/
structure SatisfiesSubmergedBlockStaticsLaws
    (setup : SubmergedWoodBlockSetup) : Prop where
  blockMassFromDensity :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      massReadout massUnit setup.blockMass =
        densityReadout massUnit lengthUnit setup.woodDensity *
          volumeReadout lengthUnit setup.blockVolume
  gravitationalForceLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit
          setup.gravitationalForce =
        massReadout massUnit setup.blockMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration
  archimedesBuoyantForceLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit setup.buoyantForce =
        densityReadout massUnit lengthUnit setup.waterDensity *
          volumeReadout lengthUnit setup.displacedWaterVolume *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration
  verticalStaticEquilibrium :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit setup.buoyantForce =
        forceReadout massUnit lengthUnit timeUnit
            setup.gravitationalForce +
          forceReadout massUnit lengthUnit timeUnit setup.stringTension

/-! ## Answer choices and target -/

/-- Labels of the four force alternatives printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Tension in newtons printed beside each answer label. -/
def displayedTensionInNewtons : AnswerChoice → ℝ
  | .A => 7 / 2
  | .B => 16 / 5
  | .C => 29 / 10
  | .D => 19 / 5

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a force displayed to the nearest tenth of a newton. -/
def RoundsToNearestTenthNewton
    (force : ForceQuantity) (displayedNewtons : ℝ) : Prop :=
  |forceInNewtons force - displayedNewtons| < 1 / 20

/-- A displayed choice is at least as close as every alternative. -/
def IsNearestDisplayedTension
    (setup : SubmergedWoodBlockSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |forceInNewtons setup.stringTension -
        displayedTensionInNewtons choice| ≤
      |forceInNewtons setup.stringTension -
        displayedTensionInNewtons other|

/-!
The laws yield an exact modeled tension of `2.94 N = 147/50 N`.  It rounds
to the printed `2.9 N`, and choice C is the unique closest displayed answer.

This is the declaration for `thm:physics:phyx_mini_0722:target`.
-/
theorem problem_phyx_mini_0722
    (setup : SubmergedWoodBlockSetup)
    (hScenario : MatchesSubmergedWoodBlockScenario setup)
    (hFigure : MatchesSuppliedSubmergedBlockFigure setup)
    (hReadouts : MatchesSubmergedBlockProblemReadouts setup)
    (hCalibration : UsesStandardWaterAndGravity setup)
    (hPhysical : HasPhysicalSubmergedBlockParameters setup)
    (hGeometry : SatisfiesCubeAndDisplacementLaws setup)
    (hLaws : SatisfiesSubmergedBlockStaticsLaws setup) :
    forceInNewtons setup.stringTension = 147 / 50 ∧
      RoundsToNearestTenthNewton setup.stringTension
        (displayedTensionInNewtons .C) ∧
      IsNearestDisplayedTension setup .C ∧
      ∀ choice : AnswerChoice,
        IsNearestDisplayedTension setup choice → choice = .C := by
  have centimeters_eq_one_hundred_meters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value : WithDim L𝓭 NNReal => (value.val : ℝ))
      (length.2 UnitChoices.SI
        ({UnitChoices.SI with length := LengthUnit.centimeters} :
          UnitChoices))
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, WithDim.smul_val,
      NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have hSideX : lengthInMeters setup.sideLengthX = 1 / 10 := by
    have h := hReadouts.sideLengthXCentimeters
    rw [centimeters_eq_one_hundred_meters] at h
    norm_num at h ⊢
    linarith
  have hSideY : lengthInMeters setup.sideLengthY = 1 / 10 := by
    have h := hReadouts.sideLengthYCentimeters
    rw [centimeters_eq_one_hundred_meters] at h
    norm_num at h ⊢
    linarith
  have hSideZ : lengthInMeters setup.sideLengthZ = 1 / 10 := by
    have h := hReadouts.sideLengthZCentimeters
    rw [centimeters_eq_one_hundred_meters] at h
    norm_num at h ⊢
    linarith
  have hBlockVolume :
      volumeInCubicMeters setup.blockVolume = 1 / 1000 := by
    have h :=
      hGeometry.blockVolumeIsProductOfSides LengthUnit.meters
    change
      volumeInCubicMeters setup.blockVolume =
        lengthInMeters setup.sideLengthX *
          lengthInMeters setup.sideLengthY *
            lengthInMeters setup.sideLengthZ at h
    rw [hSideX, hSideY, hSideZ] at h
    norm_num at h ⊢
    exact h
  have hDisplacedVolume :
      volumeInCubicMeters setup.displacedWaterVolume = 1 / 1000 := by
    have h :=
      hGeometry.fullSubmersionDisplacesBlockVolume LengthUnit.meters
    change
      volumeInCubicMeters setup.displacedWaterVolume =
        volumeInCubicMeters setup.blockVolume at h
    rw [hBlockVolume] at h
    exact h
  have hBlockMass : massInKilograms setup.blockMass = 7 / 10 := by
    have h := hLaws.blockMassFromDensity
      MassUnit.kilograms LengthUnit.meters
    change
      massInKilograms setup.blockMass =
        densityInKilogramsPerCubicMeter setup.woodDensity *
          volumeInCubicMeters setup.blockVolume at h
    rw [hReadouts.woodDensityKilogramsPerCubicMeter, hBlockVolume] at h
    norm_num at h ⊢
    exact h
  have hGravity :
      accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5 :=
    hCalibration.gravitationalAccelerationMetersPerSecondSquared
  have hWeight :
      forceInNewtons setup.gravitationalForce = 343 / 50 := by
    have h := hLaws.gravitationalForceLaw
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
    change
      forceInNewtons setup.gravitationalForce =
        massInKilograms setup.blockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration at h
    rw [hBlockMass, hGravity] at h
    norm_num at h ⊢
    exact h
  have hBuoyancy : forceInNewtons setup.buoyantForce = 49 / 5 := by
    have h := hLaws.archimedesBuoyantForceLaw
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
    change
      forceInNewtons setup.buoyantForce =
        densityInKilogramsPerCubicMeter setup.waterDensity *
            volumeInCubicMeters setup.displacedWaterVolume *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration at h
    rw [hCalibration.waterDensityKilogramsPerCubicMeter,
      hDisplacedVolume, hGravity] at h
    norm_num at h ⊢
    exact h
  have hTension : forceInNewtons setup.stringTension = 147 / 50 := by
    have h := hLaws.verticalStaticEquilibrium
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
    change
      forceInNewtons setup.buoyantForce =
        forceInNewtons setup.gravitationalForce +
          forceInNewtons setup.stringTension at h
    rw [hBuoyancy, hWeight] at h
    norm_num at h ⊢
    linarith
  refine ⟨hTension, ?_, ?_, ?_⟩
  · norm_num [RoundsToNearestTenthNewton, displayedTensionInNewtons,
      hTension, abs_of_nonneg, abs_of_neg]
  · intro other
    cases other <;>
      norm_num [IsNearestDisplayedTension, displayedTensionInNewtons,
        hTension, abs_of_nonneg, abs_of_neg]
  · intro choice hChoice
    cases choice with
    | A =>
        have h := hChoice .C
        norm_num [IsNearestDisplayedTension, displayedTensionInNewtons,
          hTension, abs_of_nonneg, abs_of_neg] at h
    | B =>
        have h := hChoice .C
        norm_num [IsNearestDisplayedTension, displayedTensionInNewtons,
          hTension, abs_of_nonneg, abs_of_neg] at h
    | C => rfl
    | D =>
        have h := hChoice .C
        norm_num [IsNearestDisplayedTension, displayedTensionInNewtons,
          hTension, abs_of_nonneg, abs_of_neg] at h

end PhyXMiniProblems.ProblemPhyXMini0722
