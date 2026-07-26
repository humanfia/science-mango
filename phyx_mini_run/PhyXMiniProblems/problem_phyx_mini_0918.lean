import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0918

open Dimension
open Space

/-!
# Motional emf in a slidewire generator

The raster `918.png` shows a vertical conducting rod of length `L` bridging
two horizontal rails.  It moves right at constant speed `v` through a uniform
magnetic field directed into the page.  The into-page area normal fixes the
positive (clockwise) boundary orientation, so the induced counterclockwise emf
has negative sign.

Physical magnitudes are represented by Physlib's unit-covariant
`Dimensionful (WithDim ...)` types.  Real numbers occur only at coherent-SI
readout boundaries and in the expressions printed as answer choices.

Assumption/target split:

* `MatchesSlidewireGeneratorScenario` and
  `MatchesSuppliedSlidewireFigure` record apparatus and image data;
* `HasPhysicalSlidewireParameters` records nondegeneracy;
* `ModelsUniformIntoPageMagneticField`, `SatisfiesSlidewireKinematics`,
  `SatisfiesUniformMagneticFluxLaw`, `SatisfiesFaradayInductionLaw`,
  `SatisfiesMotionalEmfDirectionLaw`, and
  `SatisfiesPassiveConductorResponse` state governing laws separately; and
* `problem_phyx_mini_0918` alone combines those premises into the requested
  signed emf, magnitude, and direction.  No premise contains `-B * L * v`.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Area has dimension `L²`. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Area-change rate has dimension `L² T⁻¹`. -/
def areaRateDimension : Dimension :=
  areaDimension * T𝓭⁻¹

/-- Magnetic flux has dimension `M L² T⁻¹ C⁻¹`. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Electromotive force, or magnetic-flux rate, has dimension
`M L² T⁻² C⁻¹`. -/
def electromotiveForceDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Electric current has dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent elapsed time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A signed area-change rate relative to the chosen area orientation. -/
abbrev SignedAreaRateQuantity : Type :=
  Dimensionful (WithDim areaRateDimension ℝ)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Signed magnetic flux relative to the chosen area normal. -/
abbrev SignedMagneticFluxQuantity : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- Signed magnetic-flux change rate. -/
abbrev SignedMagneticFluxRateQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Signed electromotive force relative to the positive loop orientation. -/
abbrev SignedEmfQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- A nonnegative electric-current magnitude. -/
abbrev CurrentMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- Read a length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read elapsed time in coherent-SI seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read area in coherent-SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read signed area-change rate in square metres per second. -/
def areaRateInSquareMetersPerSecond
    (rate : SignedAreaRateQuantity) : ℝ :=
  (rate UnitChoices.SI).val

/-- Read magnetic-flux-density magnitude in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read signed magnetic flux in coherent-SI webers. -/
def magneticFluxInWebers (flux : SignedMagneticFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-- Read signed magnetic-flux rate in coherent-SI webers per second. -/
def magneticFluxRateInWebersPerSecond
    (rate : SignedMagneticFluxRateQuantity) : ℝ :=
  (rate UnitChoices.SI).val

/-- Read signed electromotive force in coherent-SI volts. -/
def signedEmfInVolts (emf : SignedEmfQuantity) : ℝ :=
  (emf UnitChoices.SI).val

/-- Read current magnitude in coherent-SI amperes. -/
def currentMagnitudeInAmperes
    (current : CurrentMagnitudeQuantity) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-! ## Directions, loop orientation, and figure vocabulary -/

/-- A dimensionless direction vector in physical three-space. -/
abbrev DirectionVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Unit direction pointing right in the plane of the diagram. -/
def rightwardUnitVector : DirectionVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Unit direction pointing upward in the plane of the diagram. -/
def upwardUnitVector : DirectionVector :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- Unit direction pointing into the page. -/
def intoPageUnitVector : DirectionVector :=
  -EuclideanSpace.single (2 : Fin 3) 1

/-!
The ordinary right-handed cross product on Euclidean three-vectors.  This
wrapper transports Mathlib's `crossProduct` through the `EuclideanSpace`
representation used by Physlib.
-/
def euclideanCrossProduct
    (first second : DirectionVector) : DirectionVector :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (crossProduct
      (WithLp.equiv 2 (Fin 3 → ℝ) first)
      (WithLp.equiv 2 (Fin 3 → ℝ) second))

/-- The two orientations around the rectangular conducting loop. -/
inductive LoopDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Fintype, Repr

/-- Direction along the moving right-hand rod for each loop orientation. -/
def slidewireDirectionVector : LoopDirection → DirectionVector
  | .clockwise => -upwardUnitVector
  | .counterclockwise => upwardUnitVector

/-- The two horizontal rails, distinguished by vertical placement. -/
inductive Rail where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Planar and normal directions used to transcribe the raster. -/
inductive DiagramDirection where
  | leftward
  | rightward
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Fintype, Repr

/-- Physical and graphical objects visible in `918.png`. -/
inductive FigureObject where
  | upperRail
  | lowerRail
  | fixedLeftConnector
  | movingSlidewire
  | dashedLaterSlidewire
  | magneticFieldCrosses
  | velocityArrow
  | displacementGuide
  | lengthGuide
  | areaVectorMarker
  | emfArrow
  | currentArrows
  deriving DecidableEq, Fintype, Repr

/-- Symbolic labels printed in `918.png`. -/
inductive FigureLabel where
  | magneticFieldB
  | velocityV
  | displacementVDt
  | slidewireLengthL
  | areaVectorA
  | electromotiveForceE
  | currentI
  deriving DecidableEq, Fintype, Repr

/-- Glyph used for a vector normal to the page. -/
inductive NormalVectorGlyph where
  | cross
  | dot
  deriving DecidableEq, Repr

/-!
Typed presentation data from the primary raster.  The emf and current arrows
are recorded as visible, but their answer-bearing directions are deliberately
not stored here; those directions remain conclusions of the governing laws.
-/
structure SlidewireGeneratorFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  railIsHorizontal : Rail → Bool
  slidewireIsVertical : Bool
  slidewireBridgesRails : Bool
  fixedConnectorJoinsRailsAtLeft : Bool
  dashedSlidewireIsRightOfSolidSlidewire : Bool
  magneticFieldGlyph : NormalVectorGlyph
  areaVectorGlyph : NormalVectorGlyph
  velocityArrowDirection : DiagramDirection
  areaVectorDirection : DiagramDirection
  lengthGuideDirection : DiagramDirection
  lengthGuideSpansRailSeparation : Bool
  displacementGuideJoinsRodPositions : Bool

/-! ## Independent physical setup -/

/-- Material idealization of the rails and slidewire. -/
inductive ConductorModel where
  | idealConductingRailsAndSlidewire
  | other
  deriving DecidableEq, Repr

/-- Geometric idealization of the moving bar and rails. -/
inductive SlidewireGeometryModel where
  | straightRodOnParallelRails
  | other
  deriving DecidableEq, Repr

/-!
The apparatus and its independent observables.  The emf, flux rate, area rate,
and directions are not defined from `B`, `L`, `v`, or any answer choice.
-/
structure SlidewireGeneratorSetup where
  conductorModel : ConductorModel
  geometryModel : SlidewireGeometryModel
  magneticField : Electromagnetism.MagneticField 3
  magneticFluxDensity : MagneticFluxDensityQuantity
  slidewireLength : LengthQuantity
  slidewireSpeed : SpeedQuantity
  observationTime : Time
  displacementOver : TimeQuantity → LengthQuantity
  enclosedAreaAt : Time → AreaQuantity
  areaGrowthRateAt : Time → SignedAreaRateQuantity
  magneticFluxAt : Time → SignedMagneticFluxQuantity
  magneticFluxChangeRateAt : Time → SignedMagneticFluxRateQuantity
  inducedEmfAt : Time → SignedEmfQuantity
  inducedCurrentMagnitudeAt : Time → CurrentMagnitudeQuantity
  velocityDirectionVector : DirectionVector
  magneticFieldDirectionVector : DirectionVector
  positiveAreaNormalVector : DirectionVector
  positiveBoundaryOrientation : LoopDirection
  inducedEmfDirectionAt : Time → DirectionVector
  inducedEmfLoopDirectionAt : Time → LoopDirection
  inducedCurrentLoopDirectionAt : Time → LoopDirection
  figure : SlidewireGeneratorFigure

/-! ## Scenario, figure evidence, and governing laws -/

/-- Prose-level apparatus data, excluding the requested emf result. -/
structure MatchesSlidewireGeneratorScenario
    (setup : SlidewireGeneratorSetup) : Prop where
  idealConductor :
    setup.conductorModel = .idealConductingRailsAndSlidewire
  straightRodOnParallelRails :
    setup.geometryModel = .straightRodOnParallelRails
  rodMovesRight :
    setup.velocityDirectionVector = rightwardUnitVector
  areaNormalPointsIntoPage :
    setup.positiveAreaNormalVector = intoPageUnitVector
  positiveBoundaryIsClockwise :
    setup.positiveBoundaryOrientation = .clockwise

/-! Literal geometry and non-answer annotations visible in `918.png`. -/
structure MatchesSuppliedSlidewireFigure
    (setup : SlidewireGeneratorSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  railsAreHorizontal : ∀ rail, setup.figure.railIsHorizontal rail = true
  rodIsVertical : setup.figure.slidewireIsVertical = true
  rodBridgesRails : setup.figure.slidewireBridgesRails = true
  uConnectorIsAtLeft :
    setup.figure.fixedConnectorJoinsRailsAtLeft = true
  laterRodPositionIsToRight :
    setup.figure.dashedSlidewireIsRightOfSolidSlidewire = true
  fieldUsesCrosses : setup.figure.magneticFieldGlyph = .cross
  areaVectorUsesCross : setup.figure.areaVectorGlyph = .cross
  velocityArrowPointsRight :
    setup.figure.velocityArrowDirection = .rightward
  areaVectorPointsIntoPage :
    setup.figure.areaVectorDirection = .intoPage
  lengthGuideIsVertical :
    setup.figure.lengthGuideDirection = .upward
  lengthGuideSpansRails :
    setup.figure.lengthGuideSpansRailSeparation = true
  displacementGuideSpansPositions :
    setup.figure.displacementGuideJoinsRodPositions = true

/-- Positivity and nondegeneracy of the physical parameters in `B L v`. -/
structure HasPhysicalSlidewireParameters
    (setup : SlidewireGeneratorSetup) : Prop where
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensity
  rodLengthPositive :
    0 < lengthInMeters setup.slidewireLength
  rodSpeedPositive :
    0 < speedInMetersPerSecond setup.slidewireSpeed

/-!
The full Physlib magnetic field is spatially and temporally uniform, directed
into the page, and has the given magnetic-flux-density readout.
-/
structure ModelsUniformIntoPageMagneticField
    (setup : SlidewireGeneratorSetup) : Prop where
  directionVector :
    setup.magneticFieldDirectionVector = intoPageUnitVector
  uniformFieldReadout : ∀ time position,
    setup.magneticField time position =
      magneticFluxDensityInTeslas setup.magneticFluxDensity •
        intoPageUnitVector

/-!
Constant-speed kinematics: the displacement label means `v dt`, and the
rectangular loop area grows at rate `L v`.  Neither statement mentions flux
or emf.
-/
structure SatisfiesSlidewireKinematics
    (setup : SlidewireGeneratorSetup) : Prop where
  displacementLaw : ∀ duration : TimeQuantity,
    lengthInMeters (setup.displacementOver duration) =
      speedInMetersPerSecond setup.slidewireSpeed *
        timeInSeconds duration
  rectangularAreaGrowthLaw : ∀ time : Time,
    areaRateInSquareMetersPerSecond (setup.areaGrowthRateAt time) =
      lengthInMeters setup.slidewireLength *
        speedInMetersPerSecond setup.slidewireSpeed

/-!
For a uniform field parallel to the chosen area normal, flux is `B A` and its
rate is `B dA/dt`.  The law does not mention emf or substitute the slidewire
kinematics into the flux rate.
-/
structure SatisfiesUniformMagneticFluxLaw
    (setup : SlidewireGeneratorSetup) : Prop where
  fluxFromArea : ∀ time : Time,
    magneticFluxInWebers (setup.magneticFluxAt time) =
      magneticFluxDensityInTeslas setup.magneticFluxDensity *
        areaInSquareMeters (setup.enclosedAreaAt time)
  fluxRateFromAreaRate : ∀ time : Time,
    magneticFluxRateInWebersPerSecond
        (setup.magneticFluxChangeRateAt time) =
      magneticFluxDensityInTeslas setup.magneticFluxDensity *
        areaRateInSquareMetersPerSecond (setup.areaGrowthRateAt time)

/-!
Faraday's law relative to the selected positive area normal and boundary
orientation.  It contains neither the rod length nor its speed.
-/
structure SatisfiesFaradayInductionLaw
    (setup : SlidewireGeneratorSetup) : Prop where
  faradayLaw : ∀ time : Time,
    signedEmfInVolts (setup.inducedEmfAt time) =
      -magneticFluxRateInWebersPerSecond
        (setup.magneticFluxChangeRateAt time)

/-!
The magnetic Lorentz-force direction is `v × B`.  Loop geometry states how
each possible orientation traverses the rod, but does not select an answer.
-/
structure SatisfiesMotionalEmfDirectionLaw
    (setup : SlidewireGeneratorSetup) : Prop where
  lorentzCrossProductDirection : ∀ time : Time,
    setup.inducedEmfDirectionAt time =
      euclideanCrossProduct setup.velocityDirectionVector
        setup.magneticFieldDirectionVector
  loopGeometryConsistency : ∀ time : Time,
    setup.inducedEmfDirectionAt time =
      slidewireDirectionVector (setup.inducedEmfLoopDirectionAt time)

/-!
A passive conducting loop carries conventional current in the same loop
orientation as its induced emf.  Its magnitude remains unspecified because
the resistance is not supplied.
-/
structure SatisfiesPassiveConductorResponse
    (setup : SlidewireGeneratorSetup) : Prop where
  currentFollowsEmf : ∀ time : Time,
    setup.inducedCurrentLoopDirectionAt time =
      setup.inducedEmfLoopDirectionAt time

/-! ## Displayed choices and requested conclusion -/

/-- The four answer labels printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The signed-emf expression, in volts, printed for each answer choice. -/
def AnswerChoice.displayedSignedEmfInVolts
    (choice : AnswerChoice) (setup : SlidewireGeneratorSetup) : ℝ :=
  let B := magneticFluxDensityInTeslas setup.magneticFluxDensity
  let L := lengthInMeters setup.slidewireLength
  let v := speedInMetersPerSecond setup.slidewireSpeed
  match choice with
  | .A => B * L * v
  | .B => B * v / L
  | .C => -(B * L * v)
  | .D => L / (B * v)

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The signed induced emf is `-B L v`; its magnitude is `B L v`.  On the moving
rod the emf points upward, hence it traverses the loop counterclockwise, and
the conventional current has the same loop orientation.

This declaration formalizes `thm:physics:phyx_mini_0918:target`.  The combined
answer occurs only in this conclusion, not in any premise structure.
-/
theorem problem_phyx_mini_0918
    (setup : SlidewireGeneratorSetup)
    (hScenario : MatchesSlidewireGeneratorScenario setup)
    (hFigure : MatchesSuppliedSlidewireFigure setup)
    (hPhysical : HasPhysicalSlidewireParameters setup)
    (hUniformField : ModelsUniformIntoPageMagneticField setup)
    (hKinematics : SatisfiesSlidewireKinematics setup)
    (hFlux : SatisfiesUniformMagneticFluxLaw setup)
    (hFaraday : SatisfiesFaradayInductionLaw setup)
    (hDirection : SatisfiesMotionalEmfDirectionLaw setup)
    (hCurrent : SatisfiesPassiveConductorResponse setup) :
    signedEmfInVolts (setup.inducedEmfAt setup.observationTime) =
        -(magneticFluxDensityInTeslas setup.magneticFluxDensity *
          lengthInMeters setup.slidewireLength *
          speedInMetersPerSecond setup.slidewireSpeed) ∧
      |signedEmfInVolts (setup.inducedEmfAt setup.observationTime)| =
        magneticFluxDensityInTeslas setup.magneticFluxDensity *
          lengthInMeters setup.slidewireLength *
          speedInMetersPerSecond setup.slidewireSpeed ∧
      setup.inducedEmfDirectionAt setup.observationTime =
        upwardUnitVector ∧
      setup.inducedEmfLoopDirectionAt setup.observationTime =
        .counterclockwise ∧
      setup.inducedCurrentLoopDirectionAt setup.observationTime =
        .counterclockwise ∧
      signedEmfInVolts (setup.inducedEmfAt setup.observationTime) =
        recordedDatasetAnswer.displayedSignedEmfInVolts setup := by
  have hSigned :
      signedEmfInVolts (setup.inducedEmfAt setup.observationTime) =
        -(magneticFluxDensityInTeslas setup.magneticFluxDensity *
          lengthInMeters setup.slidewireLength *
          speedInMetersPerSecond setup.slidewireSpeed) := by
    rw [hFaraday.faradayLaw, hFlux.fluxRateFromAreaRate,
      hKinematics.rectangularAreaGrowthLaw]
    ring
  have hProductPositive :
      0 < magneticFluxDensityInTeslas setup.magneticFluxDensity *
        lengthInMeters setup.slidewireLength *
        speedInMetersPerSecond setup.slidewireSpeed :=
    mul_pos (mul_pos hPhysical.fieldMagnitudePositive
      hPhysical.rodLengthPositive) hPhysical.rodSpeedPositive
  have hMagnitude :
      |signedEmfInVolts (setup.inducedEmfAt setup.observationTime)| =
        magneticFluxDensityInTeslas setup.magneticFluxDensity *
          lengthInMeters setup.slidewireLength *
          speedInMetersPerSecond setup.slidewireSpeed := by
    rw [hSigned, abs_neg, abs_of_pos hProductPositive]
  have hEmfDirection :
      setup.inducedEmfDirectionAt setup.observationTime =
        upwardUnitVector := by
    rw [hDirection.lorentzCrossProductDirection,
      hScenario.rodMovesRight, hUniformField.directionVector]
    simp [euclideanCrossProduct, rightwardUnitVector,
      intoPageUnitVector, upwardUnitVector, crossProduct]
    ext i
    fin_cases i <;> norm_num [PiLp.single_apply]
  have hLoopDirection :
      setup.inducedEmfLoopDirectionAt setup.observationTime =
        .counterclockwise := by
    have hGeometry :=
      hDirection.loopGeometryConsistency setup.observationTime
    rw [hEmfDirection] at hGeometry
    cases hLoop :
        setup.inducedEmfLoopDirectionAt setup.observationTime with
    | clockwise =>
        rw [hLoop] at hGeometry
        have hImpossible := congrArg
          (fun vector : DirectionVector => vector (1 : Fin 3)) hGeometry
        norm_num [slidewireDirectionVector, upwardUnitVector,
          PiLp.single_apply] at hImpossible
    | counterclockwise => rfl
  have hCurrentDirection :
      setup.inducedCurrentLoopDirectionAt setup.observationTime =
        .counterclockwise := by
    rw [hCurrent.currentFollowsEmf, hLoopDirection]
  have hDataset :
      signedEmfInVolts (setup.inducedEmfAt setup.observationTime) =
        recordedDatasetAnswer.displayedSignedEmfInVolts setup := by
    rw [hSigned]
    rfl
  exact ⟨hSigned, hMagnitude, hEmfDirection, hLoopDirection,
    hCurrentDirection, hDataset⟩

end PhyXMiniProblems.ProblemPhyXMini0918
