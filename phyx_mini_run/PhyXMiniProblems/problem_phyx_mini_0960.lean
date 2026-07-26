import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0960

open Dimension

/-!
# Magnetic field of two opposed short wire segments

Two parallel horizontal wires are `5.00 cm` apart.  The highlighted
`1.50 mm` segment of the upper wire carries `12.0 A` to the right, while the
opposite segment of the lower wire carries `24.0 A` to the left.  The point
`P` is midway between the wires and `8.00 cm` from either segment.  The
right-hand rule therefore makes both short-segment Biot--Savart contributions
point into the page.

Lengths, current magnitudes, permeability, and the magnitude of the resulting
magnetic flux density are unit-independent Physlib `Dimensionful` quantities.
The magnetic fields themselves use Physlib's spacetime-dependent vector-field
type; their explicitly named values at `P` are coherent-SI vector readouts.

Assumption/target split:

* governing laws: steady-current time independence, standard vacuum
  permeability, the vector short-segment Biot--Savart law, magnetic-field
  superposition, and the norm relation between the total vector and magnitude;
* previous-part results: none;
* figure/data readouts: `5.00 cm` wire separation, both `1.50 mm` highlighted
  segments, both `8.00 cm` dashed distances, the `12.0 A` rightward upper
  current, the `24.0 A` leftward lower current, and point `P` between the
  parallel wires;
* current target conclusions: the exact total field and its magnitude, its
  into-page direction, rounding to `2.64 * 10^-7 T`, and unique selection of
  answer B.

No premise stores the target total-field value, direction, or answer choice.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic permeability has physical dimension `M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density (tesla) has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Read a length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a length in centimetres, as used by the separation and distance labels. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a length in millimetres, as used by the highlighted-segment labels. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  1000 * lengthInMeters length

/-- Read an electric-current magnitude in coherent-SI amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Read permeability in coherent-SI tesla-metres per ampere. -/
def permeabilityInTeslaMetersPerAmpere
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  ((permeability UnitChoices.SI).val : ℝ)

/-- Read a magnetic-flux-density magnitude in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  ((fieldMagnitude UnitChoices.SI).val : ℝ)

/-! ## Three-dimensional geometry and primary-figure vocabulary -/

/-- Coherent-SI three-dimensional vectors used at readout boundaries. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- Mathlib's ordinary right-handed cross product, transported to `SpatialVector`. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- Positive coordinate unit vectors for the diagram plane and page normal. -/
def xHat : SpatialVector :=
  EuclideanSpace.single (0 : Fin 3) 1

def yHat : SpatialVector :=
  EuclideanSpace.single (1 : Fin 3) 1

def zHat : SpatialVector :=
  EuclideanSpace.single (2 : Fin 3) 1

/-- The upper and lower wires distinguished in the primary raster. -/
inductive Wire where
  | top
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- Direction of a current arrow along a horizontal wire. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Dimensionless vector represented by a horizontal arrow direction. -/
def horizontalDirectionVector : HorizontalDirection → SpatialVector
  | .leftward => -xHat
  | .rightward => xHat

/-- The two orientations normal to the plane of the page. -/
inductive PageNormalDirection where
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Unit vector represented by a page-normal direction. -/
def pageNormalVector : PageNormalDirection → SpatialVector
  | .intoPage => -zHat
  | .outOfPage => zHat

/-- A nonzero vector points in a page-normal direction when it is a positive
multiple of the corresponding oriented unit vector. -/
def PointsInPageNormalDirection
    (vector : SpatialVector) (direction : PageNormalDirection) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧
    vector = magnitude • pageNormalVector direction

/-- Whether the current is time independent. -/
inductive CurrentRegime where
  | steady
  | timeDependent
  deriving DecidableEq, Repr

/-- Colours used for highlighted segments and current arrows in the raster. -/
inductive FigureColor where
  | red
  | purple
  | other
  deriving DecidableEq, Repr

/-!
Literal labels and qualitative evidence in the supplied image `960.png`.
Displayed scalar labels remain separate from the physical quantities they
calibrate.
-/
structure OpposedWireSegmentsFigure where
  wireShown : Wire → Bool
  wireDrawnHorizontal : Wire → Bool
  highlightedSegmentShown : Wire → Bool
  highlightedSegmentColor : Wire → FigureColor
  displayedSegmentLengthInMillimeters : Wire → ℝ
  currentArrowShown : Wire → Bool
  currentArrowColor : Wire → FigureColor
  currentArrowDirection : Wire → HorizontalDirection
  displayedCurrentInAmperes : Wire → ℝ
  pointPShown : Bool
  dashedDistanceLineShown : Wire → Bool
  displayedDistanceInCentimeters : Wire → ℝ
  pointDrawnBetweenWires : Bool

/-! ## Independent physical setup -/

/-!
Independent physical quantities, geometry, and magnetic observables.  Neither
the segment fields nor the total field is defined from the recorded answer.
-/
structure OpposedWireSegmentsSetup where
  unitSystem : UnitChoices
  wireSeparation : LengthQuantity
  segmentLength : Wire → LengthQuantity
  distanceFromSegmentToP : Wire → LengthQuantity
  currentMagnitude : Wire → ElectricCurrentMagnitude
  currentRegime : Wire → CurrentRegime
  segmentMidpoint : Wire → Space 3
  pointP : Space 3
  currentUnitDirection : Wire → SpatialVector
  radialUnitDirectionToP : Wire → SpatialVector
  electromagneticSystem : Electromagnetism.EMSystem
  vacuumPermeability : MagneticPermeabilityQuantity
  magneticFieldDueToSegment : Wire → Electromagnetism.MagneticField 3
  totalMagneticField : Electromagnetism.MagneticField 3
  totalMagneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  observationTime : Time
  figure : OpposedWireSegmentsFigure

/-- Coherent-SI magnetic-field vector at `P` due to one highlighted segment. -/
def segmentFieldVectorAtPInTeslas
    (setup : OpposedWireSegmentsSetup) (wire : Wire) : SpatialVector :=
  setup.magneticFieldDueToSegment wire setup.observationTime setup.pointP

/-- Coherent-SI total magnetic-field vector at `P`. -/
def totalFieldVectorAtPInTeslas
    (setup : OpposedWireSegmentsSetup) : SpatialVector :=
  setup.totalMagneticField setup.observationTime setup.pointP

/-! ## Written data, figure evidence, and geometry -/

/-- Numerical and qualitative information stated in the problem text. -/
structure MatchesWrittenTwoWireScenario
    (setup : OpposedWireSegmentsSetup) : Prop where
  usesSIReferenceUnits : setup.unitSystem = UnitChoices.SI
  wireSeparationIsFiveCentimeters :
    lengthInCentimeters setup.wireSeparation = 5
  bothSegmentsAreOnePointFiveMillimeters : ∀ wire,
    lengthInMillimeters (setup.segmentLength wire) = 3 / 2
  bothDistancesAreEightCentimeters : ∀ wire,
    lengthInCentimeters (setup.distanceFromSegmentToP wire) = 8
  bothCurrentsAreSteady : ∀ wire,
    setup.currentRegime wire = .steady
  currentsRunInOppositeParallelDirections :
    setup.currentUnitDirection .top = -setup.currentUnitDirection .bottom

/-!
Transcription of the primary raster and calibration of its printed labels.
This premise records no magnetic-field value or field direction.
-/
structure MatchesPrimaryOpposedWireFigure
    (setup : OpposedWireSegmentsSetup) : Prop where
  bothWiresShown : ∀ wire, setup.figure.wireShown wire = true
  bothWiresHorizontal : ∀ wire, setup.figure.wireDrawnHorizontal wire = true
  bothHighlightedSegmentsShown : ∀ wire,
    setup.figure.highlightedSegmentShown wire = true
  highlightedSegmentsAreRed : ∀ wire,
    setup.figure.highlightedSegmentColor wire = .red
  bothSegmentLabelsReadOnePointFive : ∀ wire,
    setup.figure.displayedSegmentLengthInMillimeters wire = 3 / 2
  segmentLabelsCalibratePhysicalLengths : ∀ wire,
    setup.figure.displayedSegmentLengthInMillimeters wire =
      lengthInMillimeters (setup.segmentLength wire)
  bothCurrentArrowsShown : ∀ wire,
    setup.figure.currentArrowShown wire = true
  bothCurrentArrowsArePurple : ∀ wire,
    setup.figure.currentArrowColor wire = .purple
  topCurrentArrowPointsRight :
    setup.figure.currentArrowDirection .top = .rightward
  bottomCurrentArrowPointsLeft :
    setup.figure.currentArrowDirection .bottom = .leftward
  topCurrentLabelReadsTwelve :
    setup.figure.displayedCurrentInAmperes .top = 12
  bottomCurrentLabelReadsTwentyFour :
    setup.figure.displayedCurrentInAmperes .bottom = 24
  currentLabelsCalibratePhysicalCurrents : ∀ wire,
    setup.figure.displayedCurrentInAmperes wire =
      currentInAmperes (setup.currentMagnitude wire)
  currentArrowsCalibratePhysicalDirections : ∀ wire,
    setup.currentUnitDirection wire =
      horizontalDirectionVector (setup.figure.currentArrowDirection wire)
  pointMarkerPShown : setup.figure.pointPShown = true
  bothDashedDistanceLinesShown : ∀ wire,
    setup.figure.dashedDistanceLineShown wire = true
  bothDistanceLabelsReadEight : ∀ wire,
    setup.figure.displayedDistanceInCentimeters wire = 8
  distanceLabelsCalibratePhysicalDistances : ∀ wire,
    setup.figure.displayedDistanceInCentimeters wire =
      lengthInCentimeters (setup.distanceFromSegmentToP wire)
  pointPIsDrawnBetweenWires : setup.figure.pointDrawnBetweenWires = true

/-!
Cartesian realization of the pictured geometry.  The two segment centres are
vertically separated, while `P` is to their right on the midline.  The signed
vertical components `±(separation/2)/distance` retain exactly the sine factor
needed by the Biot--Savart cross product without asserting any field result.
-/
structure MatchesOpposedWireGeometry
    (setup : OpposedWireSegmentsSetup) : Prop where
  topCurrentPointsAlongPositiveX : setup.currentUnitDirection .top = xHat
  bottomCurrentPointsAlongNegativeX : setup.currentUnitDirection .bottom = -xHat
  segmentCentersHaveStatedVerticalSeparation :
    setup.segmentMidpoint .top =
      (lengthInMeters setup.wireSeparation • yHat) +ᵥ
        setup.segmentMidpoint .bottom
  pointPositionFromEachSegment : ∀ wire,
    setup.pointP =
      (lengthInMeters (setup.distanceFromSegmentToP wire) •
          setup.radialUnitDirectionToP wire) +ᵥ
        setup.segmentMidpoint wire
  radialDirectionsAreUnit : ∀ wire,
    ‖setup.radialUnitDirectionToP wire‖ = 1
  pointIsToTheRightOfBothSegments : ∀ wire,
    0 < inner ℝ (setup.radialUnitDirectionToP wire) xHat
  radialDirectionsLieInPage : ∀ wire,
    inner ℝ (setup.radialUnitDirectionToP wire) zHat = 0
  topRadialVerticalComponent :
    inner ℝ (setup.radialUnitDirectionToP .top) yHat =
      -(lengthInMeters setup.wireSeparation /
        (2 * lengthInMeters (setup.distanceFromSegmentToP .top)))
  bottomRadialVerticalComponent :
    inner ℝ (setup.radialUnitDirectionToP .bottom) yHat =
      lengthInMeters setup.wireSeparation /
        (2 * lengthInMeters (setup.distanceFromSegmentToP .bottom))

/-- Positivity and normalization hypotheses selecting the physical branch. -/
structure HasPhysicalTwoWireParameters
    (setup : OpposedWireSegmentsSetup) : Prop where
  wireSeparationPositive : 0 < lengthInMeters setup.wireSeparation
  segmentLengthsPositive : ∀ wire,
    0 < lengthInMeters (setup.segmentLength wire)
  observationDistancesPositive : ∀ wire,
    0 < lengthInMeters (setup.distanceFromSegmentToP wire)
  currentMagnitudesPositive : ∀ wire,
    0 < currentInAmperes (setup.currentMagnitude wire)
  currentDirectionsAreUnit : ∀ wire,
    ‖setup.currentUnitDirection wire‖ = 1
  permeabilityPositive :
    0 < permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability

/-!
The dimensionful permeability agrees with the Physlib electromagnetic system
and has the standard coherent-SI vacuum value `4π * 10⁻⁷ T m/A`.
-/
structure UsesStandardVacuumPermeability
    (setup : OpposedWireSegmentsSetup) : Prop where
  agreesWithElectromagneticSystem :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      setup.electromagneticSystem.μ₀
  standardSIReadout :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      4 * Real.pi / 10 ^ 7

/-! ## Governing magnetic laws -/

/-- Steady currents produce time-independent segment and total fields here. -/
structure SatisfiesSteadyCurrentFieldModel
    (setup : OpposedWireSegmentsSetup) : Prop where
  segmentFieldsTimeIndependent : ∀ wire time position,
    setup.magneticFieldDueToSegment wire time position =
      setup.magneticFieldDueToSegment wire setup.observationTime position
  totalFieldTimeIndependent : ∀ time position,
    setup.totalMagneticField time position =
      setup.totalMagneticField setup.observationTime position

/-!
Short-current-element Biot--Savart law for either highlighted segment:

`B = μ₀ I Δℓ /(4πr²) (î_current × r̂)`.

This is a reusable governing relation in the independent stored quantities;
it contains no target numerical field or answer choice.
-/
structure SatisfiesShortSegmentBiotSavartLaw
    (setup : OpposedWireSegmentsSetup) : Prop where
  fieldAtP : ∀ wire,
    segmentFieldVectorAtPInTeslas setup wire =
      (permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability *
          currentInAmperes (setup.currentMagnitude wire) *
          lengthInMeters (setup.segmentLength wire) /
          (4 * Real.pi *
            lengthInMeters (setup.distanceFromSegmentToP wire) ^ 2)) •
        spatialCross (setup.currentUnitDirection wire)
          (setup.radialUnitDirectionToP wire)

/-- Magnetic fields from the two independent segments add vectorially at `P`. -/
structure SatisfiesMagneticFieldSuperposition
    (setup : OpposedWireSegmentsSetup) : Prop where
  totalAtPIsSum :
    totalFieldVectorAtPInTeslas setup =
      segmentFieldVectorAtPInTeslas setup .top +
        segmentFieldVectorAtPInTeslas setup .bottom

/-- The independent total-field magnitude is the norm of the total vector. -/
structure SatisfiesTotalFieldMagnitudeRelation
    (setup : OpposedWireSegmentsSetup) : Prop where
  magnitudeIsVectorNorm :
    magneticFluxDensityInTeslas setup.totalMagneticFluxDensityMagnitude =
      ‖totalFieldVectorAtPInTeslas setup‖

/-! ## Derived field and displayed-answer target -/

/-!
Under the short-segment model the two into-page contributions add to
`135 / 512000000 T`, i.e. `2.63671875 * 10⁻⁷ T`.
-/
lemma totalMagneticFieldAtP_exact
    (setup : OpposedWireSegmentsSetup)
    (hData : MatchesWrittenTwoWireScenario setup)
    (hFigure : MatchesPrimaryOpposedWireFigure setup)
    (hGeometry : MatchesOpposedWireGeometry setup)
    (hPhysical : HasPhysicalTwoWireParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hSteady : SatisfiesSteadyCurrentFieldModel setup)
    (hBiotSavart : SatisfiesShortSegmentBiotSavartLaw setup)
    (hSuperposition : SatisfiesMagneticFieldSuperposition setup) :
    totalFieldVectorAtPInTeslas setup =
      (135 / 512000000 : ℝ) • pageNormalVector .intoPage := by
  have hSeparation :
      lengthInMeters setup.wireSeparation = (1 / 20 : ℝ) := by
    have h := hData.wireSeparationIsFiveCentimeters
    unfold lengthInCentimeters at h
    linarith
  have hSegmentLength (wire : Wire) :
      lengthInMeters (setup.segmentLength wire) = (3 / 2000 : ℝ) := by
    have h := hData.bothSegmentsAreOnePointFiveMillimeters wire
    unfold lengthInMillimeters at h
    linarith
  have hDistance (wire : Wire) :
      lengthInMeters (setup.distanceFromSegmentToP wire) = (2 / 25 : ℝ) := by
    have h := hData.bothDistancesAreEightCentimeters wire
    unfold lengthInCentimeters at h
    linarith
  have hTopCurrent :
      currentInAmperes (setup.currentMagnitude .top) = 12 := by
    calc
      currentInAmperes (setup.currentMagnitude .top) =
          setup.figure.displayedCurrentInAmperes .top :=
        (hFigure.currentLabelsCalibratePhysicalCurrents .top).symm
      _ = 12 := hFigure.topCurrentLabelReadsTwelve
  have hBottomCurrent :
      currentInAmperes (setup.currentMagnitude .bottom) = 24 := by
    calc
      currentInAmperes (setup.currentMagnitude .bottom) =
          setup.figure.displayedCurrentInAmperes .bottom :=
        (hFigure.currentLabelsCalibratePhysicalCurrents .bottom).symm
      _ = 24 := hFigure.bottomCurrentLabelReadsTwentyFour
  have hTopRadialY :
      inner ℝ (setup.radialUnitDirectionToP .top) yHat =
        (-5 / 16 : ℝ) := by
    rw [hGeometry.topRadialVerticalComponent, hSeparation, hDistance]
    norm_num
  have hBottomRadialY :
      inner ℝ (setup.radialUnitDirectionToP .bottom) yHat =
        (5 / 16 : ℝ) := by
    rw [hGeometry.bottomRadialVerticalComponent, hSeparation, hDistance]
    norm_num
  have hTopRadialZ :
      inner ℝ (setup.radialUnitDirectionToP .top) zHat = 0 :=
    hGeometry.radialDirectionsLieInPage .top
  have hBottomRadialZ :
      inner ℝ (setup.radialUnitDirectionToP .bottom) zHat = 0 :=
    hGeometry.radialDirectionsLieInPage .bottom
  have hTopCross :
      spatialCross (setup.currentUnitDirection .top)
          (setup.radialUnitDirectionToP .top) =
        (-5 / 16 : ℝ) • zHat := by
    rw [hGeometry.topCurrentPointsAlongPositiveX]
    ext i
    fin_cases i <;>
      simp [spatialCross, xHat, yHat, zHat, crossProduct,
        EuclideanSpace.inner_single_right] at hTopRadialY hTopRadialZ ⊢
    · exact hTopRadialZ
    · exact hTopRadialY
  have hBottomCross :
      spatialCross (setup.currentUnitDirection .bottom)
          (setup.radialUnitDirectionToP .bottom) =
        (-5 / 16 : ℝ) • zHat := by
    rw [hGeometry.bottomCurrentPointsAlongNegativeX]
    ext i
    fin_cases i <;>
      simp [spatialCross, xHat, yHat, zHat, crossProduct,
        EuclideanSpace.inner_single_right] at hBottomRadialY hBottomRadialZ ⊢
    · exact hBottomRadialZ
    · linarith
  have hTopField :
      segmentFieldVectorAtPInTeslas setup .top =
        (45 / 512000000 : ℝ) • pageNormalVector .intoPage := by
    rw [hBiotSavart.fieldAtP, hVacuum.standardSIReadout, hTopCurrent,
      hSegmentLength, hDistance, hTopCross]
    simp only [pageNormalVector]
    rw [smul_smul, smul_neg, ← neg_smul]
    congr 1
    field_simp [Real.pi_ne_zero]
    ring
  have hBottomField :
      segmentFieldVectorAtPInTeslas setup .bottom =
        (90 / 512000000 : ℝ) • pageNormalVector .intoPage := by
    rw [hBiotSavart.fieldAtP, hVacuum.standardSIReadout, hBottomCurrent,
      hSegmentLength, hDistance, hBottomCross]
    simp only [pageNormalVector]
    rw [smul_smul, smul_neg, ← neg_smul]
    congr 1
    field_simp [Real.pi_ne_zero]
    ring
  rw [hSuperposition.totalAtPIsSum, hTopField, hBottomField, ← add_smul]
  congr 1
  norm_num

/-- Labels of the four magnetic-field-magnitude answers in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-field magnitude in teslas displayed beside each answer choice. -/
def displayedMagnitudeInTeslas : AnswerChoice → ℝ
  | .A => 352 / 10 ^ 9
  | .B => 264 / 10 ^ 9
  | .C => 132 / 10 ^ 9
  | .D => 264 / 10 ^ 10

/-- Dataset answer label retained as metadata, not as a correctness premise. -/
def recordedDatasetAnswer : AnswerChoice :=
  .B

/-- Rounding to the nearest nanotesla, the precision of `2.64 * 10⁻⁷ T`. -/
def RoundsToNearestNanotesla (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / (2 * 10 ^ 9)

/-- A displayed answer is strictly closer than every distinct alternative. -/
def IsUniqueClosestDisplayedMagnitude
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice, otherChoice ≠ choice →
    |actual - displayedMagnitudeInTeslas choice| <
      |actual - displayedMagnitudeInTeslas otherChoice|

/-!
Blueprint declaration `thm:physics:phyx_mini_0960:target`.

The total magnetic field at `P` has exact short-segment magnitude
`135 / 512000000 T`, points into the page, rounds to `2.64 * 10⁻⁷ T`, and
uniquely selects answer B.
-/
theorem problem_phyx_mini_0960
    (setup : OpposedWireSegmentsSetup)
    (hData : MatchesWrittenTwoWireScenario setup)
    (hFigure : MatchesPrimaryOpposedWireFigure setup)
    (hGeometry : MatchesOpposedWireGeometry setup)
    (hPhysical : HasPhysicalTwoWireParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hSteady : SatisfiesSteadyCurrentFieldModel setup)
    (hBiotSavart : SatisfiesShortSegmentBiotSavartLaw setup)
    (hSuperposition : SatisfiesMagneticFieldSuperposition setup)
    (hMagnitude : SatisfiesTotalFieldMagnitudeRelation setup) :
    totalFieldVectorAtPInTeslas setup =
        (135 / 512000000 : ℝ) • pageNormalVector .intoPage ∧
      magneticFluxDensityInTeslas setup.totalMagneticFluxDensityMagnitude =
        (135 / 512000000 : ℝ) ∧
      PointsInPageNormalDirection
        (totalFieldVectorAtPInTeslas setup) .intoPage ∧
      RoundsToNearestNanotesla
        (magneticFluxDensityInTeslas setup.totalMagneticFluxDensityMagnitude)
        (displayedMagnitudeInTeslas .B) ∧
      IsUniqueClosestDisplayedMagnitude
        (magneticFluxDensityInTeslas setup.totalMagneticFluxDensityMagnitude)
        .B := by
  have hField := totalMagneticFieldAtP_exact setup hData hFigure hGeometry
    hPhysical hVacuum hSteady hBiotSavart hSuperposition
  have hFieldMagnitude :
      magneticFluxDensityInTeslas setup.totalMagneticFluxDensityMagnitude =
        (135 / 512000000 : ℝ) := by
    rw [hMagnitude.magnitudeIsVectorNorm, hField, norm_smul]
    norm_num [pageNormalVector, zHat, EuclideanSpace.norm_single,
      Real.norm_eq_abs, abs_of_nonneg]
  refine ⟨hField, hFieldMagnitude, ?_, ?_, ?_⟩
  · refine ⟨(135 / 512000000 : ℝ), by norm_num, hField⟩
  · rw [hFieldMagnitude]
    norm_num [RoundsToNearestNanotesla, displayedMagnitudeInTeslas,
      abs_of_nonneg, abs_of_nonpos]
  · rw [hFieldMagnitude]
    intro otherChoice hOtherChoice
    fin_cases otherChoice <;>
      norm_num [IsUniqueClosestDisplayedMagnitude,
        displayedMagnitudeInTeslas, abs_of_nonneg, abs_of_nonpos] at *

end PhyXMiniProblems.ProblemPhyXMini0960
