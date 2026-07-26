import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0961

open Dimension

/-!
# Magnetic field of two short elements of a right-angle wire

A steady `28.0 A` current travels upward along the vertical leg of a wire and
then to the right along its horizontal leg.  The primary image marks one
`2.00 mm` current element on each leg, with the centers of both elements
`3.00 cm` from the bend.  Point `P` is the midpoint of the dashed segment
joining those two centers.

Physical lengths, current, permeability, and magnetic-flux-density magnitude
are unit-independent Physlib `Dimensionful` quantities.  Cartesian vectors
are explicitly coherent-SI readouts: positions and current-element vectors
are in metres, while magnetic-field vectors are in teslas.

Assumption/target split:

* governing laws: steady-current time independence, the short-element
  Biot--Savart vector law for each marked element, vector superposition, the
  norm law for field magnitude, and the standard SI vacuum permeability;
* previous-part results: none;
* figure/data readouts: a right-angle vertical/horizontal wire, upward then
  rightward current, `28.0 A`, two `2.00 mm` elements, both centers `3.00 cm`
  from the bend, and `P` midway between the centers;
* current target conclusions: the exact total magnitude
  `14 * sqrt 2 / 1125000 T`, its rounding to `1.76 * 10^-5 T`, and unique
  selection of answer choice B.

No target field value or answer choice is stored in the setup, figure, or
governing-law premises.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Electric current has dimension charge per unit time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Magnetic permeability has dimension `M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density (tesla) has dimension `M T⁻¹ C⁻¹`. -/
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

/-- Read a nonnegative physical quantity in coherent SI units. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  coherentSIReadout length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical length in millimetres. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  1000 * lengthInMeters length

/-- Read a physical current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  coherentSIReadout current

/-- Read magnetic permeability in tesla-metres per ampere. -/
def permeabilityInTeslaMetersPerAmpere
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  coherentSIReadout permeability

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityMagnitude) : ℝ :=
  coherentSIReadout density

/-! ## Cartesian geometry and primary-figure vocabulary -/

/-- Three-dimensional coherent-SI spatial vectors. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Mathlib's right-handed cross product transported to `SpatialVector`. -/
def spatialCrossProduct (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- Coordinate axes used to orient the two wire legs and the page normal. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Positive unit vector associated with a Cartesian axis. -/
def axisVector : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single (0 : Fin 3) 1
  | .y => EuclideanSpace.single (1 : Fin 3) 1
  | .z => EuclideanSpace.single (2 : Fin 3) 1

/-- The two perpendicular legs of the bent wire. -/
inductive WireLeg where
  | vertical
  | horizontal
  deriving DecidableEq, Fintype, Repr

/-- The marked short current element on each leg. -/
inductive MarkedElement where
  | vertical
  | horizontal
  deriving DecidableEq, Fintype, Repr

/-- The leg containing a marked current element. -/
def MarkedElement.leg : MarkedElement → WireLeg
  | .vertical => .vertical
  | .horizontal => .horizontal

/-- Qualitative directions used by the current arrow and wire legs. -/
inductive AxisDirection where
  | upward
  | rightward
  deriving DecidableEq, Repr

/-- Unit vector represented by a qualitative direction. -/
def directionVector : AxisDirection → SpatialVector
  | .upward => axisVector .y
  | .rightward => axisVector .x

/-- A time-independent or time-varying current regime. -/
inductive CurrentRegime where
  | steady
  | timeVarying
  deriving DecidableEq, Repr

/-!
Literal graphical readouts from the primary image `961.png`.  The scalar
labels remain distinct from the dimensionful quantities they calibrate.
-/
structure RightAngleWireFigure where
  bendShown : Bool
  rightAngleBendShown : Bool
  wireLegShown : WireLeg → Bool
  markedElementShown : MarkedElement → Bool
  displayedElementLengthInMillimeters : MarkedElement → ℝ
  displayedBendDistanceInCentimeters : MarkedElement → ℝ
  currentArrowShown : Bool
  currentArrowDirection : AxisDirection
  displayedCurrentInAmperes : ℝ
  pointPShown : Bool
  dashedElementJoinShown : Bool

/-!
Independent physical quantities and observables for the bent wire.  The
requested magnetic-field magnitude is an observable, not a definition from
an answer choice or target numeral.
-/
structure RightAngleWireSetup where
  unitSystem : UnitChoices
  currentRegime : CurrentRegime
  currentMagnitude : ElectricCurrentMagnitude
  elementLength : MarkedElement → LengthQuantity
  elementCenterDistanceFromBend : MarkedElement → LengthQuantity
  bendPositionInMeters : Space 3
  elementCenterPositionInMeters : MarkedElement → Space 3
  pointPPositionInMeters : Space 3
  currentElementVectorInMeters : MarkedElement → SpatialVector
  electromagneticSystem : Electromagnetism.EMSystem
  vacuumPermeability : MagneticPermeabilityQuantity
  magneticFieldDueToElement : MarkedElement → Electromagnetism.MagneticField 3
  totalMagneticField : Electromagnetism.MagneticField 3
  producedFieldMagnitudeAtP : MagneticFluxDensityMagnitude
  observationTime : Time
  figure : RightAngleWireFigure

/-- Displacement from a marked element's center to `P`, in metres. -/
def displacementToPInMeters
    (setup : RightAngleWireSetup) (element : MarkedElement) : SpatialVector :=
  WithLp.toLp 2
    (setup.pointPPositionInMeters - setup.elementCenterPositionInMeters element)

/-- Magnetic-field vector at `P` due to one marked element, in teslas. -/
def elementFieldVectorAtPInTeslas
    (setup : RightAngleWireSetup) (element : MarkedElement) : SpatialVector :=
  setup.magneticFieldDueToElement element setup.observationTime
    setup.pointPPositionInMeters

/-- Total magnetic-field vector at `P`, in teslas. -/
def totalFieldVectorAtPInTeslas
    (setup : RightAngleWireSetup) : SpatialVector :=
  setup.totalMagneticField setup.observationTime setup.pointPPositionInMeters

/-- Physical magnitude of the total field at `P`, read in teslas. -/
def totalFieldMagnitudeAtPInTeslas
    (setup : RightAngleWireSetup) : ℝ :=
  magneticFluxDensityInTeslas setup.producedFieldMagnitudeAtP

/-! ## Problem data and primary-image geometry -/

/-- Numerical problem data, separated from the requested field value. -/
structure MatchesRightAngleWireProblemData
    (setup : RightAngleWireSetup) : Prop where
  usesSIUnits : setup.unitSystem = UnitChoices.SI
  currentIsSteady : setup.currentRegime = .steady
  currentMagnitudeIsTwentyEightAmperes :
    currentInAmperes setup.currentMagnitude = 28
  eachElementIsTwoMillimeters : ∀ element,
    lengthInMillimeters (setup.elementLength element) = 2
  eachElementIsTwoThousandthsMeter : ∀ element,
    lengthInMeters (setup.elementLength element) = 2 / 1000
  eachCenterIsThreeCentimetersFromBend : ∀ element,
    lengthInCentimeters (setup.elementCenterDistanceFromBend element) = 3
  eachCenterIsThreeHundredthsMeter : ∀ element,
    lengthInMeters (setup.elementCenterDistanceFromBend element) = 3 / 100

/-!
Primary-image transcription and coherent-SI coordinate geometry.  The
vertical element lies below the bend and carries current upward; after the
bend, the horizontal element carries the same current rightward.  `P` is
the affine midpoint of the two element centers.
-/
structure MatchesPrimaryRightAngleWireFigure
    (setup : RightAngleWireSetup) : Prop where
  bendIsShown : setup.figure.bendShown = true
  bendIsMarkedRightAngle : setup.figure.rightAngleBendShown = true
  bothLegsShown : ∀ leg, setup.figure.wireLegShown leg = true
  bothElementsShown : ∀ element, setup.figure.markedElementShown element = true
  bothElementLabelsReadTwoMillimeters : ∀ element,
    setup.figure.displayedElementLengthInMillimeters element = 2
  elementLabelsCalibratePhysicalLengths : ∀ element,
    setup.figure.displayedElementLengthInMillimeters element =
      lengthInMillimeters (setup.elementLength element)
  bothDistanceLabelsReadThreeCentimeters : ∀ element,
    setup.figure.displayedBendDistanceInCentimeters element = 3
  distanceLabelsCalibratePhysicalDistances : ∀ element,
    setup.figure.displayedBendDistanceInCentimeters element =
      lengthInCentimeters (setup.elementCenterDistanceFromBend element)
  currentArrowIsShown : setup.figure.currentArrowShown = true
  picturedCurrentArrowPointsUp : setup.figure.currentArrowDirection = .upward
  picturedCurrentLabelReadsTwentyEight :
    setup.figure.displayedCurrentInAmperes = 28
  currentLabelCalibratesPhysicalCurrent :
    setup.figure.displayedCurrentInAmperes =
      currentInAmperes setup.currentMagnitude
  pointPIsShown : setup.figure.pointPShown = true
  dashedElementJoinIsShown : setup.figure.dashedElementJoinShown = true
  bendPlacedAtOrigin : setup.bendPositionInMeters = 0
  verticalElementCenterPosition :
    setup.elementCenterPositionInMeters .vertical =
      ((-lengthInMeters (setup.elementCenterDistanceFromBend .vertical)) •
        axisVector .y).ofLp
  horizontalElementCenterPosition :
    setup.elementCenterPositionInMeters .horizontal =
      (lengthInMeters (setup.elementCenterDistanceFromBend .horizontal) •
        axisVector .x).ofLp
  pointPIsMidwayBetweenElements :
    setup.pointPPositionInMeters =
      (1 / 2 : ℝ) •
        (setup.elementCenterPositionInMeters .vertical +
          setup.elementCenterPositionInMeters .horizontal)
  verticalElementCarriesCurrentUpward :
    setup.currentElementVectorInMeters .vertical =
      lengthInMeters (setup.elementLength .vertical) • directionVector .upward
  horizontalElementCarriesCurrentRightward :
    setup.currentElementVectorInMeters .horizontal =
      lengthInMeters (setup.elementLength .horizontal) •
        directionVector .rightward

/-- Positivity conditions selecting the physical, nondegenerate branch. -/
structure HasPhysicalRightAngleWireParameters
    (setup : RightAngleWireSetup) : Prop where
  currentPositive : 0 < currentInAmperes setup.currentMagnitude
  elementLengthsPositive : ∀ element,
    0 < lengthInMeters (setup.elementLength element)
  centerDistancesPositive : ∀ element,
    0 < lengthInMeters (setup.elementCenterDistanceFromBend element)
  displacementsToPAreNonzero : ∀ element,
    displacementToPInMeters setup element ≠ 0
  permeabilityPositive :
    0 < permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability

/-!
The dimensionful permeability agrees with the Physlib electromagnetic system
and has the standard coherent-SI value `4π * 10⁻⁷ T m/A`.
-/
structure UsesStandardVacuumPermeability
    (setup : RightAngleWireSetup) : Prop where
  agreesWithElectromagneticSystem :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      setup.electromagneticSystem.μ₀
  standardSIReadout :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      4 * Real.pi / 10 ^ 7

/-! ## Governing magnetic-field laws -/

/-- A steady current produces time-independent element and total fields. -/
structure SatisfiesSteadyCurrentFieldModel
    (setup : RightAngleWireSetup) : Prop where
  elementFieldsTimeIndependent : ∀ element time position,
    setup.magneticFieldDueToElement element time position =
      setup.magneticFieldDueToElement element setup.observationTime position
  totalFieldTimeIndependent : ∀ time position,
    setup.totalMagneticField time position =
      setup.totalMagneticField setup.observationTime position

/-!
Short-current-element Biot--Savart law at `P` for both marked elements:

`B = (μ₀ I / (4π |r|³)) (dℓ × r)`.

This general vector relation retains the separation, angle factor, and
right-hand-rule direction.  It contains no requested numerical field value.
-/
structure SatisfiesShortElementBiotSavartLaw
    (setup : RightAngleWireSetup) : Prop where
  fieldAtP : ∀ element,
    elementFieldVectorAtPInTeslas setup element =
      (permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability *
          currentInAmperes setup.currentMagnitude /
          (4 * Real.pi * ‖displacementToPInMeters setup element‖ ^ 3)) •
        spatialCrossProduct (setup.currentElementVectorInMeters element)
          (displacementToPInMeters setup element)

/-- Magnetic fields produced by the two current elements superpose linearly. -/
structure SatisfiesTwoElementSuperposition
    (setup : RightAngleWireSetup) : Prop where
  totalAtPIsVectorSum :
    totalFieldVectorAtPInTeslas setup =
      elementFieldVectorAtPInTeslas setup .vertical +
        elementFieldVectorAtPInTeslas setup .horizontal

/-- The scalar physical readout is the Euclidean norm of the total field. -/
structure MagnitudeReadoutMatchesTotalField
    (setup : RightAngleWireSetup) : Prop where
  magnitudeAtP :
    totalFieldMagnitudeAtPInTeslas setup = ‖totalFieldVectorAtPInTeslas setup‖

/-! ## Derived exact magnitude and displayed-answer target -/

/-!
The two element fields have the same page-normal direction.  The exact
short-element model gives `14 * sqrt 2 / 1125000 T`; this is approximately
`1.75964 * 10⁻⁵ T`.
-/
lemma totalFieldMagnitudeAtP_exact
    (setup : RightAngleWireSetup)
    (hData : MatchesRightAngleWireProblemData setup)
    (hFigure : MatchesPrimaryRightAngleWireFigure setup)
    (hPhysical : HasPhysicalRightAngleWireParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hSteady : SatisfiesSteadyCurrentFieldModel setup)
    (hBiotSavart : SatisfiesShortElementBiotSavartLaw setup)
    (hSuperposition : SatisfiesTwoElementSuperposition setup)
    (hMagnitude : MagnitudeReadoutMatchesTotalField setup) :
    totalFieldMagnitudeAtPInTeslas setup =
      14 * Real.sqrt 2 / 1125000 := by
  have hDisplacementVertical :
      displacementToPInMeters setup .vertical =
        (3 / 200 : ℝ) • axisVector .x + (3 / 200 : ℝ) • axisVector .y := by
    ext i
    fin_cases i <;>
      norm_num [displacementToPInMeters,
        hFigure.pointPIsMidwayBetweenElements,
        hFigure.verticalElementCenterPosition,
        hFigure.horizontalElementCenterPosition,
        hData.eachCenterIsThreeHundredthsMeter, axisVector]
  have hDisplacementHorizontal :
      displacementToPInMeters setup .horizontal =
        (-3 / 200 : ℝ) • axisVector .x + (-3 / 200 : ℝ) • axisVector .y := by
    ext i
    fin_cases i <;>
      norm_num [displacementToPInMeters,
        hFigure.pointPIsMidwayBetweenElements,
        hFigure.verticalElementCenterPosition,
        hFigure.horizontalElementCenterPosition,
        hData.eachCenterIsThreeHundredthsMeter, axisVector]
  have hCurrentElementVertical :
      setup.currentElementVectorInMeters .vertical =
        (1 / 500 : ℝ) • axisVector .y := by
    rw [hFigure.verticalElementCarriesCurrentUpward,
      hData.eachElementIsTwoThousandthsMeter]
    norm_num [directionVector]
  have hCurrentElementHorizontal :
      setup.currentElementVectorInMeters .horizontal =
        (1 / 500 : ℝ) • axisVector .x := by
    rw [hFigure.horizontalElementCarriesCurrentRightward,
      hData.eachElementIsTwoThousandthsMeter]
    norm_num [directionVector]
  have hCrossVertical :
      spatialCrossProduct
          ((1 / 500 : ℝ) • axisVector .y)
          ((3 / 200 : ℝ) • axisVector .x + (3 / 200 : ℝ) • axisVector .y) =
        (-3 / 100000 : ℝ) • axisVector .z := by
    ext i
    fin_cases i <;>
      simp [spatialCrossProduct, axisVector, cross_apply] <;>
      norm_num
  have hCrossHorizontal :
      spatialCrossProduct
          ((1 / 500 : ℝ) • axisVector .x)
          ((-3 / 200 : ℝ) • axisVector .x + (-3 / 200 : ℝ) • axisVector .y) =
        (-3 / 100000 : ℝ) • axisVector .z := by
    ext i
    fin_cases i <;>
      simp [spatialCrossProduct, axisVector, cross_apply] <;>
      norm_num
  have hNormVertical :
      ‖(3 / 200 : ℝ) • axisVector .x + (3 / 200 : ℝ) • axisVector .y‖ =
        3 * Real.sqrt 2 / 200 := by
    rw [EuclideanSpace.norm_eq]
    simp [axisVector, Fin.sum_univ_succ]
    rw [show (3 / 200 : ℝ) ^ 2 + (3 / 200 : ℝ) ^ 2 =
        (3 * Real.sqrt 2 / 200) ^ 2 by
      have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      nlinarith]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hNormHorizontal :
      ‖(-3 / 200 : ℝ) • axisVector .x + (-3 / 200 : ℝ) • axisVector .y‖ =
        3 * Real.sqrt 2 / 200 := by
    rw [EuclideanSpace.norm_eq]
    simp [axisVector, Fin.sum_univ_succ]
    rw [show (-3 / 200 : ℝ) ^ 2 + (-3 / 200 : ℝ) ^ 2 =
        (3 * Real.sqrt 2 / 200) ^ 2 by
      have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      nlinarith]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hNormAxisZ : ‖axisVector .z‖ = (1 : ℝ) := by
    rw [EuclideanSpace.norm_eq]
    norm_num [axisVector, Pi.single_apply, Fin.sum_univ_succ]
  rw [hMagnitude.magnitudeAtP, hSuperposition.totalAtPIsVectorSum,
    hBiotSavart.fieldAtP .vertical,
    hBiotSavart.fieldAtP .horizontal,
    hVacuum.standardSIReadout,
    hData.currentMagnitudeIsTwentyEightAmperes,
    hDisplacementVertical, hDisplacementHorizontal,
    hCurrentElementVertical, hCurrentElementHorizontal,
    hNormVertical, hNormHorizontal, hCrossVertical, hCrossHorizontal]
  clear hDisplacementVertical hDisplacementHorizontal
    hCurrentElementVertical hCurrentElementHorizontal
    hCrossVertical hCrossHorizontal hNormVertical hNormHorizontal
  clear hData hFigure hPhysical hVacuum hSteady hBiotSavart hSuperposition
    hMagnitude setup
  have hCoefficient :
      ((4 * Real.pi / 10 ^ 7 * 28 /
            (4 * Real.pi * (3 * Real.sqrt 2 / 200) ^ 3)) +
        (4 * Real.pi / 10 ^ 7 * 28 /
            (4 * Real.pi * (3 * Real.sqrt 2 / 200) ^ 3))) *
          (-3 / 100000) =
        -(14 * Real.sqrt 2 / 1125000) := by
    have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hpi_ne, hsqrt_ne]
    nlinarith
  rw [← add_smul, smul_smul, hCoefficient, norm_smul, hNormAxisZ]
  simp only [Real.norm_eq_abs, norm_neg, mul_one]
  rw [abs_of_nonneg]
  positivity

/-- Labels of the four magnetic-field-magnitude choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-field magnitude in teslas displayed beside each answer choice. -/
def displayedMagneticFieldInTeslas : AnswerChoice → ℝ
  | .A => 212 / 10 ^ 7
  | .B => 176 / 10 ^ 7
  | .C => 88 / 10 ^ 7
  | .D => 176 / 10 ^ 6

/-!
Rounding to the nearest `0.01 * 10⁻⁵ T`, the precision of the recorded
choice `1.76 * 10⁻⁵ T`.
-/
def RoundsToChoicePrecision (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / (2 * 10 ^ 7)

/-- A displayed choice is strictly closer than every distinct alternative. -/
def IsUniqueClosestDisplayedAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice, otherChoice ≠ choice →
    |actual - displayedMagneticFieldInTeslas choice| <
      |actual - displayedMagneticFieldInTeslas otherChoice|

/-!
Blueprint declaration `thm:physics:phyx_mini_0961:target`.

The two marked elements produce an exact total magnitude
`14 * sqrt 2 / 1125000 T`, which rounds to `1.76 * 10⁻⁵ T` and uniquely
selects answer B.
-/
theorem magneticFieldMagnitudeAtMidpoint
    (setup : RightAngleWireSetup)
    (hData : MatchesRightAngleWireProblemData setup)
    (hFigure : MatchesPrimaryRightAngleWireFigure setup)
    (hPhysical : HasPhysicalRightAngleWireParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hSteady : SatisfiesSteadyCurrentFieldModel setup)
    (hBiotSavart : SatisfiesShortElementBiotSavartLaw setup)
    (hSuperposition : SatisfiesTwoElementSuperposition setup)
    (hMagnitude : MagnitudeReadoutMatchesTotalField setup) :
    totalFieldMagnitudeAtPInTeslas setup =
        14 * Real.sqrt 2 / 1125000 ∧
      RoundsToChoicePrecision
        (totalFieldMagnitudeAtPInTeslas setup)
        (displayedMagneticFieldInTeslas .B) ∧
      IsUniqueClosestDisplayedAnswer
        (totalFieldMagnitudeAtPInTeslas setup) .B := by
  have hExact := totalFieldMagnitudeAtP_exact setup hData hFigure hPhysical
    hVacuum hSteady hBiotSavart hSuperposition hMagnitude
  have hSqrtBounds :
      (141421 / 100000 : ℝ) < Real.sqrt 2 ∧
        Real.sqrt 2 < (141422 / 100000 : ℝ) := by
    clear hExact hData hFigure hPhysical hVacuum hSteady hBiotSavart
      hSuperposition hMagnitude setup
    have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    constructor <;> nlinarith
  rcases hSqrtBounds with ⟨hsqrt_lower, hsqrt_upper⟩
  refine ⟨hExact, ?_, ?_⟩
  · unfold RoundsToChoicePrecision
    rw [hExact]
    clear hExact hData hFigure hPhysical hVacuum hSteady hBiotSavart
      hSuperposition hMagnitude setup
    change
      |14 * Real.sqrt 2 / 1125000 - 176 / 10 ^ 7| <
        (1 / (2 * 10 ^ 7) : ℝ)
    rw [abs_lt]
    constructor <;> norm_num <;> nlinarith
  · unfold IsUniqueClosestDisplayedAnswer
    rw [hExact]
    clear hExact hData hFigure hPhysical hVacuum hSteady hBiotSavart
      hSuperposition hMagnitude setup
    have hB :
        14 * Real.sqrt 2 / 1125000 -
            displayedMagneticFieldInTeslas .B ≤ 0 := by
      norm_num [displayedMagneticFieldInTeslas]
      nlinarith
    intro otherChoice hOtherChoice
    fin_cases otherChoice
    · have hA :
          14 * Real.sqrt 2 / 1125000 -
              displayedMagneticFieldInTeslas .A ≤ 0 := by
        norm_num [displayedMagneticFieldInTeslas]
        nlinarith
      rw [abs_of_nonpos hB, abs_of_nonpos hA]
      norm_num [displayedMagneticFieldInTeslas]
    · contradiction
    · have hC :
          0 ≤ 14 * Real.sqrt 2 / 1125000 -
              displayedMagneticFieldInTeslas .C := by
        norm_num [displayedMagneticFieldInTeslas]
        nlinarith
      rw [abs_of_nonpos hB, abs_of_nonneg hC]
      norm_num [displayedMagneticFieldInTeslas]
      nlinarith
    · have hD :
          14 * Real.sqrt 2 / 1125000 -
              displayedMagneticFieldInTeslas .D ≤ 0 := by
        norm_num [displayedMagneticFieldInTeslas]
        nlinarith
      rw [abs_of_nonpos hB, abs_of_nonpos hD]
      norm_num [displayedMagneticFieldInTeslas]

end PhyXMiniProblems.ProblemPhyXMini0961
