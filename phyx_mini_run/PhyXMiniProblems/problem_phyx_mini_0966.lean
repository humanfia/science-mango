import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0966

open Dimension

/-!
# Magnetic field at the center of an annular-sector wire

The wire consists, in current order, of the inner circular arc `DA`, the
radial connector `AB`, the outer circular arc `BC`, and the radial connector
`CD`.  Both arcs are centered at `P` and subtend `120°`.  The inner and outer
radii are respectively `20 cm` and `30 cm`, so each radial connector has
length `10 cm`.  The `12 A` current runs clockwise on `DA` and
counterclockwise on `BC`.

Lengths, current, vacuum permeability, and the requested magnetic-flux-density
magnitude are unit-independent Physlib dimensionful quantities.  The magnetic
fields themselves use Physlib's spacetime-dependent vector-field type.  Real
numbers below are used only for coherent-SI readouts, displayed labels,
angles, and spatial-vector components.

Assumption/target split:

* governing laws: the circular-arc Biot--Savart center-field law, the zero
  center field of a radial current segment, magnetic-field superposition,
  steady-current time independence, and norm calibration of the magnitude;
* previous-part results: none;
* figure/data readouts: labels `P,A,B,C,D`, the four segments, concentric
  `20 cm` and `30 cm` arcs, two `10 cm` radial connectors, the `120°` sector,
  the depicted current traversal, `I = 12 A`, and purple current arrows;
* current target conclusions: the net field points into the page with exact
  magnitude `4π/3 μT`, rounds to `4.19 μT`, and uniquely selects choice B.

No target field value or answer choice occurs in a setup, figure, geometry,
or governing-law premise.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

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

/-- A nonnegative, unit-independent steady-current magnitude. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the three printed length values. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI ampere readout of the current magnitude. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Coherent-SI permeability readout in tesla-metres per ampere. -/
def permeabilityInTeslaMetersPerAmpere
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  ((permeability UnitChoices.SI).val : ℝ)

/-- Coherent-SI tesla readout of a magnetic-flux-density magnitude. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Microtesla readout used by the multiple-choice answers. -/
def magneticFluxDensityInMicroteslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  10 ^ 6 * magneticFluxDensityInTeslas density

/-! ## Figure labels, geometry, and current orientation -/

/-- A coherent-SI three-dimensional spatial vector. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- The five point labels printed in the primary image. -/
inductive FigurePoint where
  | P
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The four labelled pieces of the closed wire. -/
inductive WireSegment where
  | innerArcDA
  | connectorAB
  | outerArcBC
  | connectorCD
  deriving DecidableEq, Fintype, Repr

/-- The two circular pieces, distinguished by radius and endpoint labels. -/
inductive ArcSegment where
  | innerDA
  | outerBC
  deriving DecidableEq, Fintype, Repr

/-- The two straight radial pieces. -/
inductive RadialConnector where
  | AB
  | CD
  deriving DecidableEq, Fintype, Repr

/-- Convert an arc label to the corresponding complete-wire segment label. -/
def wireSegmentOfArc : ArcSegment → WireSegment
  | .innerDA => .innerArcDA
  | .outerBC => .outerArcBC

/-- Convert a radial-connector label to its complete-wire segment label. -/
def wireSegmentOfConnector : RadialConnector → WireSegment
  | .AB => .connectorAB
  | .CD => .connectorCD

/-- Sense in which current traverses an arc as viewed in the page. -/
inductive ArcCurrentSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- The two directions normal to the plane of the image. -/
inductive PageNormalDirection where
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Color of the current arrows distinguished by the primary raster. -/
inductive FigureColor where
  | purple
  | other
  deriving DecidableEq, Repr

/-- Unit normal associated with the two page-normal directions. -/
def pageNormalVector : PageNormalDirection → SpatialVector
  | .outOfPage => EuclideanSpace.single (2 : Fin 3) 1
  | .intoPage => -EuclideanSpace.single (2 : Fin 3) 1

/-- Right-hand-rule field direction at the center of a current-carrying arc. -/
def arcFieldNormalVector : ArcCurrentSense → SpatialVector
  | .clockwise => pageNormalVector .intoPage
  | .counterclockwise => pageNormalVector .outOfPage

/-- Current-directed starting point of each labelled wire segment. -/
def currentStartPoint : WireSegment → FigurePoint
  | .innerArcDA => .D
  | .connectorAB => .A
  | .outerArcBC => .B
  | .connectorCD => .C

/-- Current-directed ending point of each labelled wire segment. -/
def currentEndPoint : WireSegment → FigurePoint
  | .innerArcDA => .A
  | .connectorAB => .B
  | .outerArcBC => .C
  | .connectorCD => .D

/-!
Literal point, segment, angle, and current-arrow evidence in image `966.png`.
The figure stores no magnetic-field value and no answer choice.
-/
structure AnnularSectorFigure where
  pointLabelShown : FigurePoint → Bool
  segmentShown : WireSegment → Bool
  centerMarkerShownAtP : Bool
  angleMarkerShown : Bool
  displayedCentralAngleInDegrees : ℝ
  currentArrowShown : WireSegment → Bool
  currentArrowStart : WireSegment → FigurePoint
  currentArrowEnd : WireSegment → FigurePoint
  arcCurrentSense : ArcSegment → ArcCurrentSense
  currentArrowColor : FigureColor

/-!
Independent physical quantities, geometry, and field observables.  In
particular, `magneticFluxDensityMagnitudeAtP` and `totalMagneticField` are not
defined from the requested answer.
-/
structure AnnularSectorWireSetup where
  unitSystem : UnitChoices
  currentIsSteady : Bool
  currentMagnitude : ElectricCurrentQuantity
  arcRadius : ArcSegment → LengthQuantity
  connectorLength : RadialConnector → LengthQuantity
  centralAngleRadians : ℝ
  centerPoint : Space 3
  pointPosition : FigurePoint → Space 3
  electromagneticSystem : Electromagnetism.EMSystem
  vacuumPermeability : MagneticPermeabilityQuantity
  magneticFieldDueToSegment : WireSegment → Electromagnetism.MagneticField 3
  totalMagneticField : Electromagnetism.MagneticField 3
  magneticFluxDensityMagnitudeAtP : MagneticFluxDensityQuantity
  observationTime : Time
  figure : AnnularSectorFigure

/-- SI vector field contribution of one segment, evaluated at `P`. -/
def segmentFieldVectorAtPInTeslas
    (setup : AnnularSectorWireSetup) (segment : WireSegment) : SpatialVector :=
  setup.magneticFieldDueToSegment segment setup.observationTime
    setup.centerPoint

/-- Total SI magnetic-field vector evaluated at `P`. -/
def totalFieldVectorAtPInTeslas
    (setup : AnnularSectorWireSetup) : SpatialVector :=
  setup.totalMagneticField setup.observationTime setup.centerPoint

/-! ## Problem data and primary-image geometry -/

/-- Numerical quantities stated in the prose and displayed sector angle. -/
structure MatchesAnnularSectorProblemData
    (setup : AnnularSectorWireSetup) : Prop where
  usesSIUnits : setup.unitSystem = UnitChoices.SI
  currentIsSteady : setup.currentIsSteady = true
  currentMagnitudeIsTwelveAmperes :
    currentInAmperes setup.currentMagnitude = 12
  innerArcRadiusIsTwentyCentimeters :
    lengthInCentimeters (setup.arcRadius .innerDA) = 20
  outerArcRadiusIsThirtyCentimeters :
    lengthInCentimeters (setup.arcRadius .outerBC) = 30
  connectorABIsTenCentimeters :
    lengthInCentimeters (setup.connectorLength .AB) = 10
  connectorCDIsTenCentimeters :
    lengthInCentimeters (setup.connectorLength .CD) = 10
  centralAngleIsTwoPiOverThree :
    setup.centralAngleRadians = 2 * Real.pi / 3

/-!
Primary-raster transcription.  It fixes the closed traversal
`D → A → B → C → D`, hence opposite arc senses, but asserts no field value.
-/
structure MatchesPrimaryAnnularSectorFigure
    (setup : AnnularSectorWireSetup) : Prop where
  everyPointLabelShown : ∀ point,
    setup.figure.pointLabelShown point = true
  everyWireSegmentShown : ∀ segment,
    setup.figure.segmentShown segment = true
  centerMarkerIsShownAtP : setup.figure.centerMarkerShownAtP = true
  angleMarkerIsShown : setup.figure.angleMarkerShown = true
  angleLabelReadsOneHundredTwenty :
    setup.figure.displayedCentralAngleInDegrees = 120
  everyCurrentArrowShown : ∀ segment,
    setup.figure.currentArrowShown segment = true
  currentTraversalStartsAtDepictedEndpoint : ∀ segment,
    setup.figure.currentArrowStart segment = currentStartPoint segment
  currentTraversalEndsAtDepictedEndpoint : ∀ segment,
    setup.figure.currentArrowEnd segment = currentEndPoint segment
  innerArcCurrentIsClockwise :
    setup.figure.arcCurrentSense .innerDA = .clockwise
  outerArcCurrentIsCounterclockwise :
    setup.figure.arcCurrentSense .outerBC = .counterclockwise
  currentArrowsArePurple : setup.figure.currentArrowColor = .purple

/-!
Metric and radial-ray content of the concentric annular-sector geometry.
The scalar `centralAngleRadians` is the angle between the two radial rays.
-/
structure HasAnnularSectorGeometry
    (setup : AnnularSectorWireSetup) : Prop where
  centerPointCarriesLabelP : setup.centerPoint = setup.pointPosition .P
  AOnInnerCircle :
    dist setup.centerPoint (setup.pointPosition .A) =
      lengthInMeters (setup.arcRadius .innerDA)
  DOnInnerCircle :
    dist setup.centerPoint (setup.pointPosition .D) =
      lengthInMeters (setup.arcRadius .innerDA)
  BOnOuterCircle :
    dist setup.centerPoint (setup.pointPosition .B) =
      lengthInMeters (setup.arcRadius .outerBC)
  COnOuterCircle :
    dist setup.centerPoint (setup.pointPosition .C) =
      lengthInMeters (setup.arcRadius .outerBC)
  ABHasConnectorLength :
    dist (setup.pointPosition .A) (setup.pointPosition .B) =
      lengthInMeters (setup.connectorLength .AB)
  CDHasConnectorLength :
    dist (setup.pointPosition .C) (setup.pointPosition .D) =
      lengthInMeters (setup.connectorLength .CD)
  AAndBLieOnSameRadialRay :
    lengthInMeters (setup.arcRadius .outerBC) •
        (setup.pointPosition .A -ᵥ setup.centerPoint) =
      lengthInMeters (setup.arcRadius .innerDA) •
        (setup.pointPosition .B -ᵥ setup.centerPoint)
  CAndDLieOnSameRadialRay :
    lengthInMeters (setup.arcRadius .outerBC) •
        (setup.pointPosition .D -ᵥ setup.centerPoint) =
      lengthInMeters (setup.arcRadius .innerDA) •
        (setup.pointPosition .C -ᵥ setup.centerPoint)

/-- Positivity and branch assumptions for a nondegenerate annular sector. -/
structure HasPhysicalAnnularSectorParameters
    (setup : AnnularSectorWireSetup) : Prop where
  currentPositive : 0 < currentInAmperes setup.currentMagnitude
  innerRadiusPositive :
    0 < lengthInMeters (setup.arcRadius .innerDA)
  outerRadiusLarger :
    lengthInMeters (setup.arcRadius .innerDA) <
      lengthInMeters (setup.arcRadius .outerBC)
  connectorLengthsPositive : ∀ connector,
    0 < lengthInMeters (setup.connectorLength connector)
  centralAngleIsProper :
    0 < setup.centralAngleRadians ∧ setup.centralAngleRadians < 2 * Real.pi
  permeabilityPositive :
    0 < permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability

/-!
The physical permeability agrees with the selected Physlib electromagnetic
system and has the standard vacuum SI value `4π × 10⁻⁷ T m/A`.
-/
structure UsesStandardVacuumPermeability
    (setup : AnnularSectorWireSetup) : Prop where
  agreesWithElectromagneticSystem :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      setup.electromagneticSystem.μ₀
  standardSIReadout :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      4 * Real.pi / 10 ^ 7

/-! ## Governing magnetic-field laws -/

/-- A steady line current produces time-independent segment and total fields. -/
structure SatisfiesSteadyCurrentFieldModel
    (setup : AnnularSectorWireSetup) : Prop where
  segmentFieldsTimeIndependent : ∀ segment time position,
    setup.magneticFieldDueToSegment segment time position =
      setup.magneticFieldDueToSegment segment setup.observationTime position
  totalFieldTimeIndependent : ∀ time position,
    setup.totalMagneticField time position =
      setup.totalMagneticField setup.observationTime position

/-!
At their common center, each circular arc obeys

`B = μ₀ I θ / (4πR)`

with direction selected by the right-hand rule.  This is a general governing
law in the stored physical quantities, not the requested numerical result.
-/
structure SatisfiesCircularArcBiotSavartLaw
    (setup : AnnularSectorWireSetup) : Prop where
  fieldAtCenter : ∀ arc,
    segmentFieldVectorAtPInTeslas setup (wireSegmentOfArc arc) =
      (permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability *
          currentInAmperes setup.currentMagnitude *
          setup.centralAngleRadians /
          (4 * Real.pi * lengthInMeters (setup.arcRadius arc))) •
        arcFieldNormalVector (setup.figure.arcCurrentSense arc)

/-!
A straight radial current element has `dℓ ∥ r`, so its Biot--Savart cross
product and hence its field at the center `P` vanish.
-/
structure SatisfiesRadialConnectorBiotSavartLaw
    (setup : AnnularSectorWireSetup) : Prop where
  fieldAtCenterVanishes : ∀ connector,
    segmentFieldVectorAtPInTeslas setup
      (wireSegmentOfConnector connector) = 0

/-- The total field at `P` is the vector sum of all four segment fields. -/
structure SatisfiesMagneticFieldSuperposition
    (setup : AnnularSectorWireSetup) : Prop where
  totalAtCenterIsSegmentSum :
    totalFieldVectorAtPInTeslas setup =
      segmentFieldVectorAtPInTeslas setup .innerArcDA +
      segmentFieldVectorAtPInTeslas setup .connectorAB +
      segmentFieldVectorAtPInTeslas setup .outerArcBC +
      segmentFieldVectorAtPInTeslas setup .connectorCD

/-!
The independent dimensionful magnitude observable is calibrated by the norm
of the total Physlib magnetic-field vector at `P`.
-/
structure CalibratesMagneticFluxDensityMagnitudeAtP
    (setup : AnnularSectorWireSetup) : Prop where
  magnitudeIsVectorNorm :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitudeAtP =
      ‖totalFieldVectorAtPInTeslas setup‖

/-! ## Derived field and multiple-choice target -/

/-- Labels of the four displayed magnetic-field magnitudes. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-field magnitude printed beside each choice, in microteslas. -/
def displayedMagneticFieldInMicroteslas : AnswerChoice → ℝ
  | .A => 429 / 100
  | .B => 419 / 100
  | .C => 628 / 100
  | .D => 209 / 100

/-- Rounding to the nearest `0.01 μT`, the precision of every answer choice. -/
def RoundsToNearestHundredthMicrotesla
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-- A displayed answer is strictly closer than every distinct alternative. -/
def IsUniqueClosestDisplayedAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice, otherChoice ≠ choice →
    |actual - displayedMagneticFieldInMicroteslas choice| <
      |actual - displayedMagneticFieldInMicroteslas otherChoice|

/-!
The inner clockwise arc dominates the outer counterclockwise arc.  Their
vector difference is exactly `(4π/3) μT` into the page; both radial connector
contributions vanish.
-/
lemma totalMagneticFieldAtP_exact
    (setup : AnnularSectorWireSetup)
    (hData : MatchesAnnularSectorProblemData setup)
    (hFigure : MatchesPrimaryAnnularSectorFigure setup)
    (hGeometry : HasAnnularSectorGeometry setup)
    (hPhysical : HasPhysicalAnnularSectorParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hSteady : SatisfiesSteadyCurrentFieldModel setup)
    (hArcs : SatisfiesCircularArcBiotSavartLaw setup)
    (hRadial : SatisfiesRadialConnectorBiotSavartLaw setup)
    (hSuperposition : SatisfiesMagneticFieldSuperposition setup) :
    totalFieldVectorAtPInTeslas setup =
      (4 * Real.pi / (3 * 10 ^ 6)) • pageNormalVector .intoPage := by
  have hInnerRadius :
      lengthInMeters (setup.arcRadius .innerDA) = (1 / 5 : ℝ) := by
    have h := hData.innerArcRadiusIsTwentyCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hOuterRadius :
      lengthInMeters (setup.arcRadius .outerBC) = (3 / 10 : ℝ) := by
    have h := hData.outerArcRadiusIsThirtyCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hInnerField := hArcs.fieldAtCenter .innerDA
  have hOuterField := hArcs.fieldAtCenter .outerBC
  have hABField := hRadial.fieldAtCenterVanishes .AB
  have hCDField := hRadial.fieldAtCenterVanishes .CD
  simp only [wireSegmentOfArc] at hInnerField hOuterField
  simp only [wireSegmentOfConnector] at hABField hCDField
  have hInnerCoefficient :
      permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability *
            currentInAmperes setup.currentMagnitude *
            setup.centralAngleRadians /
          (4 * Real.pi *
            lengthInMeters (setup.arcRadius .innerDA)) =
        4 * Real.pi / 10 ^ 6 := by
    rw [hVacuum.standardSIReadout,
      hData.currentMagnitudeIsTwelveAmperes,
      hData.centralAngleIsTwoPiOverThree, hInnerRadius]
    field_simp [Real.pi_ne_zero]
    ring
  have hOuterCoefficient :
      permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability *
            currentInAmperes setup.currentMagnitude *
            setup.centralAngleRadians /
          (4 * Real.pi *
            lengthInMeters (setup.arcRadius .outerBC)) =
        8 * Real.pi / (3 * 10 ^ 6) := by
    rw [hVacuum.standardSIReadout,
      hData.currentMagnitudeIsTwelveAmperes,
      hData.centralAngleIsTwoPiOverThree, hOuterRadius]
    field_simp [Real.pi_ne_zero]
    ring
  have hOppositeNormals :
      pageNormalVector .outOfPage = -pageNormalVector .intoPage := by
    ext i
    fin_cases i <;> simp [pageNormalVector]
  have hNetCoefficient :
      4 * Real.pi / 10 ^ 6 - 8 * Real.pi / (3 * 10 ^ 6) =
        4 * Real.pi / (3 * 10 ^ 6) := by
    ring
  rw [hSuperposition.totalAtCenterIsSegmentSum,
    hInnerField, hABField, hOuterField, hCDField,
    hInnerCoefficient, hOuterCoefficient,
    hFigure.innerArcCurrentIsClockwise,
    hFigure.outerArcCurrentIsCounterclockwise]
  simp only [arcFieldNormalVector, add_zero, zero_add]
  rw [hOppositeNormals, smul_neg, ← sub_eq_add_neg, ← sub_smul,
    hNetCoefficient]

/-!
Blueprint declaration `thm:physics:phyx_mini_0966:target`.

The magnetic-field magnitude at `P` is exactly `4π/3 μT`.  This rounds to
`4.19 μT`, which is uniquely answer B among the supplied alternatives.
-/
theorem problem_phyx_mini_0966
    (setup : AnnularSectorWireSetup)
    (hData : MatchesAnnularSectorProblemData setup)
    (hFigure : MatchesPrimaryAnnularSectorFigure setup)
    (hGeometry : HasAnnularSectorGeometry setup)
    (hPhysical : HasPhysicalAnnularSectorParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hSteady : SatisfiesSteadyCurrentFieldModel setup)
    (hArcs : SatisfiesCircularArcBiotSavartLaw setup)
    (hRadial : SatisfiesRadialConnectorBiotSavartLaw setup)
    (hSuperposition : SatisfiesMagneticFieldSuperposition setup)
    (hMagnitude : CalibratesMagneticFluxDensityMagnitudeAtP setup) :
    magneticFluxDensityInMicroteslas
          setup.magneticFluxDensityMagnitudeAtP = 4 * Real.pi / 3 ∧
      RoundsToNearestHundredthMicrotesla
        (magneticFluxDensityInMicroteslas
          setup.magneticFluxDensityMagnitudeAtP)
        (displayedMagneticFieldInMicroteslas .B) ∧
      IsUniqueClosestDisplayedAnswer
        (magneticFluxDensityInMicroteslas
          setup.magneticFluxDensityMagnitudeAtP) .B := by
  have hField := totalMagneticFieldAtP_exact setup hData hFigure hGeometry
    hPhysical hVacuum hSteady hArcs hRadial hSuperposition
  have hExact : magneticFluxDensityInMicroteslas
      setup.magneticFluxDensityMagnitudeAtP = 4 * Real.pi / 3 := by
    rw [magneticFluxDensityInMicroteslas, hMagnitude.magnitudeIsVectorNorm,
      hField]
    simp [norm_smul, pageNormalVector, abs_of_pos Real.pi_pos]
    ring
  have hActualLtB : 4 * Real.pi / 3 < (419 / 100 : ℝ) := by
    linarith [Real.pi_lt_d4]
  have hActualGtD : (209 / 100 : ℝ) < 4 * Real.pi / 3 := by
    linarith [Real.pi_gt_three]
  have hActualLtA : 4 * Real.pi / 3 < (429 / 100 : ℝ) := by
    linarith
  have hActualLtC : 4 * Real.pi / 3 < (628 / 100 : ℝ) := by
    linarith
  constructor
  · exact hExact
  constructor
  · rw [hExact]
    unfold RoundsToNearestHundredthMicrotesla
    simp only [displayedMagneticFieldInMicroteslas]
    rw [abs_of_neg (sub_neg.mpr hActualLtB)]
    norm_num
    linarith [Real.pi_gt_d2]
  · rw [hExact]
    intro other hOther
    fin_cases other
    · simp only [displayedMagneticFieldInMicroteslas]
      rw [abs_of_neg (sub_neg.mpr hActualLtB),
        abs_of_neg (sub_neg.mpr hActualLtA)]
      norm_num
    · exact (hOther rfl).elim
    · simp only [displayedMagneticFieldInMicroteslas]
      rw [abs_of_neg (sub_neg.mpr hActualLtB),
        abs_of_neg (sub_neg.mpr hActualLtC)]
      norm_num
    · simp only [displayedMagneticFieldInMicroteslas]
      rw [abs_of_neg (sub_neg.mpr hActualLtB),
        abs_of_pos (sub_pos.mpr hActualGtD)]
      norm_num
      linarith [Real.pi_gt_d2]

end PhyXMiniProblems.ProblemPhyXMini0966
