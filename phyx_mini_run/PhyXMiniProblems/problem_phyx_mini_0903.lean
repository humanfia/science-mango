import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0903

open Dimension

/-!
# Electric-field magnitude at vertex 1 of an equilateral triangle

The primary image shows a negative `2.0 nC` point charge at the upper vertex
of an equilateral triangle.  The two lower vertices are labelled `1` and `2`,
and every dashed edge is labelled `1.0 cm`.  The requested observable is the
magnitude of the electric field at vertex `1`.

Charge, planar position, side length, and electric-field vector are represented
as Physlib `Dimensionful` quantities.  Real numbers occur below only as
coherent-SI or displayed-unit readouts.

Assumption/target split:

* governing laws: the planar vector form of the electrostatic point-charge
  Coulomb law, together with the coherent-SI calibration of Coulomb's constant;
* previous-part results: none;
* figure/data readouts: one negative point charge labelled `-2.0 nC`, lower
  points labelled `1` and `2`, three dashed edges, and a `1.0 cm` label on
  every side of the equilateral triangle;
* current target conclusion: the field magnitude at point `1` is
  `1.8 * 10^5 N/C`, answer choice C.

No setup field or premise states the requested numerical field magnitude.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻² C⁻¹` of an electric field. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Vectors in the two-dimensional plane of the supplied diagram. -/
abbrev PlaneVector : Type := EuclideanSpace ℝ (Fin 2)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A unit-independent planar position, expressed relative to a chosen origin. -/
abbrev PlanePositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 PlaneVector)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent planar electric-field vector. -/
abbrev PlaneElectricFieldQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension PlaneVector)

/-- Coherent-SI readout of a signed charge in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the charge label in the image. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI coordinate vector of a planar position, in metres. -/
def positionInMeters (position : PlanePositionQuantity) : PlaneVector :=
  (position UnitChoices.SI).val

/-- Coherent-SI readout of a nonnegative length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the three side labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI readout of an electric-field vector, in newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : PlaneElectricFieldQuantity) : PlaneVector :=
  (field UnitChoices.SI).val

/-- Magnitude of the coherent-SI electric-field readout, in newtons per coulomb. -/
def electricFieldMagnitudeInNewtonsPerCoulomb
    (field : PlaneElectricFieldQuantity) : ℝ :=
  ‖electricFieldVectorInNewtonsPerCoulomb field‖

/-! ## Figure labels and independent physical setup -/

/-- The two observation points printed at the lower vertices. -/
inductive ObservationPoint where
  | point1
  | point2
  deriving DecidableEq, Fintype, Repr

/-- The three vertices of the triangular diagram. -/
inductive DiagramVertex where
  | source
  | point1
  | point2
  deriving DecidableEq, Fintype, Repr

/-- The three dashed sides of the triangle. -/
inductive DiagramEdge where
  | sourcePoint1
  | sourcePoint2
  | point1Point2
  deriving DecidableEq, Fintype, Repr

/-- Endpoints assigned to each named side of the triangle. -/
def DiagramEdge.endpoints : DiagramEdge → DiagramVertex × DiagramVertex
  | .sourcePoint1 => (.source, .point1)
  | .sourcePoint2 => (.source, .point2)
  | .point1Point2 => (.point1, .point2)

/-- Vertex corresponding to a printed observation-point label. -/
def ObservationPoint.vertex : ObservationPoint → DiagramVertex
  | .point1 => .point1
  | .point2 => .point2

/-- Text printed beside each lower observation point. -/
def expectedPointLabel : ObservationPoint → String
  | .point1 => "1"
  | .point2 => "2"

/-- The sign glyph drawn inside the source circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Physical classification of the displayed charge source. -/
inductive ChargeSourceKind where
  | pointCharge
  | extendedCharge
  deriving DecidableEq, Repr

/-- Literal and idealized presentation data transcribed from image `903.png`. -/
structure ElectricFieldTriangleFigure where
  sourceCircleShown : Bool
  sourceSign : FigureChargeSign
  sourceChargeLabelNanocoulombs : ℝ
  observationPointShown : ObservationPoint → Bool
  printedPointLabel : ObservationPoint → String
  dashedEdgeShown : DiagramEdge → Bool
  sideLengthLabelCentimeters : DiagramEdge → ℝ
  triangleAppearsEquilateral : Bool

/-!
The independent physical quantities represented by the image.  In particular,
`electricFieldAt` is an observable and is not defined from an answer choice or
from the requested `1.8 * 10^5 N/C` value.
-/
structure PointChargeTriangleSetup where
  figure : ElectricFieldTriangleFigure
  electromagneticSystem : Electromagnetism.EMSystem
  sourceKind : ChargeSourceKind
  sourceCharge : SignedChargeQuantity
  vertexPosition : DiagramVertex → PlanePositionQuantity
  commonSideLength : LengthQuantity
  electricFieldAt : ObservationPoint → PlaneElectricFieldQuantity

/-- Metre displacement vector from the source to an observation point. -/
def displacementFromSourceInMeters
    (setup : PointChargeTriangleSetup) (point : ObservationPoint) : PlaneVector :=
  positionInMeters (setup.vertexPosition point.vertex) -
    positionInMeters (setup.vertexPosition .source)

/-- Distance in metres between the endpoints of a displayed triangle edge. -/
def edgeLengthInMeters
    (setup : PointChargeTriangleSetup) (edge : DiagramEdge) : ℝ :=
  let endpoints := edge.endpoints
  ‖positionInMeters (setup.vertexPosition endpoints.1) -
    positionInMeters (setup.vertexPosition endpoints.2)‖

/-- Distance in centimetres between the endpoints of a displayed edge. -/
def edgeLengthInCentimeters
    (setup : PointChargeTriangleSetup) (edge : DiagramEdge) : ℝ :=
  100 * edgeLengthInMeters setup edge

/-! ## Scenario, primary-image evidence, and physical parameters -/

/-- The displayed upper object has the point-charge role used by Coulomb's law. -/
structure MatchesSinglePointChargeScenario
    (setup : PointChargeTriangleSetup) : Prop where
  displayedSourceIsPointCharge : setup.sourceKind = .pointCharge

/-!
The labels, dashed geometry, and charge read directly from the primary image,
together with their association to the independent physical quantities.  No
electric-field value appears in this evidence structure.
-/
structure MatchesSuppliedElectricFieldTriangleFigure
    (setup : PointChargeTriangleSetup) : Prop where
  sourceCircleIsShown : setup.figure.sourceCircleShown = true
  sourceSignIsNegative : setup.figure.sourceSign = .minus
  printedSourceCharge : setup.figure.sourceChargeLabelNanocoulombs = -2
  physicalChargeMatchesLabel :
    chargeInNanocoulombs setup.sourceCharge =
      setup.figure.sourceChargeLabelNanocoulombs
  bothObservationPointsAreShown :
    ∀ point, setup.figure.observationPointShown point = true
  printedObservationPointLabels :
    ∀ point,
      setup.figure.printedPointLabel point = expectedPointLabel point
  allThreeEdgesAreDashed :
    ∀ edge, setup.figure.dashedEdgeShown edge = true
  everyPrintedSideLengthIsOneCentimeter :
    ∀ edge, setup.figure.sideLengthLabelCentimeters edge = 1
  physicalEdgesMatchPrintedLengths :
    ∀ edge,
      edgeLengthInCentimeters setup edge =
        setup.figure.sideLengthLabelCentimeters edge
  commonSideLengthMatchesEveryEdge :
    ∀ edge,
      edgeLengthInMeters setup edge =
        lengthInMeters setup.commonSideLength
  commonSideLengthMatchesLabels :
    ∀ edge,
      lengthInCentimeters setup.commonSideLength =
        setup.figure.sideLengthLabelCentimeters edge
  equilateralAppearance : setup.figure.triangleAppearsEquilateral = true

/-!
The rounded coherent-SI value of Coulomb's constant used in the elementary
multiple-choice calculation.  The scalar itself is Physlib's
`Electromagnetism.EMSystem.coulombConstant`.
-/
structure UsesSchoolCoulombConstant
    (setup : PointChargeTriangleSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-- Positivity and source-separation conditions for the intended geometry. -/
structure HasPhysicalPointChargeTriangleParameters
    (setup : PointChargeTriangleSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.commonSideLength
  observationsAvoidSource :
    ∀ point, edgeLengthInMeters setup
      (match point with
      | ObservationPoint.point1 => DiagramEdge.sourcePoint1
      | ObservationPoint.point2 => DiagramEdge.sourcePoint2) ≠ 0
  sourceChargeNonzero : chargeInCoulombs setup.sourceCharge ≠ 0
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Governing electrostatic law -/

/-!
For a source charge `q` at `r₀`, the static vector field at `r ≠ r₀` is

`E(r) = k q (r - r₀) / ‖r - r₀‖³`.

This is a general governing law at both labelled observation points and does
not contain the requested numerical magnitude.
-/
structure SatisfiesPlanarPointChargeCoulombLaw
    (setup : PointChargeTriangleSetup) : Prop where
  fieldOfDisplayedSource : ∀ point,
    ‖displacementFromSourceInMeters setup point‖ ≠ 0 →
      electricFieldVectorInNewtonsPerCoulomb
          (setup.electricFieldAt point) =
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs setup.sourceCharge /
              ‖displacementFromSourceInMeters setup point‖ ^ 3) •
          displacementFromSourceInMeters setup point

/-! ## Derived readouts and multiple-choice target -/

/-- The figure places point `1` exactly `1.0 cm` from the source charge. -/
lemma point1_source_distance_readout
    (setup : PointChargeTriangleSetup)
    (_figure : MatchesSuppliedElectricFieldTriangleFigure setup) :
    edgeLengthInCentimeters setup .sourcePoint1 = 1 := by
  exact
    (_figure.physicalEdgesMatchPrintedLengths .sourcePoint1).trans
      (_figure.everyPrintedSideLengthIsOneCentimeter .sourcePoint1)

/-- The physical source-charge readout is the displayed `-2.0 nC`. -/
lemma source_charge_readout
    (setup : PointChargeTriangleSetup)
    (_figure : MatchesSuppliedElectricFieldTriangleFigure setup) :
    chargeInNanocoulombs setup.sourceCharge = -2 := by
  exact _figure.physicalChargeMatchesLabel.trans _figure.printedSourceCharge

/-!
Specializing the governing law at point `1` gives the vector expression from
which the requested magnitude is later calculated.
-/
lemma fieldAtPoint1_eq_coulombVector
    (setup : PointChargeTriangleSetup)
    (_physical : HasPhysicalPointChargeTriangleParameters setup)
    (_law : SatisfiesPlanarPointChargeCoulombLaw setup) :
    electricFieldVectorInNewtonsPerCoulomb
        (setup.electricFieldAt .point1) =
      (setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs setup.sourceCharge /
            ‖displacementFromSourceInMeters setup .point1‖ ^ 3) •
        displacementFromSourceInMeters setup .point1 := by
  exact _law.fieldOfDisplayedSource .point1 (by
    simpa [displacementFromSourceInMeters, edgeLengthInMeters,
      DiagramEdge.endpoints, ObservationPoint.vertex, norm_sub_rev] using
        (_physical.observationsAvoidSource .point1))

/-- Labels attached to the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Field magnitude in N/C printed beside each answer label. -/
def AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => (125 / 100) * (10 : ℝ) ^ 3
  | .B => (135 / 100) * (10 : ℝ) ^ 5
  | .C => (18 / 10) * (10 : ℝ) ^ 5
  | .D => (533 / 100) * (10 : ℝ) ^ 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
**Blueprint target** `thm:physics:phyx_mini_0903:target`.

For a `-2.0 nC` point charge at a distance of `1.0 cm`, the vector Coulomb
law gives a field magnitude
`(9 * 10^9) * (2 * 10^-9) / (10^-2)^2 = 1.8 * 10^5 N/C`, answer C.
-/
theorem problem_phyx_mini_0903
    (setup : PointChargeTriangleSetup)
    (_scenario : MatchesSinglePointChargeScenario setup)
    (_figure : MatchesSuppliedElectricFieldTriangleFigure setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalPointChargeTriangleParameters setup)
    (_law : SatisfiesPlanarPointChargeCoulombLaw setup) :
    electricFieldMagnitudeInNewtonsPerCoulomb
        (setup.electricFieldAt .point1) =
      (18 / 10 : ℝ) * (10 : ℝ) ^ 5 := by
  have hDistanceScale :
      100 * ‖displacementFromSourceInMeters setup .point1‖ = 1 := by
    simpa [edgeLengthInCentimeters, edgeLengthInMeters,
      displacementFromSourceInMeters, DiagramEdge.endpoints,
      ObservationPoint.vertex, norm_sub_rev] using
        point1_source_distance_readout setup _figure
  have hDistance :
      ‖displacementFromSourceInMeters setup .point1‖ = (1 / 100 : ℝ) := by
    linarith
  have hChargeNano := source_charge_readout setup _figure
  have hCharge :
      chargeInCoulombs setup.sourceCharge = (-2 / (10 : ℝ) ^ 9) := by
    unfold chargeInNanocoulombs at hChargeNano
    norm_num at hChargeNano ⊢
    linarith
  unfold electricFieldMagnitudeInNewtonsPerCoulomb
  rw [fieldAtPoint1_eq_coulombVector setup _physical _law, norm_smul,
    _constant.coulombConstantCalibration, hCharge, hDistance]
  norm_num [Real.norm_eq_abs]

end PhyXMiniProblems.ProblemPhyXMini0903
