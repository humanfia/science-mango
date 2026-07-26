import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began.
The source asks about `x = 2 cm`, although the graph axis is in metres, and records
`-5 V/m`; both details are preserved literally below. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0875

open CarriesDimension Dimension

/-!
# Electric-field component from a potential-versus-position graph

The primary image plots electric potential `V`, in volts, against the
Cartesian coordinate `x`, in metres.  Its straight segments join
`(-3, 0)`, `(-1, -10)`, `(1, 10)`, and `(3, 0)`.  The potential is stated to
be independent of `y` and `z`.

Signed axial positions, electric potentials, and electric-field components
are unit-independent Physlib `Dimensionful` quantities.  Real numbers occur
only as readouts in explicitly named units.  The full electric field retains
Physlib's spacetime-dependent vector-field type.

Assumption/target split:

* governing laws: time independence, calibration of the dimensionful
  `x`-component against the Physlib vector field, and the electrostatic law
  `Eₓ = -dV/dx`;
* previous-part results: none;
* figure/data readouts: the axis labels and units, all four plotted vertices,
  the three straight segments, and the statement that `V` is independent of
  `y` and `z`;
* current target: at the literal question position `x = 2 cm = 0.02 m`, the
  graph and electrostatic law give `Eₓ = -10 V/m`; consequently none of the
  displayed choices matches the physical field component.

The recorded choice D remains dataset metadata only.  No premise or setup
field states the current target value or the answer-choice mismatch.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L T⁻² C⁻¹` of an electric-field component. -/
def electricFieldComponentDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed physical position on the plotted Cartesian axis. -/
abbrev AxialPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed, unit-independent electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A signed, unit-independent Cartesian electric-field component. -/
abbrev ElectricFieldComponentQuantity : Type :=
  Dimensionful (WithDim electricFieldComponentDimension ℝ)

/-- Read a signed axial position in a selected physical length unit. -/
def positionReadout
    (unit : LengthUnit) (position : AxialPositionQuantity) : ℝ :=
  (position ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Construct a signed physical position from a readout in a selected unit. -/
def positionFromReadout
    (unit : LengthUnit) (value : ℝ) : AxialPositionQuantity :=
  toDimensionful
    ({ UnitChoices.SI with length := unit } : UnitChoices)
    (show WithDim L𝓭 ℝ from ⟨value⟩)

/-- Coherent-SI readout of electric potential, in volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Coherent-SI readout of a signed field component, in volts per metre. -/
def electricFieldComponentInVoltsPerMeter
    (component : ElectricFieldComponentQuantity) : ℝ :=
  (component UnitChoices.SI).val

/-! ## Figure labels, vertices, and physical setup -/

/-- The horizontal and vertical axes visible in image `875.png`. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity named by a graph axis. -/
inductive GraphAxisQuantity where
  | xPosition
  | electricPotential
  deriving DecidableEq, Repr

/-- Literal unit text printed beside a graph axis. -/
inductive GraphAxisUnitLabel where
  | meters
  | volts
  deriving DecidableEq, Repr

/-- The four vertices of the piecewise-linear green plot, from left to right. -/
inductive PotentialGraphVertex where
  | leftZero
  | trough
  | peak
  | rightZero
  deriving DecidableEq, Fintype, Repr

/-- The three straight green segments connecting adjacent vertices. -/
inductive PotentialGraphSegment where
  | leftDescending
  | middleAscending
  | rightDescending
  deriving DecidableEq, Fintype, Repr

/-- Endpoints that the supplied image assigns to each plotted segment. -/
def expectedSegmentEndpoints :
    PotentialGraphSegment → PotentialGraphVertex × PotentialGraphVertex
  | .leftDescending => (.leftZero, .trough)
  | .middleAscending => (.trough, .peak)
  | .rightDescending => (.peak, .rightZero)

/-- Metre coordinate read from the image for each plotted vertex. -/
def expectedVertexPositionInMeters : PotentialGraphVertex → ℝ
  | .leftZero => -3
  | .trough => -1
  | .peak => 1
  | .rightZero => 3

/-- Potential, in volts, read from the image for each plotted vertex. -/
def expectedVertexPotentialInVolts : PotentialGraphVertex → ℝ
  | .leftZero => 0
  | .trough => -10
  | .peak => 10
  | .rightZero => 0

/-- Typed presentation data transcribed from the supplied graph. -/
structure PotentialVersusPositionFigure where
  axisQuantity : GraphAxis → GraphAxisQuantity
  axisUnitLabel : GraphAxis → GraphAxisUnitLabel
  vertexPosition : PotentialGraphVertex → AxialPositionQuantity
  vertexPotential : PotentialGraphVertex → ElectricPotentialQuantity
  segmentEndpoints :
    PotentialGraphSegment → PotentialGraphVertex × PotentialGraphVertex
  segmentDrawnStraight : PotentialGraphSegment → Bool

/-- The coordinate index denoted by `x` in the Cartesian frame. -/
def xAxis : Fin 3 := 0

/-- A `Space 3` point on the `x`-axis, with its coordinate read in metres. -/
def pointOnXAxisInMeters (xMeters : ℝ) : Space 3 :=
  ⟨fun i => if i = xAxis then xMeters else 0⟩

/-!
Independent physical fields and observables in the electrostatic setup.

Neither the field component at the question position nor any answer choice is
stored here.  Governing-law premises below relate these independent fields.
-/
structure ElectrostaticPotentialGraphSetup where
  figure : PotentialVersusPositionFigure
  potentialAt : Space 3 → ElectricPotentialQuantity
  potentialAlongX : AxialPositionQuantity → ElectricPotentialQuantity
  electricField : Electromagnetism.ElectricField 3
  electricFieldXAlongAxis :
    AxialPositionQuantity → ElectricFieldComponentQuantity
  observationTime : Time

/-- Volt readout of the physical potential profile as a function of metres. -/
def potentialProfileInVolts
    (setup : ElectrostaticPotentialGraphSetup) (xMeters : ℝ) : ℝ :=
  electricPotentialInVolts
    (setup.potentialAlongX
      (positionFromReadout LengthUnit.meters xMeters))

/-- Volts-per-metre readout of the independent `x`-component observable. -/
def electricFieldXInVoltsPerMeter
    (setup : ElectrostaticPotentialGraphSetup)
    (position : AxialPositionQuantity) : ℝ :=
  electricFieldComponentInVoltsPerMeter
    (setup.electricFieldXAlongAxis position)

/-! ## Figure evidence and governing electrostatics -/

/--
The axis metadata, vertices, and straight-segment incidences visible in the
primary image.  This contains potential data only, not an electric-field
answer.
-/
structure MatchesSuppliedPotentialGraph
    (setup : ElectrostaticPotentialGraphSetup) : Prop where
  horizontalAxisIsPosition :
    setup.figure.axisQuantity .horizontal = .xPosition
  verticalAxisIsPotential :
    setup.figure.axisQuantity .vertical = .electricPotential
  horizontalAxisUsesMeters :
    setup.figure.axisUnitLabel .horizontal = .meters
  verticalAxisUsesVolts :
    setup.figure.axisUnitLabel .vertical = .volts
  vertexPositionReadouts : ∀ vertex,
    positionReadout LengthUnit.meters
        (setup.figure.vertexPosition vertex) =
      expectedVertexPositionInMeters vertex
  vertexPotentialReadouts : ∀ vertex,
    electricPotentialInVolts (setup.figure.vertexPotential vertex) =
      expectedVertexPotentialInVolts vertex
  segmentEndpointLabels : ∀ segment,
    setup.figure.segmentEndpoints segment = expectedSegmentEndpoints segment
  allThreeSegmentsAreStraight : ∀ segment,
    setup.figure.segmentDrawnStraight segment = true

/--
The physical potential profile is the piecewise-affine green graph.  The
three formulas are the straight-line interpolants through the four supplied
vertices and contain no electric-field conclusion.
-/
structure PotentialProfileMatchesFigure
    (setup : ElectrostaticPotentialGraphSetup) : Prop where
  physicalPotentialAtVertices : ∀ vertex,
    setup.potentialAlongX (setup.figure.vertexPosition vertex) =
      setup.figure.vertexPotential vertex
  leftStraightSegment : ∀ xMeters,
    xMeters ∈ Set.Icc (-3 : ℝ) (-1) →
      potentialProfileInVolts setup xMeters = -5 * (xMeters + 3)
  middleStraightSegment : ∀ xMeters,
    xMeters ∈ Set.Icc (-1 : ℝ) 1 →
      potentialProfileInVolts setup xMeters = 10 * xMeters
  rightStraightSegment : ∀ xMeters,
    xMeters ∈ Set.Icc (1 : ℝ) 3 →
      potentialProfileInVolts setup xMeters = 5 * (3 - xMeters)

/-- The problem statement's assertion that potential is independent of `y,z`. -/
structure PotentialIsIndependentOfYAndZ
    (setup : ElectrostaticPotentialGraphSetup) : Prop where
  dependsOnlyOnX : ∀ point,
    setup.potentialAt point =
      setup.potentialAlongX
        (positionFromReadout LengthUnit.meters (point.val xAxis))

/--
The dimensionful component observable calibrates the `x` component of
Physlib's full vector electric field in coherent SI units.
-/
structure CalibratesElectricFieldXComponent
    (setup : ElectrostaticPotentialGraphSetup) : Prop where
  xComponentCalibration : ∀ position,
    setup.electricField setup.observationTime
        (pointOnXAxisInMeters
          (positionReadout LengthUnit.meters position)) xAxis =
      electricFieldXInVoltsPerMeter setup position

/--
Electrostatic governing law: the field is static and, wherever the plotted
potential has derivative `slope` in volts per metre, `Eₓ = -slope`.
This is a general physical law rather than the requested numerical answer.
-/
structure SatisfiesElectrostaticPotentialFieldLaw
    (setup : ElectrostaticPotentialGraphSetup) : Prop where
  fieldIsTimeIndependent : ∀ time point,
    setup.electricField time point =
      setup.electricField setup.observationTime point
  electricFieldIsNegativePotentialDerivative :
    ∀ position slope,
      HasDerivAt (potentialProfileInVolts setup) slope
          (positionReadout LengthUnit.meters position) →
        electricFieldXInVoltsPerMeter setup position = -slope

/-! ## Literal question position, displayed choices, and target -/

/-- The position written in the question: `x = 2 cm`. -/
noncomputable def questionPosition : AxialPositionQuantity :=
  positionFromReadout LengthUnit.centimeters 2

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed field component, in volts per metre, printed beside each choice. -/
def AnswerChoice.fieldComponentInVoltsPerMeter : AnswerChoice → ℝ
  | .A => 12
  | .B => -14
  | .C => -200
  | .D => -5

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A choice matches the independently modeled field-component observable. -/
def AnswerMatchesElectricField
    (setup : ElectrostaticPotentialGraphSetup)
    (choice : AnswerChoice) : Prop :=
  electricFieldXInVoltsPerMeter setup questionPosition =
    choice.fieldComponentInVoltsPerMeter

/-- The literal question coordinate has the readout `2 cm`. -/
lemma questionPosition_readout_centimeters :
    positionReadout LengthUnit.centimeters questionPosition = 2 := by
  simp [questionPosition, positionReadout, positionFromReadout,
    CarriesDimension.toDimensionful_apply_apply]

/-- Equivalently, the literal question coordinate is `0.02 m`. -/
lemma questionPosition_readout_meters :
    positionReadout LengthUnit.meters questionPosition = 2 / 100 := by
  norm_num [questionPosition, positionReadout, positionFromReadout,
    CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale,
    LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
    LengthUnit.div_eq_val, NNReal.smul_def, NNReal.toReal]

/-!
At the literal source position `x = 2 cm = 0.02 m`, the point lies on the
middle segment `V(x) = 10x`, so `dV/dx = 10 V/m` and the electrostatic law
gives `Eₓ = -10 V/m`.  None of the four displayed choices has that value.

This declaration formalizes `thm:physics:phyx_mini_0875:target` using the
physically supported result.  The recorded value `-5` and label D occur only
in answer-choice metadata, not in any setup or premise.  The source's
unit/sign inconsistency is exposed by the second conjunct rather than hidden
in an assumption.
-/
theorem problem_phyx_mini_0875
    (setup : ElectrostaticPotentialGraphSetup)
    (_figure : MatchesSuppliedPotentialGraph setup)
    (_profile : PotentialProfileMatchesFigure setup)
    (_independence : PotentialIsIndependentOfYAndZ setup)
    (_calibration : CalibratesElectricFieldXComponent setup)
    (_law : SatisfiesElectrostaticPotentialFieldLaw setup) :
    electricFieldXInVoltsPerMeter setup questionPosition = -10 ∧
      ∀ choice, ¬ AnswerMatchesElectricField setup choice := by
  have h_deriv :
      HasDerivAt (potentialProfileInVolts setup) 10
        (positionReadout LengthUnit.meters questionPosition) := by
    rw [questionPosition_readout_meters]
    apply
      (hasDerivAt_const_mul (x := (2 / 100 : ℝ)) (10 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds (a := (-1 : ℝ)) (b := 1)
        (x := (2 / 100 : ℝ)) (by norm_num) (by norm_num)] with x hx
    exact _profile.middleStraightSegment x hx
  have hfield :=
    _law.electricFieldIsNegativePotentialDerivative questionPosition 10 h_deriv
  refine ⟨hfield, ?_⟩
  intro choice hmatch
  unfold AnswerMatchesElectricField at hmatch
  rw [hfield] at hmatch
  cases choice <;>
    norm_num [AnswerChoice.fieldComponentInVoltsPerMeter] at hmatch

end PhyXMiniProblems.ProblemPhyXMini0875
