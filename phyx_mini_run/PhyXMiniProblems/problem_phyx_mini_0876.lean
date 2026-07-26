import Mathlib.Analysis.Calculus.Gradient.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0876

open Dimension

/-!
# Electric-field magnitude from an equipotential map

The primary raster shows four concentric dashed equipotential contours labelled
`0 V`, `25 V`, `50 V`, and `100 V` on a square grid.  Point `1` is the upper
intersection of the `50 V` contour with the common radial axis, while point `2`
is the lower intersection of the `25 V` contour.  Each grid square has side
length `1 cm`.

The contour radii read from the image are respectively `0.5 cm`, `1.5 cm`,
`2.5 cm`, and `3.5 cm`.  Thus the upper `25 V` and `100 V` intersections used
for a centered estimate about point `1` are separated by `2 cm`.  Their
potential difference is `75 V`, giving the recorded magnitude `3750 V/m`.

Lengths, electric potentials, and electric-field magnitudes are represented by
unit-independent Physlib `Dimensionful` quantities.  Real numbers occur only
as coherent-SI readouts or literal labels from the figure and answer choices.
The vector electric field uses Physlib's `Electromagnetism.ElectricField 2`;
the coordinate plane is Mathlib's `EuclideanSpace ℝ (Fin 2)`.

Assumption/target split:

* governing laws: the displayed curves are equipotential contours, the static
  electric field is the negative gradient of the potential, the dimensionful
  magnitude calibrates the norm of the vector field, and the image is read
  using a centered neighboring-contour estimate;
* previous-part results: none;
* figure/data readouts: the four voltage labels, the two marked-point contour
  memberships and sides, the `1 cm` grid scale, and the four radii counted from
  that grid;
* current target conclusion: the point-`1` field-magnitude readout is answer D,
  namely `3750 V/m`.

No setup field or premise assigns `3750 V/m` to the electric field.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Coherent-SI readout of a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used for the grid scale and contour radii. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI readout of an electric potential in volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Coherent-SI readout of a field magnitude in volts per metre. -/
def electricFieldMagnitudeInVoltsPerMeter
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-! ## Figure labels and independent physical setup -/

/-- The four dashed equipotential contours visible in the primary raster. -/
inductive EquipotentialContour where
  | zeroVolt
  | twentyFiveVolt
  | fiftyVolt
  | hundredVolt
  deriving DecidableEq, Fintype, Repr

/-- The two black points labelled by numerals in the primary raster. -/
inductive DiagramPoint where
  | pointOne
  | pointTwo
  deriving DecidableEq, Fintype, Repr

/-- Which intersection of a concentric contour with the vertical radial axis. -/
inductive RadialSide where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Contour on which each marked point lies, as read from the image. -/
def expectedContourForPoint : DiagramPoint → EquipotentialContour
  | .pointOne => .fiftyVolt
  | .pointTwo => .twentyFiveVolt

/-- Side of the common center on which each marked point lies. -/
def expectedSideForPoint : DiagramPoint → RadialSide
  | .pointOne => .upper
  | .pointTwo => .lower

/-- Literal presentation data transcribed from image `876.png`. -/
structure EquipotentialMapFigure where
  contourShown : EquipotentialContour → Bool
  printedPotentialInVolts : EquipotentialContour → ℝ
  markedPointShown : DiagramPoint → Bool
  markedPointContour : DiagramPoint → EquipotentialContour
  markedPointSide : DiagramPoint → RadialSide
  squareGridShown : Bool
  scaleBarShown : Bool
  printedGridSquareSideCentimeters : ℝ

/--
Independent geometric and physical data for the electrostatic map.

The point-`1` magnitude is an unconstrained physical observable.  It is not
defined from an answer choice or from the desired numerical value.
-/
structure EquipotentialFieldSetup where
  figure : EquipotentialMapFigure
  gridSquareSide : LengthQuantity
  contourRadius : EquipotentialContour → LengthQuantity
  contourPotential : EquipotentialContour → ElectricPotentialQuantity
  contourCurve : EquipotentialContour → Set (EuclideanSpace ℝ (Fin 2))
  contourAxisIntersection :
    EquipotentialContour → RadialSide → EuclideanSpace ℝ (Fin 2)
  commonCenter : EuclideanSpace ℝ (Fin 2)
  upperRadialUnit : EuclideanSpace ℝ (Fin 2)
  pointCoordinate : DiagramPoint → EuclideanSpace ℝ (Fin 2)
  potentialAt : EuclideanSpace ℝ (Fin 2) → ElectricPotentialQuantity
  spatialOrigin : Space 2
  observationTime : Time
  electricField : Electromagnetism.ElectricField 2
  fieldMagnitudeAt : DiagramPoint → ElectricFieldMagnitudeQuantity

/-- Real-valued voltage field in coordinates whose spatial unit is the metre. -/
def potentialVoltageField
    (setup : EquipotentialFieldSetup) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun coordinate => electricPotentialInVolts (setup.potentialAt coordinate)

/-! ## Primary-image evidence and concentric geometry -/

/--
All scalar labels and point associations read from the primary raster.  The
radii are inferred by counting the `1 cm` grid squares from the common center.
No electric-field magnitude occurs in this figure predicate.
-/
structure MatchesPrimaryEquipotentialFigure
    (setup : EquipotentialFieldSetup) : Prop where
  allContoursShown : ∀ contour, setup.figure.contourShown contour = true
  allMarkedPointsShown : ∀ point, setup.figure.markedPointShown point = true
  squareGridShown : setup.figure.squareGridShown = true
  scaleBarShown : setup.figure.scaleBarShown = true
  zeroVoltLabel : setup.figure.printedPotentialInVolts .zeroVolt = 0
  twentyFiveVoltLabel :
    setup.figure.printedPotentialInVolts .twentyFiveVolt = 25
  fiftyVoltLabel : setup.figure.printedPotentialInVolts .fiftyVolt = 50
  hundredVoltLabel : setup.figure.printedPotentialInVolts .hundredVolt = 100
  physicalPotentialsMatchLabels : ∀ contour,
    electricPotentialInVolts (setup.contourPotential contour) =
      setup.figure.printedPotentialInVolts contour
  pointContoursMatchImage : ∀ point,
    setup.figure.markedPointContour point = expectedContourForPoint point
  pointSidesMatchImage : ∀ point,
    setup.figure.markedPointSide point = expectedSideForPoint point
  printedGridScaleIsOneCentimeter :
    setup.figure.printedGridSquareSideCentimeters = 1
  physicalGridScaleMatchesLabel :
    lengthInCentimeters setup.gridSquareSide =
      setup.figure.printedGridSquareSideCentimeters
  zeroVoltRadiusReadout :
    lengthInCentimeters (setup.contourRadius .zeroVolt) = 1 / 2
  twentyFiveVoltRadiusReadout :
    lengthInCentimeters (setup.contourRadius .twentyFiveVolt) = 3 / 2
  fiftyVoltRadiusReadout :
    lengthInCentimeters (setup.contourRadius .fiftyVolt) = 5 / 2
  hundredVoltRadiusReadout :
    lengthInCentimeters (setup.contourRadius .hundredVolt) = 7 / 2

/--
The four dashed curves are concentric circles.  Their upper and lower axial
intersections are obtained by moving the stated radius from the common center.
The two black-dot coordinates are then fixed by their image-read contour and
side associations.
-/
structure SatisfiesConcentricContourGeometry
    (setup : EquipotentialFieldSetup) : Prop where
  upperDirectionIsUnit : ‖setup.upperRadialUnit‖ = 1
  radiiStrictlyNested :
    0 < lengthInMeters (setup.contourRadius .zeroVolt) ∧
      lengthInMeters (setup.contourRadius .zeroVolt) <
        lengthInMeters (setup.contourRadius .twentyFiveVolt) ∧
      lengthInMeters (setup.contourRadius .twentyFiveVolt) <
        lengthInMeters (setup.contourRadius .fiftyVolt) ∧
      lengthInMeters (setup.contourRadius .fiftyVolt) <
        lengthInMeters (setup.contourRadius .hundredVolt)
  upperAxisIntersections : ∀ contour,
    setup.contourAxisIntersection contour .upper =
      setup.commonCenter +
        lengthInMeters (setup.contourRadius contour) • setup.upperRadialUnit
  lowerAxisIntersections : ∀ contour,
    setup.contourAxisIntersection contour .lower =
      setup.commonCenter -
        lengthInMeters (setup.contourRadius contour) • setup.upperRadialUnit
  markedPointCoordinates : ∀ point,
    setup.pointCoordinate point =
      setup.contourAxisIntersection
        (expectedContourForPoint point) (expectedSideForPoint point)

/-- The drawn dashed curves really are level sets of the physical potential. -/
structure RepresentsEquipotentialContours
    (setup : EquipotentialFieldSetup) : Prop where
  axisIntersectionsLieOnContour : ∀ contour side,
    setup.contourAxisIntersection contour side ∈ setup.contourCurve contour
  markedPointsLieOnExpectedContour : ∀ point,
    setup.pointCoordinate point ∈
      setup.contourCurve (expectedContourForPoint point)
  potentialIsConstantOnContour : ∀ contour coordinate,
    coordinate ∈ setup.contourCurve contour →
      setup.potentialAt coordinate = setup.contourPotential contour

/-- Positivity and nondegeneracy conditions for the physical readouts. -/
structure HasPhysicalEquipotentialParameters
    (setup : EquipotentialFieldSetup) : Prop where
  gridSquareSidePositive : 0 < lengthInMeters setup.gridSquareSide
  fieldMagnitudeReadoutsNonnegative : ∀ point,
    0 ≤ electricFieldMagnitudeInVoltsPerMeter (setup.fieldMagnitudeAt point)
  neighboringProbePointsDistinct :
    setup.contourAxisIntersection .hundredVolt .upper ≠
      setup.contourAxisIntersection .twentyFiveVolt .upper

/-! ## Governing electrostatics and contour-map estimate -/

/--
Static electrostatics in metre coordinates: the electric field is the negative
gradient of the scalar electric potential, `E = -∇V`.
-/
structure SatisfiesElectrostaticPotentialLaw
    (setup : EquipotentialFieldSetup) : Prop where
  electricFieldIsNegativePotentialGradient : ∀ coordinate,
    setup.electricField setup.observationTime
        (coordinate +ᵥ setup.spatialOrigin) =
      -gradient (potentialVoltageField setup) coordinate

/--
The dimensionful scalar observable agrees with the norm of the Physlib vector
field at each marked point.
-/
structure CalibratesMarkedPointFieldMagnitudes
    (setup : EquipotentialFieldSetup) : Prop where
  magnitudeMatchesVectorField : ∀ point,
    electricFieldMagnitudeInVoltsPerMeter (setup.fieldMagnitudeAt point) =
      ‖setup.electricField setup.observationTime
        (setup.pointCoordinate point +ᵥ setup.spatialOrigin)‖

/--
Centered equipotential-map estimate at point `1`.  The upper intersections of
the nearest displayed inner and outer contours, `25 V` and `100 V`, bracket
point `1` by one grid square on each side.  The relation is the general
finite-difference estimate `|E| = |ΔV| / Δs`; it contains no answer value.
-/
structure UsesCenteredEquipotentialEstimate
    (setup : EquipotentialFieldSetup) : Prop where
  centeredGradientMagnitude :
    ‖gradient (potentialVoltageField setup)
        (setup.pointCoordinate .pointOne)‖ =
      |electricPotentialInVolts (setup.contourPotential .hundredVolt) -
          electricPotentialInVolts (setup.contourPotential .twentyFiveVolt)| /
        ‖setup.contourAxisIntersection .hundredVolt .upper -
          setup.contourAxisIntersection .twentyFiveVolt .upper‖

/-! ## Answer choices and formalization targets -/

/-- Labels of the four answer choices in the source record. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed number in volts per metre printed beside each answer choice. -/
def AnswerChoice.fieldReadoutInVoltsPerMeter : AnswerChoice → ℝ
  | .A => 1200
  | .B => -1004
  | .C => -2000
  | .D => 3750

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The two neighboring upper contour intersections are `2 cm` apart. -/
lemma centered_probe_separation
    (setup : EquipotentialFieldSetup)
    (_figure : MatchesPrimaryEquipotentialFigure setup)
    (_geometry : SatisfiesConcentricContourGeometry setup) :
    ‖setup.contourAxisIntersection .hundredVolt .upper -
        setup.contourAxisIntersection .twentyFiveVolt .upper‖ = 2 / 100 := by
  have hHundred :
      lengthInMeters (setup.contourRadius .hundredVolt) = 7 / 200 := by
    have h := _figure.hundredVoltRadiusReadout
    simp only [lengthInCentimeters] at h
    linarith
  have hTwentyFive :
      lengthInMeters (setup.contourRadius .twentyFiveVolt) = 3 / 200 := by
    have h := _figure.twentyFiveVoltRadiusReadout
    simp only [lengthInCentimeters] at h
    linarith
  rw [_geometry.upperAxisIntersections, _geometry.upperAxisIntersections]
  rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
    _geometry.upperDirectionIsUnit]
  rw [hHundred, hTwentyFive]
  norm_num

/-- The neighboring contour values span `100 V - 25 V = 75 V`. -/
lemma centered_probe_potential_span
    (setup : EquipotentialFieldSetup)
    (_figure : MatchesPrimaryEquipotentialFigure setup) :
    |electricPotentialInVolts (setup.contourPotential .hundredVolt) -
        electricPotentialInVolts (setup.contourPotential .twentyFiveVolt)| = 75 := by
  rw [_figure.physicalPotentialsMatchLabels,
    _figure.physicalPotentialsMatchLabels, _figure.hundredVoltLabel,
    _figure.twentyFiveVoltLabel]
  norm_num

/--
Before evaluating the labels, the point-`1` magnitude is the centered
potential difference divided by the neighboring-contour separation.
-/
lemma point_one_field_centered_expression
    (setup : EquipotentialFieldSetup)
    (_potentialLaw : SatisfiesElectrostaticPotentialLaw setup)
    (_calibration : CalibratesMarkedPointFieldMagnitudes setup)
    (_estimate : UsesCenteredEquipotentialEstimate setup) :
    electricFieldMagnitudeInVoltsPerMeter
        (setup.fieldMagnitudeAt .pointOne) =
      |electricPotentialInVolts (setup.contourPotential .hundredVolt) -
          electricPotentialInVolts (setup.contourPotential .twentyFiveVolt)| /
        ‖setup.contourAxisIntersection .hundredVolt .upper -
          setup.contourAxisIntersection .twentyFiveVolt .upper‖ := by
  calc
    electricFieldMagnitudeInVoltsPerMeter
        (setup.fieldMagnitudeAt .pointOne) =
        ‖setup.electricField setup.observationTime
          (setup.pointCoordinate .pointOne +ᵥ setup.spatialOrigin)‖ :=
      _calibration.magnitudeMatchesVectorField .pointOne
    _ = ‖-gradient (potentialVoltageField setup)
        (setup.pointCoordinate .pointOne)‖ := by
      rw [_potentialLaw.electricFieldIsNegativePotentialGradient]
    _ = ‖gradient (potentialVoltageField setup)
        (setup.pointCoordinate .pointOne)‖ := norm_neg _
    _ = |electricPotentialInVolts (setup.contourPotential .hundredVolt) -
          electricPotentialInVolts (setup.contourPotential .twentyFiveVolt)| /
        ‖setup.contourAxisIntersection .hundredVolt .upper -
          setup.contourAxisIntersection .twentyFiveVolt .upper‖ :=
      _estimate.centeredGradientMagnitude

/-!
The `75 V` centered potential difference over `2 cm = 0.02 m` gives
`|E(1)| = 75 / 0.02 = 3750 V/m`, which is the dataset's answer D.

This declaration formalizes `thm:physics:phyx_mini_0876:target`.  The target
number occurs only in the answer-choice presentation and the conclusion, never
in a setup field, figure predicate, governing law, or estimate premise.
-/
theorem problem_phyx_mini_0876
    (setup : EquipotentialFieldSetup)
    (_figure : MatchesPrimaryEquipotentialFigure setup)
    (_geometry : SatisfiesConcentricContourGeometry setup)
    (_equipotential : RepresentsEquipotentialContours setup)
    (_physical : HasPhysicalEquipotentialParameters setup)
    (_potentialLaw : SatisfiesElectrostaticPotentialLaw setup)
    (_calibration : CalibratesMarkedPointFieldMagnitudes setup)
    (_estimate : UsesCenteredEquipotentialEstimate setup) :
    electricFieldMagnitudeInVoltsPerMeter
        (setup.fieldMagnitudeAt .pointOne) =
      recordedDatasetAnswer.fieldReadoutInVoltsPerMeter := by
  rw [point_one_field_centered_expression setup _potentialLaw _calibration _estimate,
    centered_probe_potential_span setup _figure,
    centered_probe_separation setup _figure _geometry]
  norm_num [recordedDatasetAnswer, AnswerChoice.fieldReadoutInVoltsPerMeter]

end PhyXMiniProblems.ProblemPhyXMini0876
