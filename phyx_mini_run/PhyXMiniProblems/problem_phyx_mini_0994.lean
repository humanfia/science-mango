import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0994

open Dimension
open scoped BigOperators

/-!
# Electric field at an off-axis point of an electric dipole

The primary raster `994.png` places a `+12 nC` point charge `q₁` and a
`-12 nC` point charge `q₂` on the horizontal axis, `10.0 cm` apart.  Point
`c` lies above their midpoint and is `13.0 cm` from each charge.  Thus each
half of the geometry is a `5`-`12`-`13` triangle.

The image is used as primary evidence here.  In particular, it shows
`E₁` up and to the right, `E₂` down and to the right, and their resultant
`E_c` horizontally rightward.  This corrects the auxiliary prose caption,
which incorrectly calls the resultant downward.

Charges, lengths, and the resultant magnitude are represented by Physlib's
unit-independent `Dimensionful` quantities.  The positions below are
explicit coherent-SI metre readouts, while the components of
`Electromagnetism.ElectricField 2` are interpreted as newtons per coulomb.

Assumption/target split:

* governing laws: the vector point-charge form of Coulomb's law, electric
  field superposition, the school calibration of Coulomb's constant, and the
  relation between the physical magnitude and the norm of the vector field;
* previous-part results: none;
* figure/data readouts: the two signed `12 nC` labels, `0.100 m` separation,
  the `4.0 cm`, `6.0 cm`, and `13.0 cm` segment labels, the point and arrow
  labels, and the symmetric above-axis geometry;
* current target: the total field at `c` is rightward, its magnitude rounds
  to `4.9 * 10^3 N/C`, and B is the unique nearest displayed choice.

No premise fixes the requested numerical field or identifies a physical
field observable with a displayed answer.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the dimension labels in the raster. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the two charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of a field magnitude in newtons per coulomb. -/
def fieldMagnitudeInNewtonsPerCoulomb
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-! ## Figure labels -/

/-- The two point charges named in the problem and raster. -/
inductive SourceCharge where
  | q1
  | q2
  deriving DecidableEq, Fintype, Repr

/-- All five labelled points on the horizontal/vertical diagram. -/
inductive FigurePoint where
  | b
  | q1
  | a
  | q2
  | c
  deriving DecidableEq, Fintype, Repr

/-- The sign glyph printed inside each charge circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Fill colours used to distinguish the two charge signs. -/
inductive FigureChargeColor where
  | red
  | blue
  deriving DecidableEq, Repr

/-- The five distance segments carrying labels or dashed geometry. -/
inductive FigureSegment where
  | bToQ1
  | q1ToA
  | aToQ2
  | q1ToC
  | q2ToC
  deriving DecidableEq, Fintype, Repr

/-- The electric-field arrows explicitly labelled in the supplied image. -/
inductive FigureFieldArrow where
  | Eb
  | Ea
  | E1
  | E2
  | Ec
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions sufficient to transcribe the raster faithfully. -/
inductive FigureArrowDirection where
  | leftward
  | rightward
  | upRight
  | downRight
  deriving DecidableEq, Repr

/-- The three occurrences of the angle label `α` in the image. -/
inductive AlphaMark where
  | atQ1
  | betweenE1AndEc
  | betweenEcAndE2
  deriving DecidableEq, Fintype, Repr

/-- The image point occupied by each physical source charge. -/
def expectedSourcePoint : SourceCharge → FigurePoint
  | .q1 => .q1
  | .q2 => .q2

/-- Signed nanocoulomb value printed beside each source. -/
def expectedChargeInNanocoulombs : SourceCharge → ℝ
  | .q1 => 12
  | .q2 => -12

/-- Sign glyph printed inside each source circle. -/
def expectedChargeSign : SourceCharge → FigureChargeSign
  | .q1 => .plus
  | .q2 => .minus

/-- Colour of each source circle in the raster. -/
def expectedChargeColor : SourceCharge → FigureChargeColor
  | .q1 => .red
  | .q2 => .blue

/-- First endpoint of each dimensioned or dashed segment. -/
def segmentStart : FigureSegment → FigurePoint
  | .bToQ1 => .b
  | .q1ToA => .q1
  | .aToQ2 => .a
  | .q1ToC => .q1
  | .q2ToC => .q2

/-- Second endpoint of each dimensioned or dashed segment. -/
def segmentEnd : FigureSegment → FigurePoint
  | .bToQ1 => .q1
  | .q1ToA => .a
  | .aToQ2 => .q2
  | .q1ToC => .c
  | .q2ToC => .c

/-- Centimetre values literally printed on the five figure segments. -/
def expectedSegmentLengthInCentimeters : FigureSegment → ℝ
  | .bToQ1 => 4
  | .q1ToA => 6
  | .aToQ2 => 4
  | .q1ToC => 13
  | .q2ToC => 13

/-- The point from which each labelled arrow is drawn. -/
def expectedArrowOrigin : FigureFieldArrow → FigurePoint
  | .Eb => .b
  | .Ea => .a
  | .E1 => .c
  | .E2 => .c
  | .Ec => .c

/-- Qualitative arrow directions read directly from the primary raster. -/
def expectedArrowDirection : FigureFieldArrow → FigureArrowDirection
  | .Eb => .leftward
  | .Ea => .rightward
  | .E1 => .upRight
  | .E2 => .downRight
  | .Ec => .rightward

/-- Literal presentation data transcribed from image `994.png`. -/
structure ElectricDipoleFigure where
  xAxisShown : Bool
  yAxisShown : Bool
  pointShown : FigurePoint → Bool
  sourcePoint : SourceCharge → FigurePoint
  sourceSign : SourceCharge → FigureChargeSign
  sourceColor : SourceCharge → FigureChargeColor
  printedChargeNanocoulombs : SourceCharge → ℝ
  segmentShown : FigureSegment → Bool
  segmentIsDashed : FigureSegment → Bool
  printedSegmentLengthCentimeters : FigureSegment → ℝ
  fieldArrowShown : FigureFieldArrow → Bool
  fieldArrowOrigin : FigureFieldArrow → FigurePoint
  fieldArrowDirection : FigureFieldArrow → FigureArrowDirection
  alphaMarkShown : AlphaMark → Bool

/-! ## Independent physical setup -/

/-- Turn a planar `Space 2` point into its explicitly metre-valued vector. -/
def positionVectorInMeters (point : Space 2) : EuclideanSpace ℝ (Fin 2) :=
  !₂[point.val 0, point.val 1]

/-!
Independent physical objects in the dipole setup.  In particular, the source
fields, resultant field, and resultant magnitude are observables, not local
definitions of the requested answer.
-/
structure ElectricDipoleSetup where
  figure : ElectricDipoleFigure
  electromagneticSystem : Electromagnetism.EMSystem
  sourceIsPointCharge : SourceCharge → Bool
  charge : SourceCharge → SignedChargeQuantity
  chargeSeparation : LengthQuantity
  pointPosition : FigurePoint → Space 2
  sourceElectricField : SourceCharge → Electromagnetism.ElectricField 2
  resultantElectricField : Electromagnetism.ElectricField 2
  observationTime : Time
  resultantMagnitudeAtC : ElectricFieldMagnitudeQuantity

/-- Spatial position occupied by a named source charge. -/
def sourcePosition
    (setup : ElectricDipoleSetup) (source : SourceCharge) : Space 2 :=
  setup.pointPosition (setup.figure.sourcePoint source)

/-- Displacement from a source charge to an arbitrary field point, in metres. -/
def displacementFromSourceInMeters
    (setup : ElectricDipoleSetup)
    (source : SourceCharge) (point : Space 2) :
    EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters point - positionVectorInMeters (sourcePosition setup source)

/-- Displacement associated with a labelled segment, in metres. -/
def segmentDisplacementInMeters
    (setup : ElectricDipoleSetup) (segment : FigureSegment) :
    EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters (setup.pointPosition (segmentEnd segment)) -
    positionVectorInMeters (setup.pointPosition (segmentStart segment))

/-- The total electric-field vector at point `c`, in newtons per coulomb. -/
def resultantFieldAtCInNewtonsPerCoulomb
    (setup : ElectricDipoleSetup) : EuclideanSpace ℝ (Fin 2) :=
  setup.resultantElectricField setup.observationTime
    (setup.pointPosition .c)

/-- Norm of the total electric-field vector at point `c`. -/
def resultantFieldNormAtCInNewtonsPerCoulomb
    (setup : ElectricDipoleSetup) : ℝ :=
  ‖resultantFieldAtCInNewtonsPerCoulomb setup‖

/-! ## Scenario and primary-image evidence -/

/-!
The textual problem data: two point charges of equal magnitude and opposite
sign, separated by `0.100 m`.  No electric-field value occurs here.
-/
structure MatchesStatedElectricDipoleScenario
    (setup : ElectricDipoleSetup) : Prop where
  bothSourcesArePointCharges : ∀ source,
    setup.sourceIsPointCharge source = true
  sourceLocations : ∀ source,
    setup.figure.sourcePoint source = expectedSourcePoint source
  printedChargeLabels : ∀ source,
    setup.figure.printedChargeNanocoulombs source =
      expectedChargeInNanocoulombs source
  physicalChargesMatchLabels : ∀ source,
    chargeInNanocoulombs (setup.charge source) =
      setup.figure.printedChargeNanocoulombs source
  statedChargeSeparation :
    lengthInMeters setup.chargeSeparation = 0.100
  positionSeparationMatchesPhysicalLength :
    ‖positionVectorInMeters (sourcePosition setup .q2) -
        positionVectorInMeters (sourcePosition setup .q1)‖ =
      lengthInMeters setup.chargeSeparation

/-!
Primary-image evidence.  The predicate records presentation and geometry only;
the qualitative arrow transcription is not identified with the independently
modeled physical fields.
-/
structure MatchesSuppliedElectricDipoleFigure
    (setup : ElectricDipoleSetup) : Prop where
  horizontalAxisShown : setup.figure.xAxisShown = true
  verticalAxisShown : setup.figure.yAxisShown = true
  allNamedPointsShown : ∀ point, setup.figure.pointShown point = true
  sourceSigns : ∀ source,
    setup.figure.sourceSign source = expectedChargeSign source
  sourceColors : ∀ source,
    setup.figure.sourceColor source = expectedChargeColor source
  allSegmentsShown : ∀ segment,
    setup.figure.segmentShown segment = true
  sourceToCSegmentsDashed :
    setup.figure.segmentIsDashed .q1ToC = true ∧
      setup.figure.segmentIsDashed .q2ToC = true
  horizontalSegmentsSolid :
    setup.figure.segmentIsDashed .bToQ1 = false ∧
      setup.figure.segmentIsDashed .q1ToA = false ∧
      setup.figure.segmentIsDashed .aToQ2 = false
  printedSegmentLabels : ∀ segment,
    setup.figure.printedSegmentLengthCentimeters segment =
      expectedSegmentLengthInCentimeters segment
  segmentGeometryMatchesLabels : ∀ segment,
    100 * ‖segmentDisplacementInMeters setup segment‖ =
      setup.figure.printedSegmentLengthCentimeters segment
  q1AtOrigin :
    positionVectorInMeters (setup.pointPosition .q1) = !₂[0, 0]
  q2OnPositiveXAxis :
    positionVectorInMeters (setup.pointPosition .q2) =
      !₂[lengthInMeters setup.chargeSeparation, 0]
  horizontalPointOrder :
    positionVectorInMeters (setup.pointPosition .b) 0 <
        positionVectorInMeters (setup.pointPosition .q1) 0 ∧
      positionVectorInMeters (setup.pointPosition .q1) 0 <
        positionVectorInMeters (setup.pointPosition .a) 0 ∧
      positionVectorInMeters (setup.pointPosition .a) 0 <
        positionVectorInMeters (setup.pointPosition .q2) 0
  horizontalPointsOnAxis :
    positionVectorInMeters (setup.pointPosition .b) 1 = 0 ∧
      positionVectorInMeters (setup.pointPosition .q1) 1 = 0 ∧
      positionVectorInMeters (setup.pointPosition .a) 1 = 0 ∧
      positionVectorInMeters (setup.pointPosition .q2) 1 = 0
  cAboveAxis : 0 < positionVectorInMeters (setup.pointPosition .c) 1
  cOnPerpendicularBisector :
    positionVectorInMeters (setup.pointPosition .c) 0 =
      (positionVectorInMeters (setup.pointPosition .q1) 0 +
        positionVectorInMeters (setup.pointPosition .q2) 0) / 2
  allFieldArrowsShown : ∀ arrow,
    setup.figure.fieldArrowShown arrow = true
  fieldArrowOrigins : ∀ arrow,
    setup.figure.fieldArrowOrigin arrow = expectedArrowOrigin arrow
  fieldArrowDirections : ∀ arrow,
    setup.figure.fieldArrowDirection arrow = expectedArrowDirection arrow
  allAlphaMarksShown : ∀ mark,
    setup.figure.alphaMarkShown mark = true

/-- Positivity, nonzero-charge, and source-separation conditions. -/
structure HasPhysicalElectricDipoleParameters
    (setup : ElectricDipoleSetup) : Prop where
  separationPositive : 0 < lengthInMeters setup.chargeSeparation
  chargesNonzero : ∀ source,
    chargeInCoulombs (setup.charge source) ≠ 0
  observationSeparatedFromSources : ∀ source,
    0 < ‖displacementFromSourceInMeters setup source
      (setup.pointPosition .c)‖
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Governing electrostatic laws -/

/-!
The rounded Coulomb constant used in the school-level multiple-choice
calculation.  Physlib's `EMSystem.coulombConstant` is the scalar
`1 / (4 π ε₀)` that appears in the Coulomb field law.
-/
structure UsesSchoolCoulombConstant
    (setup : ElectricDipoleSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-!
For source charge `q` and source-to-field-point displacement `r`, the field is
`k q r / ‖r‖³`.  This general all-points law contains no requested result.
-/
structure SatisfiesPointChargeCoulombFieldLaw
    (setup : ElectricDipoleSetup) : Prop where
  fieldOfEachSource : ∀ source time point,
    point ≠ sourcePosition setup source →
      setup.sourceElectricField source time point =
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge source) /
          ‖displacementFromSourceInMeters setup source point‖ ^ 3) •
            displacementFromSourceInMeters setup source point

/-- The total electric field is the vector sum of the two source fields. -/
structure SatisfiesElectricFieldSuperposition
    (setup : ElectricDipoleSetup) : Prop where
  resultantIsSourceSum : ∀ time point,
    setup.resultantElectricField time point =
      ∑ source : SourceCharge, setup.sourceElectricField source time point

/-!
The dimensionful scalar observable is the Euclidean norm of the independently
modeled resultant vector at `c`; no numerical value is fixed here.
-/
structure ResultantMagnitudeRepresentsFieldAtC
    (setup : ElectricDipoleSetup) : Prop where
  magnitudeReadoutAgreesWithVectorNorm :
    fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitudeAtC =
      resultantFieldNormAtCInNewtonsPerCoulomb setup

/-! ## Displayed choices and target relations -/

/-- Labels attached to the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electric-field magnitude in newtons per coulomb printed by each choice. -/
def AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 6.39 * (10 : ℝ) ^ 3
  | .B => 4.9 * (10 : ℝ) ^ 3
  | .C => 8.78 * (10 : ℝ) ^ 3
  | .D => 5.3 * (10 : ℝ) ^ 3

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A vector in the diagram plane points strictly rightward. -/
def IsRightward (field : EuclideanSpace ℝ (Fin 2)) : Prop :=
  0 < field 0 ∧ field 1 = 0

/-- A field magnitude rounds to the displayed nearest `100 N/C`. -/
def RoundsToNearestHundred
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 50

/-- A displayed choice is strictly nearer than every alternative. -/
def IsUniqueNearestDisplayedFieldMagnitude
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - choice.fieldMagnitudeInNewtonsPerCoulomb| <
      |actual - other.fieldMagnitudeInNewtonsPerCoulomb|

/-!
Coulomb's vector law and superposition specialize at `c` to the sum of the
two source expressions.  The right-hand side uses only source data and the
independent electromagnetic-system constant.
-/
lemma resultantFieldAtC_eq_coulombSum
    (setup : ElectricDipoleSetup)
    (_physical : HasPhysicalElectricDipoleParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup) :
    resultantFieldAtCInNewtonsPerCoulomb setup =
      ∑ source : SourceCharge,
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge source) /
          ‖displacementFromSourceInMeters setup source
              (setup.pointPosition .c)‖ ^ 3) •
            displacementFromSourceInMeters setup source
              (setup.pointPosition .c) := by
  rw [resultantFieldAtCInNewtonsPerCoulomb,
    _superposition.resultantIsSourceSum]
  apply Finset.sum_congr rfl
  intro source _
  apply _coulomb.fieldOfEachSource
  intro hpoint
  have hsep :=
    _physical.observationSeparatedFromSources source
  have hzero :
      displacementFromSourceInMeters setup source
          (setup.pointPosition .c) = 0 := by
    simp [displacementFromSourceInMeters, hpoint]
  rw [hzero, norm_zero] at hsep
  exact (lt_irrefl 0 hsep)

/-!
The equal-and-opposite charges and symmetric `5`-`12`-`13` geometry make the
vertical components cancel and the horizontal components add.  With the
school Coulomb constant, the resulting norm lies between `4850 N/C` and
`4950 N/C`.
-/
lemma resultantFieldAtC_direction_and_numericalBounds
    (setup : ElectricDipoleSetup)
    (_scenario : MatchesStatedElectricDipoleScenario setup)
    (_figure : MatchesSuppliedElectricDipoleFigure setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalElectricDipoleParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup) :
    IsRightward (resultantFieldAtCInNewtonsPerCoulomb setup) ∧
      (4850 : ℝ) < resultantFieldNormAtCInNewtonsPerCoulomb setup ∧
      resultantFieldNormAtCInNewtonsPerCoulomb setup < 4950 := by
  have hcharge_q1 :
      chargeInCoulombs (setup.charge .q1) =
        (12 : ℝ) / (10 : ℝ) ^ 9 := by
    have h := _scenario.physicalChargesMatchLabels .q1
    rw [_scenario.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hcharge_q2 :
      chargeInCoulombs (setup.charge .q2) =
        (-12 : ℝ) / (10 : ℝ) ^ 9 := by
    have h := _scenario.physicalChargesMatchLabels .q2
    rw [_scenario.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hdisplacement_q1 :
      displacementFromSourceInMeters setup .q1
          (setup.pointPosition .c) =
        segmentDisplacementInMeters setup .q1ToC := by
    simp [displacementFromSourceInMeters,
      segmentDisplacementInMeters, sourcePosition, segmentStart,
      segmentEnd, _scenario.sourceLocations, expectedSourcePoint]
  have hdisplacement_q2 :
      displacementFromSourceInMeters setup .q2
          (setup.pointPosition .c) =
        segmentDisplacementInMeters setup .q2ToC := by
    simp [displacementFromSourceInMeters,
      segmentDisplacementInMeters, sourcePosition, segmentStart,
      segmentEnd, _scenario.sourceLocations, expectedSourcePoint]
  have hnorm_q1 :
      ‖displacementFromSourceInMeters setup .q1
          (setup.pointPosition .c)‖ = (13 : ℝ) / 100 := by
    rw [hdisplacement_q1]
    have h := _figure.segmentGeometryMatchesLabels .q1ToC
    rw [_figure.printedSegmentLabels] at h
    norm_num [expectedSegmentLengthInCentimeters] at h ⊢
    linarith
  have hnorm_q2 :
      ‖displacementFromSourceInMeters setup .q2
          (setup.pointPosition .c)‖ = (13 : ℝ) / 100 := by
    rw [hdisplacement_q2]
    have h := _figure.segmentGeometryMatchesLabels .q2ToC
    rw [_figure.printedSegmentLabels] at h
    norm_num [expectedSegmentLengthInCentimeters] at h ⊢
    linarith
  have hq2_position :
      positionVectorInMeters (setup.pointPosition .q2) =
        !₂[(1 : ℝ) / 10, 0] := by
    rw [_figure.q2OnPositiveXAxis,
      _scenario.statedChargeSeparation]
    norm_num
  have hc_x :
      positionVectorInMeters (setup.pointPosition .c) 0 =
        (1 : ℝ) / 20 := by
    have h := _figure.cOnPerpendicularBisector
    rw [_figure.q1AtOrigin, hq2_position] at h
    norm_num at h ⊢
    exact h
  have hq1_y :
      positionVectorInMeters (setup.pointPosition .q1) 1 = 0 := by
    rw [_figure.q1AtOrigin]
    norm_num
  have hq2_y :
      positionVectorInMeters (setup.pointPosition .q2) 1 = 0 := by
    rw [hq2_position]
    norm_num
  have hdisplacement_q1_x :
      displacementFromSourceInMeters setup .q1
          (setup.pointPosition .c) 0 = (1 : ℝ) / 20 := by
    simp [displacementFromSourceInMeters, sourcePosition,
      _scenario.sourceLocations, expectedSourcePoint,
      hc_x, _figure.q1AtOrigin]
  have hdisplacement_q2_x :
      displacementFromSourceInMeters setup .q2
          (setup.pointPosition .c) 0 = (-1 : ℝ) / 20 := by
    simp [displacementFromSourceInMeters, sourcePosition,
      _scenario.sourceLocations, expectedSourcePoint,
      hc_x, hq2_position]
    norm_num
  have hdisplacement_q1_y :
      displacementFromSourceInMeters setup .q1
          (setup.pointPosition .c) 1 =
        positionVectorInMeters (setup.pointPosition .c) 1 := by
    simp [displacementFromSourceInMeters, sourcePosition,
      _scenario.sourceLocations, expectedSourcePoint, hq1_y]
  have hdisplacement_q2_y :
      displacementFromSourceInMeters setup .q2
          (setup.pointPosition .c) 1 =
        positionVectorInMeters (setup.pointPosition .c) 1 := by
    simp [displacementFromSourceInMeters, sourcePosition,
      _scenario.sourceLocations, expectedSourcePoint, hq2_y]
  have hcoefficient_q1 :
      setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q1) /
          ‖displacementFromSourceInMeters setup .q1
              (setup.pointPosition .c)‖ ^ 3 =
        (108000000 : ℝ) / 2197 := by
    rw [_constant.coulombConstantCalibration, hcharge_q1,
      hnorm_q1]
    norm_num
  have hcoefficient_q2 :
      setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q2) /
          ‖displacementFromSourceInMeters setup .q2
              (setup.pointPosition .c)‖ ^ 3 =
        (-108000000 : ℝ) / 2197 := by
    rw [_constant.coulombConstantCalibration, hcharge_q2,
      hnorm_q2]
    norm_num
  have hfield := resultantFieldAtC_eq_coulombSum
    setup _physical _coulomb _superposition
  have hfield_x :
      resultantFieldAtCInNewtonsPerCoulomb setup 0 =
        (10800000 : ℝ) / 2197 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 0) hfield
    rw [show (Finset.univ : Finset SourceCharge) =
        {.q1, .q2} by decide] at h
    simp at h
    rw [hcoefficient_q1, hcoefficient_q2,
      hdisplacement_q1_x, hdisplacement_q2_x] at h
    norm_num at h ⊢
    exact h
  have hfield_y :
      resultantFieldAtCInNewtonsPerCoulomb setup 1 = 0 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 1) hfield
    rw [show (Finset.univ : Finset SourceCharge) =
        {.q1, .q2} by decide] at h
    simp at h
    rw [hcoefficient_q1, hcoefficient_q2,
      hdisplacement_q1_y, hdisplacement_q2_y] at h
    linarith
  have hfield_exact :
      resultantFieldAtCInNewtonsPerCoulomb setup =
        !₂[(10800000 : ℝ) / 2197, 0] := by
    ext i
    fin_cases i
    · simpa using hfield_x
    · simpa using hfield_y
  have hnorm :
      resultantFieldNormAtCInNewtonsPerCoulomb setup =
        (10800000 : ℝ) / 2197 := by
    rw [resultantFieldNormAtCInNewtonsPerCoulomb,
      hfield_exact, EuclideanSpace.norm_eq]
    norm_num
  constructor
  · constructor
    · rw [hfield_x]
      norm_num
    · exact hfield_y
  · rw [hnorm]
    constructor <;> norm_num

/-!
The total field at `c` is rightward and has magnitude approximately
`4.9 * 10^3 N/C`.  Therefore B is the unique nearest displayed choice.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0994:target`.
-/
theorem problem_phyx_mini_0994
    (setup : ElectricDipoleSetup)
    (_scenario : MatchesStatedElectricDipoleScenario setup)
    (_figure : MatchesSuppliedElectricDipoleFigure setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalElectricDipoleParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup)
    (_magnitude : ResultantMagnitudeRepresentsFieldAtC setup) :
    IsRightward (resultantFieldAtCInNewtonsPerCoulomb setup) ∧
      (4850 : ℝ) <
        fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitudeAtC ∧
      fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitudeAtC < 4950 ∧
      RoundsToNearestHundred
        (fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitudeAtC)
        recordedDatasetAnswer.fieldMagnitudeInNewtonsPerCoulomb ∧
      IsUniqueNearestDisplayedFieldMagnitude
        (fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitudeAtC)
        recordedDatasetAnswer := by
  rcases resultantFieldAtC_direction_and_numericalBounds
      setup _scenario _figure _constant _physical _coulomb
        _superposition with
    ⟨h_direction, h_lower, h_upper⟩
  rw [_magnitude.magnitudeReadoutAgreesWithVectorNorm]
  refine ⟨h_direction, h_lower, h_upper, ?_, ?_⟩
  · unfold RoundsToNearestHundred
    norm_num [recordedDatasetAnswer,
      AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb]
    rw [abs_lt]
    constructor <;> linarith
  · unfold IsUniqueNearestDisplayedFieldMagnitude
    intro other h_other
    have h_near :
        |resultantFieldNormAtCInNewtonsPerCoulomb setup - 4900| <
          50 := by
      rw [abs_lt]
      constructor <;> linarith
    fin_cases other
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb] at h_other ⊢
      calc
        |resultantFieldNormAtCInNewtonsPerCoulomb setup - 4900| <
            50 := h_near
        _ <
            |resultantFieldNormAtCInNewtonsPerCoulomb setup -
              6390| := by
          rw [abs_of_neg (by linarith)]
          linarith
    · simp [recordedDatasetAnswer] at h_other
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb] at h_other ⊢
      calc
        |resultantFieldNormAtCInNewtonsPerCoulomb setup - 4900| <
            50 := h_near
        _ <
            |resultantFieldNormAtCInNewtonsPerCoulomb setup -
              8780| := by
          rw [abs_of_neg (by linarith)]
          linarith
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb] at h_other ⊢
      calc
        |resultantFieldNormAtCInNewtonsPerCoulomb setup - 4900| <
            50 := h_near
        _ <
            |resultantFieldNormAtCInNewtonsPerCoulomb setup -
              5300| := by
          rw [abs_of_neg (by linarith)]
          linarith

end PhyXMiniProblems.ProblemPhyXMini0994
