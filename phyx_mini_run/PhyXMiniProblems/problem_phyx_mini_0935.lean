import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Area

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0935

open Dimension

/-!
# Induced emf and current in a loop between electromagnet poles

A stationary one-turn conducting loop of area `120 cm² = 0.012 m²` lies in
the uniform field between an electromagnet's poles.  The field magnitude is
increasing at `0.020 T/s`, and the total series resistance of the loop and
meter is `5.0 Ω`.

The primary image shows an upper pole labelled `S`, a lower pole labelled
`N`, upward magnetic-field arrows, an upward displayed area vector, loop
points `a` and `b`, and a leftward current arrow at the visible front of the
loop.  That traversal is clockwise when viewed from above.  We use the drawn
current traversal as the positive sign convention.  Its right-hand normal is
downward, antiparallel to the increasing upward field, so Faraday--Lenz and
Ohm's laws predict positive signed emf and current relative to the arrow.

Assumption/target split:

* governing laws: the field-magnitude profile has the stated derivative; the
  stationary, uniform, single-turn flux rate is the oriented product of area
  and field rate; Faraday's law is `emf = -dΦ/dt`; and the passive series
  circuit obeys `emf = R I`;
* previous-part results: none;
* figure/data readouts: pole labels `S` and `N`, point labels `a` and `b`, the
  upward field and area arrows, the leftward current-reference arrow, the
  connected meter, `0.020 T/s`, `120 cm² = 0.012 m²`, and `5.0 Ω`;
* current conclusions: the induced-emf magnitude is `0.24 mV`, the induced
  current magnitude is `0.048 mA`, the current follows the drawn clockwise
  arrow, and displayed answer choice `B` matches the emf.

No target emf, target current, target direction, or answer label occurs in a
setup, data predicate, physical-parameter predicate, or governing-law field.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Physical dimension `M L² T⁻¹ C⁻²` of electrical resistance. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `M T⁻¹ C⁻¹` of magnetic flux density (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `M T⁻² C⁻¹` of magnetic-flux-density rate. -/
def magneticFluxDensityRateDimension : Dimension :=
  magneticFluxDensityDimension * T𝓭⁻¹

/-- Physical dimension `M L² T⁻² C⁻¹` of magnetic-flux rate. -/
def magneticFluxRateDimension : Dimension :=
  magneticFluxDensityRateDimension * L𝓭 * L𝓭

/-- Physical dimension `M L² T⁻² C⁻¹` of electromotive force. -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `C T⁻¹` of electric current. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent loop area from Physlib's area API. -/
abbrev AreaMagnitude : Type := DimArea

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ElectricalResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density rate. -/
abbrev MagneticFluxDensityRateMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityRateDimension NNReal)

/-- A signed, unit-independent magnetic-flux rate. -/
abbrev SignedMagneticFluxRate : Type :=
  Dimensionful (WithDim magneticFluxRateDimension ℝ)

/-- A signed, unit-independent electromotive force. -/
abbrev ElectromotiveForce : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- A signed, unit-independent electric current. -/
abbrev ElectricCurrent : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- Read physical area in the coherent area unit selected by `units`. -/
def areaReadout (units : UnitChoices) (area : AreaMagnitude) : ℝ :=
  ((area units).val : ℝ)

/-- Read electrical resistance in the coherent unit selected by `units`. -/
def resistanceReadout
    (units : UnitChoices) (resistance : ElectricalResistanceMagnitude) : ℝ :=
  ((resistance units).val : ℝ)

/-- Read magnetic-flux-density magnitude in the selected coherent unit. -/
def magneticFluxDensityReadout
    (units : UnitChoices) (field : MagneticFluxDensityMagnitude) : ℝ :=
  ((field units).val : ℝ)

/-- Read magnetic-flux-density rate in the selected coherent unit. -/
def magneticFluxDensityRateReadout
    (units : UnitChoices) (rate : MagneticFluxDensityRateMagnitude) : ℝ :=
  ((rate units).val : ℝ)

/-- Read signed magnetic-flux rate in the selected coherent unit. -/
def signedMagneticFluxRateReadout
    (units : UnitChoices) (rate : SignedMagneticFluxRate) : ℝ :=
  (rate units).val

/-- Read signed electromotive force in the selected coherent unit. -/
def electromotiveForceReadout
    (units : UnitChoices) (emf : ElectromotiveForce) : ℝ :=
  (emf units).val

/-- Read signed electric current in the selected coherent unit. -/
def electricCurrentReadout
    (units : UnitChoices) (current : ElectricCurrent) : ℝ :=
  (current units).val

/-- Coherent-SI square-metre readout of loop area. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  areaReadout UnitChoices.SI area

/-- Square-centimetre readout used by the printed area label. -/
def areaInSquareCentimeters (area : AreaMagnitude) : ℝ :=
  10000 * areaInSquareMeters area

/-- Coherent-SI ohm readout of total circuit resistance. -/
def resistanceInOhms (resistance : ElectricalResistanceMagnitude) : ℝ :=
  resistanceReadout UnitChoices.SI resistance

/-- Coherent-SI tesla readout of magnetic-flux-density magnitude. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  magneticFluxDensityReadout UnitChoices.SI field

/-- Coherent-SI tesla-per-second readout of field-magnitude rate. -/
def magneticFluxDensityRateInTeslasPerSecond
    (rate : MagneticFluxDensityRateMagnitude) : ℝ :=
  magneticFluxDensityRateReadout UnitChoices.SI rate

/-- Coherent-SI weber-per-second readout of signed magnetic-flux rate. -/
def signedMagneticFluxRateInWebersPerSecond
    (rate : SignedMagneticFluxRate) : ℝ :=
  signedMagneticFluxRateReadout UnitChoices.SI rate

/-- Coherent-SI volt readout of signed electromotive force. -/
def electromotiveForceInVolts (emf : ElectromotiveForce) : ℝ :=
  electromotiveForceReadout UnitChoices.SI emf

/-- Signed millivolt readout relative to the drawn current traversal. -/
def electromotiveForceInMillivolts (emf : ElectromotiveForce) : ℝ :=
  1000 * electromotiveForceInVolts emf

/-- The unsigned emf magnitude requested by the positive answer choices. -/
def electromotiveForceMagnitudeInMillivolts
    (emf : ElectromotiveForce) : ℝ :=
  |electromotiveForceInMillivolts emf|

/-- Coherent-SI ampere readout, signed relative to the drawn arrow. -/
def electricCurrentInAmperes (current : ElectricCurrent) : ℝ :=
  electricCurrentReadout UnitChoices.SI current

/-- Milliampere readout, signed relative to the drawn arrow. -/
def electricCurrentInMilliamperes (current : ElectricCurrent) : ℝ :=
  1000 * electricCurrentInAmperes current

/-- The unsigned current magnitude requested by the problem. -/
def electricCurrentMagnitudeInMilliamperes (current : ElectricCurrent) : ℝ :=
  |electricCurrentInMilliamperes current|

/-! ## Geometry, physical setup, and primary-image vocabulary -/

/-- Labels printed on the two electromagnet pole pieces. -/
inductive MagneticPole where
  | north
  | south
  deriving DecidableEq, Repr

/-- Vertical locations of the two pole pieces in the primary image. -/
inductive PolePosition where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- The two lettered points where the external circuit meets the loop. -/
inductive LoopPoint where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- Vertical directions available to field and area-vector arrows. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Traversal directions at the visible front portion of the loop. -/
inductive LoopTraversalDirection where
  | leftwardAtFront
  | rightwardAtFront
  deriving DecidableEq, Repr

/-- Sense in which a horizontal loop is traversed when viewed from above. -/
inductive LoopSenseFromAbove where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Parallel or antiparallel alignment of two axial directions. -/
inductive AxialAlignment where
  | parallel
  | antiparallel
  deriving DecidableEq, Repr

/-- Topology and conductor count of the depicted loop. -/
inductive LoopTopology where
  | singleTurnClosedConductingLoop
  deriving DecidableEq, Repr

/-- Mechanical state relevant to the motional-emf contribution. -/
inductive LoopMotionModel where
  | stationary
  deriving DecidableEq, Repr

/-- Kind of meter identifiable from the primary image. -/
inductive MeterKind where
  | unmarkedAnalogSeriesMeter
  deriving DecidableEq, Repr

/-- Pole label expected at each location in image `935.png`. -/
def expectedPoleAt : PolePosition → MagneticPole
  | .upper => .south
  | .lower => .north

/-- Right-hand normal generated by a chosen positive loop traversal. -/
def rightHandNormal : LoopTraversalDirection → VerticalDirection
  | .leftwardAtFront => .downward
  | .rightwardAtFront => .upward

/-- View-from-above sense of the traversal shown at the loop's front. -/
def traversalSenseFromAbove : LoopTraversalDirection → LoopSenseFromAbove
  | .leftwardAtFront => .clockwise
  | .rightwardAtFront => .counterclockwise

/-- Whether two vertical axial directions are parallel or antiparallel. -/
def axialAlignment : VerticalDirection → VerticalDirection → AxialAlignment
  | .upward, .upward => .parallel
  | .downward, .downward => .parallel
  | .upward, .downward => .antiparallel
  | .downward, .upward => .antiparallel

/-- Cosine factor for the two axial alignments in this setup. -/
def AxialAlignment.cosine : AxialAlignment → ℝ
  | .parallel => 1
  | .antiparallel => -1

/-!
Literal geometric, presentation, and numerical content transcribed from the
primary raster.  The purple current arrow chooses a sign reference; it does
not assume that the induced current actually follows the arrow.
-/
structure ElectromagneticInductionFigure where
  polePieceShown : PolePosition → Bool
  poleLabelAt : PolePosition → MagneticPole
  conductingLoopShownBetweenPoles : Bool
  loopPointLabelShown : LoopPoint → Bool
  connectedCircuitWireShown : Bool
  connectedMeterShown : Bool
  meterKind : MeterKind
  meterNeedleDeflected : Bool
  fieldArrowsShown : Bool
  fieldArrowDirection : VerticalDirection
  areaVectorShown : Bool
  areaVectorDirection : VerticalDirection
  currentReferenceArrowShown : Bool
  currentReferenceArrowDirection : LoopTraversalDirection
  displayedFieldRateTeslasPerSecond : ℝ
  displayedAreaSquareCentimeters : ℝ
  displayedAreaSquareMeters : ℝ
  displayedTotalResistanceOhms : ℝ

/-!
Independent physical objects and observables.  The Physlib magnetic field,
its dimensionful magnitude profile, induced emf, and induced current are not
defined from numerical answers.
-/
structure InductionLoopSetup where
  topology : LoopTopology
  motionModel : LoopMotionModel
  magneticField : Electromagnetism.MagneticField 3
  upwardUnitVector : EuclideanSpace ℝ (Fin 3)
  loopArea : AreaMagnitude
  totalCircuitResistance : ElectricalResistanceMagnitude
  fieldMagnitudeRate : MagneticFluxDensityRateMagnitude
  magneticFieldMagnitudeAtSeconds : ℝ → MagneticFluxDensityMagnitude
  measurementTimeSeconds : ℝ
  fieldDirection : VerticalDirection
  displayedAreaNormalDirection : VerticalDirection
  currentSignReferenceDirection : LoopTraversalDirection
  signedMagneticFluxRate : SignedMagneticFluxRate
  inducedEmf : ElectromotiveForce
  inducedCurrent : ElectricCurrent
  figure : ElectromagneticInductionFigure

/-! ## Figure readouts, physical calibration, and governing laws -/

/-- Exact labels, arrows, components, and printed values in image `935.png`. -/
structure MatchesPrimaryInductionFigure (setup : InductionLoopSetup) : Prop where
  bothPolePiecesShown : ∀ position, setup.figure.polePieceShown position = true
  poleLabelsMatchImage : ∀ position,
    setup.figure.poleLabelAt position = expectedPoleAt position
  loopIsBetweenPoles : setup.figure.conductingLoopShownBetweenPoles = true
  bothLoopPointLabelsShown : ∀ point,
    setup.figure.loopPointLabelShown point = true
  circuitWireIsShown : setup.figure.connectedCircuitWireShown = true
  connectedMeterIsShown : setup.figure.connectedMeterShown = true
  displayedMeterIsUnmarkedAnalogMeter :
    setup.figure.meterKind = .unmarkedAnalogSeriesMeter
  meterNeedleShowsDeflection : setup.figure.meterNeedleDeflected = true
  upwardFieldArrowsShown :
    setup.figure.fieldArrowsShown = true ∧
      setup.figure.fieldArrowDirection = .upward
  upwardAreaVectorShown :
    setup.figure.areaVectorShown = true ∧
      setup.figure.areaVectorDirection = .upward
  leftwardCurrentReferenceShown :
    setup.figure.currentReferenceArrowShown = true ∧
      setup.figure.currentReferenceArrowDirection = .leftwardAtFront
  displayedFieldRate :
    setup.figure.displayedFieldRateTeslasPerSecond = 20 / 1000
  displayedAreaInSquareCentimeters :
    setup.figure.displayedAreaSquareCentimeters = 120
  displayedAreaInSquareMeters :
    setup.figure.displayedAreaSquareMeters = 12 / 1000
  displayedResistance : setup.figure.displayedTotalResistanceOhms = 5

/-!
Qualitative setup and calibration of independent physical quantities to the
primary-image readouts.  The Physlib field uses coordinates chosen so that
its vector norm is read in teslas.
-/
structure MatchesInductionProblemDescription
    (setup : InductionLoopSetup) : Prop where
  loopIsOneClosedConductingTurn :
    setup.topology = .singleTurnClosedConductingLoop
  loopIsStationary : setup.motionModel = .stationary
  upwardAxisIsUnit : ‖setup.upwardUnitVector‖ = 1
  magneticFieldIsSpatiallyUniform : ∀ time position₁ position₂,
    setup.magneticField time position₁ = setup.magneticField time position₂
  magneticFieldVectorMatchesMagnitudeProfile : ∀ time position,
    setup.magneticField time position =
      magneticFluxDensityInTeslas
          (setup.magneticFieldMagnitudeAtSeconds time.val) •
        setup.upwardUnitVector
  physicalFieldDirectionMatchesArrows :
    setup.fieldDirection = setup.figure.fieldArrowDirection
  physicalAreaNormalMatchesVector :
    setup.displayedAreaNormalDirection = setup.figure.areaVectorDirection
  currentSignReferenceMatchesArrow :
    setup.currentSignReferenceDirection =
      setup.figure.currentReferenceArrowDirection
  fieldRateCalibrated :
    magneticFluxDensityRateInTeslasPerSecond setup.fieldMagnitudeRate =
      setup.figure.displayedFieldRateTeslasPerSecond
  areaCalibratedInSquareCentimeters :
    areaInSquareCentimeters setup.loopArea =
      setup.figure.displayedAreaSquareCentimeters
  areaCalibratedInSquareMeters :
    areaInSquareMeters setup.loopArea = setup.figure.displayedAreaSquareMeters
  resistanceCalibrated :
    resistanceInOhms setup.totalCircuitResistance =
      setup.figure.displayedTotalResistanceOhms

/-- Positivity conditions selecting the ordinary passive-circuit branch. -/
structure HasPhysicalInductionParameters (setup : InductionLoopSetup) : Prop where
  loopAreaPositive : 0 < areaInSquareMeters setup.loopArea
  totalResistancePositive :
    0 < resistanceInOhms setup.totalCircuitResistance
  fieldMagnitudeRatePositive :
    0 < magneticFluxDensityRateInTeslasPerSecond setup.fieldMagnitudeRate

/-!
The governing induction and circuit laws.  The signed flux rate uses the
normal determined by the current sign reference, which is intentionally
distinct from the independently displayed upward area vector.  No requested
emf or current value occurs in these laws.
-/
structure SatisfiesElectromagneticInductionLaws
    (setup : InductionLoopSetup) : Prop where
  fieldMagnitudeHasStatedInstantaneousRate :
    HasDerivAt
      (fun timeSeconds =>
        magneticFluxDensityInTeslas
          (setup.magneticFieldMagnitudeAtSeconds timeSeconds))
      (magneticFluxDensityRateInTeslasPerSecond setup.fieldMagnitudeRate)
      setup.measurementTimeSeconds
  uniformStationarySingleTurnFluxRate :
    signedMagneticFluxRateInWebersPerSecond setup.signedMagneticFluxRate =
      (axialAlignment setup.fieldDirection
          (rightHandNormal setup.currentSignReferenceDirection)).cosine *
        areaInSquareMeters setup.loopArea *
        magneticFluxDensityRateInTeslasPerSecond setup.fieldMagnitudeRate
  faradayLenzLaw :
    electromotiveForceInVolts setup.inducedEmf =
      -signedMagneticFluxRateInWebersPerSecond setup.signedMagneticFluxRate
  passiveSeriesCircuitOhmLaw :
    electromotiveForceInVolts setup.inducedEmf =
      resistanceInOhms setup.totalCircuitResistance *
        electricCurrentInAmperes setup.inducedCurrent

/-! ## Requested quantities, direction, and answer choice -/

/-- The four emf magnitudes, in millivolts, printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Emf magnitude in millivolts printed beside an answer choice. -/
def AnswerChoice.displayedEmfInMillivolts : AnswerChoice → ℝ
  | .A => 45 / 100
  | .B => 24 / 100
  | .C => 54 / 100
  | .D => 23 / 100

/-- Answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A choice matches the independently modeled induced-emf magnitude. -/
def AnswerMatchesInducedEmf
    (setup : InductionLoopSetup) (choice : AnswerChoice) : Prop :=
  electromotiveForceMagnitudeInMillivolts setup.inducedEmf =
    choice.displayedEmfInMillivolts

/-- Positive signed current means motion along the purple reference arrow. -/
def InducedCurrentRunsAlongDrawnArrow (setup : InductionLoopSetup) : Prop :=
  0 < electricCurrentInAmperes setup.inducedCurrent

/-- The induced current follows the clockwise traversal seen from above. -/
def InducedCurrentIsClockwiseViewedFromAbove
    (setup : InductionLoopSetup) : Prop :=
  InducedCurrentRunsAlongDrawnArrow setup ∧
    traversalSenseFromAbove setup.currentSignReferenceDirection = .clockwise

/-!
Blueprint label: `thm:physics:phyx_mini_0935:target`.

The loop has induced-emf magnitude `0.24 mV` and induced-current magnitude
`0.048 mA`.  The positive signed current follows the clockwise purple arrow,
and the recorded answer choice `B` matches the emf.
-/
theorem inducedEmf_and_current_for_supplied_loop
    (setup : InductionLoopSetup)
    (hFigure : MatchesPrimaryInductionFigure setup)
    (hDescription : MatchesInductionProblemDescription setup)
    (hPhysical : HasPhysicalInductionParameters setup)
    (hLaws : SatisfiesElectromagneticInductionLaws setup) :
    electromotiveForceMagnitudeInMillivolts setup.inducedEmf = 24 / 100 ∧
      electricCurrentMagnitudeInMilliamperes setup.inducedCurrent = 48 / 1000 ∧
      InducedCurrentIsClockwiseViewedFromAbove setup ∧
      AnswerMatchesInducedEmf setup recordedDatasetAnswer := by
  have hFieldDirection : setup.fieldDirection = .upward :=
    hDescription.physicalFieldDirectionMatchesArrows.trans
      hFigure.upwardFieldArrowsShown.2
  have hCurrentDirection :
      setup.currentSignReferenceDirection = .leftwardAtFront :=
    hDescription.currentSignReferenceMatchesArrow.trans
      hFigure.leftwardCurrentReferenceShown.2
  have hArea : areaInSquareMeters setup.loopArea = 12 / 1000 :=
    hDescription.areaCalibratedInSquareMeters.trans
      hFigure.displayedAreaInSquareMeters
  have hFieldRate :
      magneticFluxDensityRateInTeslasPerSecond setup.fieldMagnitudeRate =
        20 / 1000 :=
    hDescription.fieldRateCalibrated.trans hFigure.displayedFieldRate
  have hResistance :
      resistanceInOhms setup.totalCircuitResistance = 5 :=
    hDescription.resistanceCalibrated.trans hFigure.displayedResistance
  have hFluxRate :
      signedMagneticFluxRateInWebersPerSecond setup.signedMagneticFluxRate =
        -(24 / 100000 : ℝ) := by
    rw [hLaws.uniformStationarySingleTurnFluxRate, hFieldDirection,
      hCurrentDirection, hArea, hFieldRate]
    norm_num [rightHandNormal, axialAlignment, AxialAlignment.cosine]
  have hEmf :
      electromotiveForceInVolts setup.inducedEmf = 24 / 100000 := by
    rw [hLaws.faradayLenzLaw, hFluxRate]
    norm_num
  have hCurrent :
      electricCurrentInAmperes setup.inducedCurrent = 48 / 1000000 := by
    have hOhm := hLaws.passiveSeriesCircuitOhmLaw
    rw [hEmf, hResistance] at hOhm
    norm_num at hOhm ⊢
    linarith
  have hEmfMagnitude :
      electromotiveForceMagnitudeInMillivolts setup.inducedEmf = 24 / 100 := by
    unfold electromotiveForceMagnitudeInMillivolts
      electromotiveForceInMillivolts
    rw [hEmf]
    norm_num
  have hCurrentMagnitude :
      electricCurrentMagnitudeInMilliamperes setup.inducedCurrent =
        48 / 1000 := by
    unfold electricCurrentMagnitudeInMilliamperes
      electricCurrentInMilliamperes
    rw [hCurrent]
    norm_num
  refine ⟨hEmfMagnitude, hCurrentMagnitude, ?_, ?_⟩
  · constructor
    · unfold InducedCurrentRunsAlongDrawnArrow
      rw [hCurrent]
      norm_num
    · rw [hCurrentDirection]
      rfl
  · simpa [AnswerMatchesInducedEmf, recordedDatasetAnswer,
      AnswerChoice.displayedEmfInMillivolts] using hEmfMagnitude

end PhyXMiniProblems.ProblemPhyXMini0935
