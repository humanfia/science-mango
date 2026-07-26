import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0917

open Dimension

/-!
# Current induced in a loop between electromagnet poles

A stationary one-turn conducting loop of area `120 cm² = 0.012 m²` is placed
between the poles of an electromagnet.  The field is spatially uniform and its
magnitude is increasing at `0.020 T/s`.  The total resistance of the loop and
meter is `5.0 Ω`.

The primary raster shows the lower pole labelled `N`, the upper pole labelled
`S`, upward field arrows and an upward area vector.  Its purple leftward
current arrow is used only to choose the positive sign of current.  The
right-hand normal belonging to that traversal is downward, so the signed flux
relative to the current reference is decreasing while the field magnitude is
increasing.

Assumption/target split:

* governing laws: the displayed field-magnitude waveform has the stated time
  derivative, uniform-loop flux is `B A` with the appropriate orientation
  sign, Faraday's law is `emf = -dΦ/dt`, and Ohm's law is `emf = R I`;
* previous-part results: none;
* figure/data readouts: pole labels `S` and `N`, loop-point labels `a` and `b`,
  upward field arrows, the upward area vector, the leftward current sign
  reference, the connected meter, `0.020 T/s`, `120 cm² = 0.012 m²`, and
  `5.0 Ω`;
* current targets: the induced signed current is `+0.048 mA`, hence it runs
  along the drawn reference arrow and answer choice `C` matches.

No target current value or target direction occurs in a setup, figure,
description, parameter, or law field below.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- Physical dimension `L²` of loop area. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Physical dimension `M L² T⁻¹ C⁻²` of electrical resistance. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `M T⁻¹ C⁻¹` of magnetic flux density. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `M T⁻² C⁻¹` of a magnetic-flux-density rate. -/
def magneticFluxDensityRateDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `M L² T⁻² C⁻¹` of magnetic-flux rate. -/
def magneticFluxRateDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `M L² T⁻² C⁻¹` of electromotive force. -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `C T⁻¹` of electric current. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaMagnitude : Type :=
  Dimensionful (WithDim areaDimension NNReal)

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

/-- Read a physical area in the coherent area unit selected by `units`. -/
def areaReadout (units : UnitChoices) (area : AreaMagnitude) : ℝ :=
  ((area units).val : ℝ)

/-- Read resistance in the coherent resistance unit selected by `units`. -/
def resistanceReadout
    (units : UnitChoices) (resistance : ElectricalResistanceMagnitude) : ℝ :=
  ((resistance units).val : ℝ)

/-- Read magnetic flux density in the coherent unit selected by `units`. -/
def magneticFluxDensityReadout
    (units : UnitChoices) (field : MagneticFluxDensityMagnitude) : ℝ :=
  ((field units).val : ℝ)

/-- Read magnetic-flux-density rate in the coherent unit selected by `units`. -/
def magneticFluxDensityRateReadout
    (units : UnitChoices) (rate : MagneticFluxDensityRateMagnitude) : ℝ :=
  ((rate units).val : ℝ)

/-- Read signed magnetic-flux rate in the coherent unit selected by `units`. -/
def signedMagneticFluxRateReadout
    (units : UnitChoices) (rate : SignedMagneticFluxRate) : ℝ :=
  (rate units).val

/-- Read electromotive force in the coherent unit selected by `units`. -/
def electromotiveForceReadout
    (units : UnitChoices) (emf : ElectromotiveForce) : ℝ :=
  (emf units).val

/-- Read signed electric current in the coherent unit selected by `units`. -/
def electricCurrentReadout
    (units : UnitChoices) (current : ElectricCurrent) : ℝ :=
  (current units).val

/-- Coherent-SI square-metre readout of loop area. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  areaReadout UnitChoices.SI area

/-- Square-centimetre readout used in the printed area label. -/
def areaInSquareCentimeters (area : AreaMagnitude) : ℝ :=
  10000 * areaInSquareMeters area

/-- Coherent-SI ohm readout of resistance. -/
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

/-- Coherent-SI volt readout of electromotive force. -/
def electromotiveForceInVolts (emf : ElectromotiveForce) : ℝ :=
  electromotiveForceReadout UnitChoices.SI emf

/-- Coherent-SI ampere readout, signed relative to the drawn arrow. -/
def electricCurrentInAmperes (current : ElectricCurrent) : ℝ :=
  electricCurrentReadout UnitChoices.SI current

/-- Milliampere readout, signed relative to the drawn arrow. -/
def electricCurrentInMilliamperes (current : ElectricCurrent) : ℝ :=
  1000 * electricCurrentInAmperes current

/-! ## Geometry, figure labels, and sign conventions -/

/-- Labels printed on the two electromagnet pole pieces. -/
inductive MagneticPole where
  | north
  | south
  deriving DecidableEq, Repr

/-- Vertical locations of the two pole pieces in the primary raster. -/
inductive PolePosition where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- The two lettered points where the external circuit meets the loop. -/
inductive LoopPoint where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- Vertical directions available to the field and area-vector arrows. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Traversal directions at the visible front part of the loop. -/
inductive LoopTraversalDirection where
  | leftwardAtFront
  | rightwardAtFront
  deriving DecidableEq, Repr

/-- Parallel or antiparallel alignment of two axial directions. -/
inductive AxialAlignment where
  | parallel
  | antiparallel
  deriving DecidableEq, Repr

/-- Topology and conductor count of the loop shown in the problem. -/
inductive LoopTopology where
  | singleTurnClosedConductingLoop
  deriving DecidableEq, Repr

/-- Mechanical state relevant to the motional-emf term. -/
inductive LoopMotionModel where
  | stationary
  deriving DecidableEq, Repr

/-- Spatial idealization stated for the field at each instant. -/
inductive FieldSpatialUniformity where
  | uniformAtEachTime
  deriving DecidableEq, Repr

/-- Kind of meter connected into the single series circuit. -/
inductive MeterKind where
  | currentMeter
  deriving DecidableEq, Repr

/-- Pole label expected at each vertical location in image `917.png`. -/
def expectedPoleAt : PolePosition → MagneticPole
  | .upper => .south
  | .lower => .north

/-- Right-hand normal generated by a chosen positive loop traversal. -/
def rightHandNormal : LoopTraversalDirection → VerticalDirection
  | .leftwardAtFront => .downward
  | .rightwardAtFront => .upward

/-- Whether two vertical axial directions are parallel or antiparallel. -/
def axialAlignment : VerticalDirection → VerticalDirection → AxialAlignment
  | .upward, .upward => .parallel
  | .downward, .downward => .parallel
  | .upward, .downward => .antiparallel
  | .downward, .upward => .antiparallel

/-- Cosine factor for the only two alignments appearing in this problem. -/
def AxialAlignment.cosine : AxialAlignment → ℝ
  | .parallel => 1
  | .antiparallel => -1

/-!
Literal geometric and numerical content transcribed from the primary raster.
The purple arrow chooses the positive current sign; it does not assert which
way the induced current actually flows.
-/
structure ElectromagneticInductionFigure where
  polePieceShown : PolePosition → Bool
  poleLabelAt : PolePosition → MagneticPole
  conductingLoopShownBetweenPoles : Bool
  loopPointLabelShown : LoopPoint → Bool
  connectedMeterShown : Bool
  meterKind : MeterKind
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
Independent physical objects and observables.  In particular, induced emf and
current are not defined from any answer choice or numerical target.
-/
structure InductionLoopSetup where
  topology : LoopTopology
  motionModel : LoopMotionModel
  fieldUniformity : FieldSpatialUniformity
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

/-! ## Problem data, figure evidence, and governing laws -/

/-- Exact labels, arrows, components, and printed values in image `917.png`. -/
structure MatchesPrimaryInductionFigure (setup : InductionLoopSetup) : Prop where
  bothPolePiecesShown : ∀ position, setup.figure.polePieceShown position = true
  poleLabelsMatchImage : ∀ position,
    setup.figure.poleLabelAt position = expectedPoleAt position
  loopIsBetweenPoles : setup.figure.conductingLoopShownBetweenPoles = true
  bothLoopPointLabelsShown : ∀ point,
    setup.figure.loopPointLabelShown point = true
  connectedMeterIsShown : setup.figure.connectedMeterShown = true
  displayedMeterIsCurrentMeter : setup.figure.meterKind = .currentMeter
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

/-- Qualitative setup and calibration of physical quantities to raster data. -/
structure MatchesInductionProblemDescription (setup : InductionLoopSetup) : Prop where
  loopIsOneClosedConductingTurn :
    setup.topology = .singleTurnClosedConductingLoop
  loopIsStationary : setup.motionModel = .stationary
  fieldIsUniformAtEachTime : setup.fieldUniformity = .uniformAtEachTime
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
Faraday induction and the series-circuit constitutive law.  The flux-rate law
uses the normal determined by the current sign reference, which is distinct
from the independently displayed upward area vector.
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
  faradayLaw :
    electromotiveForceInVolts setup.inducedEmf =
      -signedMagneticFluxRateInWebersPerSecond setup.signedMagneticFluxRate
  seriesCircuitOhmLaw :
    electromotiveForceInVolts setup.inducedEmf =
      resistanceInOhms setup.totalCircuitResistance *
        electricCurrentInAmperes setup.inducedCurrent

/-! ## Requested signed current and answer choice -/

/-- The four signed milliampere answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed current in milliamperes printed beside an answer choice. -/
def AnswerChoice.displayedCurrentInMilliamperes : AnswerChoice → ℝ
  | .A => 24 / 1000
  | .B => -(24 / 1000)
  | .C => 48 / 1000
  | .D => -(48 / 1000)

/-- Answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice matches the independently modeled induced current. -/
def AnswerMatchesInducedCurrent
    (setup : InductionLoopSetup) (choice : AnswerChoice) : Prop :=
  electricCurrentInMilliamperes setup.inducedCurrent =
    choice.displayedCurrentInMilliamperes

/-- Positive signed current means motion along the purple reference arrow. -/
def InducedCurrentRunsAlongDrawnArrow (setup : InductionLoopSetup) : Prop :=
  0 < electricCurrentInAmperes setup.inducedCurrent

/-!
Blueprint label: `thm:physics:phyx_mini_0917:target`.

The induced current is `+0.048 mA` relative to the purple leftward arrow, so
the physical current follows that arrow and the recorded choice `C` matches.
-/
theorem inducedCurrent_is_zeroPointZeroFourEightMilliamperes
    (setup : InductionLoopSetup)
    (hFigure : MatchesPrimaryInductionFigure setup)
    (hDescription : MatchesInductionProblemDescription setup)
    (hPhysical : HasPhysicalInductionParameters setup)
    (hLaws : SatisfiesElectromagneticInductionLaws setup) :
    electricCurrentInMilliamperes setup.inducedCurrent = 48 / 1000 ∧
      InducedCurrentRunsAlongDrawnArrow setup ∧
      AnswerMatchesInducedCurrent setup recordedDatasetAnswer := by
  have hFieldDirection : setup.fieldDirection = .upward := by
    rw [hDescription.physicalFieldDirectionMatchesArrows]
    exact hFigure.upwardFieldArrowsShown.2
  have hReferenceDirection :
      setup.currentSignReferenceDirection = .leftwardAtFront := by
    rw [hDescription.currentSignReferenceMatchesArrow]
    exact hFigure.leftwardCurrentReferenceShown.2
  have hArea : areaInSquareMeters setup.loopArea = 12 / 1000 :=
    hDescription.areaCalibratedInSquareMeters.trans
      hFigure.displayedAreaInSquareMeters
  have hRate :
      magneticFluxDensityRateInTeslasPerSecond setup.fieldMagnitudeRate =
        20 / 1000 :=
    hDescription.fieldRateCalibrated.trans hFigure.displayedFieldRate
  have hResistance :
      resistanceInOhms setup.totalCircuitResistance = 5 :=
    hDescription.resistanceCalibrated.trans hFigure.displayedResistance
  have hFlux := hLaws.uniformStationarySingleTurnFluxRate
  rw [hFieldDirection, hReferenceDirection, hArea, hRate] at hFlux
  norm_num [rightHandNormal, axialAlignment, AxialAlignment.cosine] at hFlux
  have hEmf := hLaws.faradayLaw
  rw [hFlux] at hEmf
  norm_num at hEmf
  have hOhm := hLaws.seriesCircuitOhmLaw
  rw [hEmf, hResistance] at hOhm
  have hCurrent :
      electricCurrentInAmperes setup.inducedCurrent = 48 / 1000000 := by
    norm_num at hOhm ⊢
    linarith
  constructor
  · unfold electricCurrentInMilliamperes
    rw [hCurrent]
    norm_num
  constructor
  · unfold InducedCurrentRunsAlongDrawnArrow
    rw [hCurrent]
    norm_num
  · unfold AnswerMatchesInducedCurrent recordedDatasetAnswer
      AnswerChoice.displayedCurrentInMilliamperes
    unfold electricCurrentInMilliamperes
    rw [hCurrent]
    norm_num

end PhyXMiniProblems.ProblemPhyXMini0917
