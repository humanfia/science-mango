import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0938

open Dimension

/-!
# Induced electric field around a long solenoid

The supplied panel `(a)` shows a circular wire loop and galvanometer surrounding
the blue magnetic-field region of a long solenoid.  The solenoid has `500`
turns per metre, cross-sectional area `4.0 cm²`, and winding-current increase
rate `100 A/s`.  The observation circle has radius `2.0 cm`.

Physical magnitudes are represented by Physlib's unit-covariant
`Dimensionful (WithDim ...)` types.  Real numbers occur only at explicitly
named coherent-SI readout boundaries.  The full electric and magnetic fields
retain Physlib's spacetime-dependent vector-field types.

Assumption/target split:

* governing laws: the ideal long-solenoid field-rate law, uniform-flux law,
  Faraday's signed induction law, and the circular line-integral law;
* previous-part results: none;
* figure/data readouts: the apparatus geometry, labels and arrow directions,
  the four numerical problem parameters, the textbook value of vacuum
  permeability, and the displayed multiple-choice values;
* current target conclusion: the induced electric-field magnitude is
  `2 * 10⁻⁴ V/m`, hence displayed choice `B`.

No premise states the requested electric-field value or the combined formula
from which that value is obtained.
-/

/-! ## Dimensions, physical quantities, and coherent-SI readouts -/

/-- Electric current has dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- A current-change rate has dimension `C T⁻²`. -/
def electricCurrentRateDimension : Dimension :=
  electricCurrentDimension * T𝓭⁻¹

/-- Turns per unit length have inverse-length dimension `L⁻¹`. -/
def turnDensityDimension : Dimension :=
  L𝓭⁻¹

/-- Area has dimension `L²`. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A magnetic-flux-density change rate has dimension `M T⁻² C⁻¹`. -/
def magneticFluxDensityRateDimension : Dimension :=
  magneticFluxDensityDimension * T𝓭⁻¹

/-- Magnetic flux has dimension `M L² T⁻¹ C⁻¹`. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Magnetic-flux rate and electromotive force have dimension
`M L² T⁻² C⁻¹`. -/
def electromotiveForceDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Electric field has dimension `M L T⁻² C⁻¹`, equivalently volts per metre. -/
def electricFieldDimension : Dimension :=
  electromotiveForceDimension * L𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative winding-current magnitude. -/
abbrev CurrentMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative winding-current increase rate. -/
abbrev CurrentIncreaseRateQuantity : Type :=
  Dimensionful (WithDim electricCurrentRateDimension NNReal)

/-- A nonnegative number of solenoid turns per unit length. -/
abbrev TurnDensityQuantity : Type :=
  Dimensionful (WithDim turnDensityDimension NNReal)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative magnetic-flux-density increase rate. -/
abbrev MagneticFluxDensityIncreaseRateQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityRateDimension NNReal)

/-- Signed magnetic-flux change rate relative to the selected area normal. -/
abbrev SignedMagneticFluxRateQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Signed electric-field circulation relative to the selected loop orientation. -/
abbrev SignedElectricCirculationQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Signed tangential component of electric field on the circular loop. -/
abbrev SignedElectricFieldQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension ℝ)

/-- Nonnegative magnitude of electric field on the circular loop. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension NNReal)

/-- Read a length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read an area in coherent-SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a winding current in coherent-SI amperes. -/
def currentInAmperes (current : CurrentMagnitudeQuantity) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Read a winding-current increase rate in coherent-SI amperes per second. -/
def currentIncreaseRateInAmperesPerSecond
    (rate : CurrentIncreaseRateQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-- Read solenoid turn density in coherent-SI turns per metre. -/
def turnDensityInTurnsPerMeter (density : TurnDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read magnetic-flux density in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read magnetic-flux-density increase rate in teslas per second. -/
def magneticFluxDensityIncreaseRateInTeslasPerSecond
    (rate : MagneticFluxDensityIncreaseRateQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-- Read signed magnetic-flux rate in coherent-SI webers per second. -/
def magneticFluxRateInWebersPerSecond
    (rate : SignedMagneticFluxRateQuantity) : ℝ :=
  (rate UnitChoices.SI).val

/-- Read signed electric-field circulation in coherent-SI volts. -/
def electricCirculationInVolts
    (circulation : SignedElectricCirculationQuantity) : ℝ :=
  (circulation UnitChoices.SI).val

/-- Read a signed tangential electric field in coherent-SI volts per metre. -/
def signedElectricFieldInVoltsPerMeter
    (field : SignedElectricFieldQuantity) : ℝ :=
  (field UnitChoices.SI).val

/-- Read electric-field magnitude in coherent-SI volts per metre. -/
def electricFieldMagnitudeInVoltsPerMeter
    (field : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-! ## Figure vocabulary and independent apparatus -/

/-- Dimensionless spatial direction vectors in physical three-space. -/
abbrev DirectionVector : Type := EuclideanSpace ℝ (Fin 3)

/-- A selected unit vector along the solenoid axis and blue cylinder. -/
def solenoidAxisUnitVector : DirectionVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Physical objects visible in the primary raster `938.png`. -/
inductive FigureObject where
  | solenoid
  | blueMagneticFieldCylinder
  | wireLoop
  | galvanometer
  | leftWindingLead
  | rightWindingLead
  deriving DecidableEq, Fintype, Repr

/-- Symbolic or textual labels visible in panel `(a)`. -/
inductive FigureLabel where
  | panelA
  | solenoidText
  | blueCylinderFieldText
  | wireLoopText
  | galvanometerText
  | galvanometerG
  | windingCurrentI
  | windingCurrentRateDIOverDt
  | magneticFieldB
  | crossSectionA
  | inducedCurrentIPrime
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions in the oblique drawing plane. -/
inductive DiagramDirection where
  | upward
  | downward
  | alongSolenoidAxis
  deriving DecidableEq, Repr

/-- Literal, non-numerical presentation data from `938.png`. -/
structure SolenoidLoopFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  wireLoopSurroundsBlueCylinder : Bool
  galvanometerInsertedInWireLoop : Bool
  blueCylinderMarksMagneticFieldRegion : Bool
  inducedCurrentArrowOnLeftSideOfLoop : Bool
  leftLeadCurrentArrowDirection : DiagramDirection
  rightLeadCurrentArrowDirection : DiagramDirection
  inducedCurrentArrowDirection : DiagramDirection
  magneticFieldArrowDirection : DiagramDirection

/-- Idealization selected by the prose description. -/
inductive ApparatusModel where
  | longSolenoidWithEncirclingCircularLoop
  | other
  deriving DecidableEq, Repr

/-!
Independent physical observables.  In particular, the induced electric-field
magnitude is not defined from the solenoid parameters or an answer choice.
-/
structure SolenoidInductionSetup where
  apparatusModel : ApparatusModel
  electromagneticSystem : Electromagnetism.EMSystem
  magneticField : Electromagnetism.MagneticField 3
  inducedElectricField : Electromagnetism.ElectricField 3
  observationTime : Time
  solenoidInterior : Set (Space 3)
  wireLoopPath : Set (Space 3)
  positiveAxisDirection : DirectionVector
  positiveLoopTangentAt : Space 3 → DirectionVector
  windingCurrentAt : Time → CurrentMagnitudeQuantity
  windingCurrentIncreaseRateAt : Time → CurrentIncreaseRateQuantity
  solenoidTurnsPerLength : TurnDensityQuantity
  solenoidCrossSectionArea : AreaQuantity
  magneticFluxDensityAt : Time → MagneticFluxDensityQuantity
  magneticFluxDensityIncreaseRateAt :
    Time → MagneticFluxDensityIncreaseRateQuantity
  loopRadius : LengthQuantity
  loopCircumference : LengthQuantity
  magneticFluxChangeRateAt : Time → SignedMagneticFluxRateQuantity
  inducedElectricCirculationAt : Time → SignedElectricCirculationQuantity
  signedTangentialElectricFieldAt : Time → SignedElectricFieldQuantity
  inducedElectricFieldMagnitudeAt : Time → ElectricFieldMagnitudeQuantity
  figure : SolenoidLoopFigure

/-! ## Scenario, figure evidence, data, and governing laws -/

/-- Prose-level apparatus and geometry, excluding all answer-bearing values. -/
structure MatchesLongSolenoidLoopScenario
    (setup : SolenoidInductionSetup) : Prop where
  longSolenoidAndCircularLoop :
    setup.apparatusModel = .longSolenoidWithEncirclingCircularLoop
  positiveAxisAgreesWithFigure :
    setup.positiveAxisDirection = solenoidAxisUnitVector
  solenoidInteriorNonempty : setup.solenoidInterior.Nonempty
  wireLoopPathNonempty : setup.wireLoopPath.Nonempty
  wireLoopLiesOutsideSolenoid :
    ∀ point ∈ setup.wireLoopPath, point ∉ setup.solenoidInterior

/-- Literal object, label, and arrow evidence read from the primary raster. -/
structure MatchesSuppliedSolenoidLoopFigure
    (setup : SolenoidInductionSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  loopSurroundsFieldCylinder :
    setup.figure.wireLoopSurroundsBlueCylinder = true
  galvanometerIsInLoop :
    setup.figure.galvanometerInsertedInWireLoop = true
  blueCylinderIsFieldRegion :
    setup.figure.blueCylinderMarksMagneticFieldRegion = true
  inducedCurrentArrowIsOnLeft :
    setup.figure.inducedCurrentArrowOnLeftSideOfLoop = true
  leftLeadArrowPointsUp :
    setup.figure.leftLeadCurrentArrowDirection = .upward
  rightLeadArrowPointsDown :
    setup.figure.rightLeadCurrentArrowDirection = .downward
  inducedCurrentArrowPointsDown :
    setup.figure.inducedCurrentArrowDirection = .downward
  magneticFieldArrowFollowsAxis :
    setup.figure.magneticFieldArrowDirection = .alongSolenoidAxis

/-- Positivity and nondegeneracy of the independent physical parameters. -/
structure HasPhysicalSolenoidLoopParameters
    (setup : SolenoidInductionSetup) : Prop where
  vacuumPermeabilityPositive : 0 < setup.electromagneticSystem.μ₀
  turnDensityPositive :
    0 < turnDensityInTurnsPerMeter setup.solenoidTurnsPerLength
  crossSectionAreaPositive :
    0 < areaInSquareMeters setup.solenoidCrossSectionArea
  currentIsIncreasing :
    0 < currentIncreaseRateInAmperesPerSecond
      (setup.windingCurrentIncreaseRateAt setup.observationTime)
  loopRadiusPositive : 0 < lengthInMeters setup.loopRadius
  loopCircumferencePositive : 0 < lengthInMeters setup.loopCircumference

/-!
The numerical values supplied by the text, converted at the explicit SI
readout boundary: `4 cm² = 4 / 10⁴ m²` and `2 cm = 2 / 100 m`.
-/
structure HasStatedSolenoidLoopData
    (setup : SolenoidInductionSetup) : Prop where
  turnsPerMeter :
    turnDensityInTurnsPerMeter setup.solenoidTurnsPerLength = 500
  crossSectionAreaInSquareMeters :
    areaInSquareMeters setup.solenoidCrossSectionArea = (4 : ℝ) / 10 ^ 4
  currentIncreaseRateInSI :
    currentIncreaseRateInAmperesPerSecond
        (setup.windingCurrentIncreaseRateAt setup.observationTime) = 100
  loopRadiusInMeters :
    lengthInMeters setup.loopRadius = (2 : ℝ) / 100

/-- Textbook coherent-SI calibration of vacuum permeability. -/
structure HasTextbookVacuumPermeability
    (setup : SolenoidInductionSetup) : Prop where
  permeabilityInSI :
    setup.electromagneticSystem.μ₀ = 4 * Real.pi / 10 ^ 7

/-!
Circular-loop geometry.  This relation mentions neither electric nor magnetic
fields and does not choose an answer value.
-/
structure SatisfiesCircularLoopGeometry
    (setup : SolenoidInductionSetup) : Prop where
  circumferenceLaw :
    lengthInMeters setup.loopCircumference =
      2 * Real.pi * lengthInMeters setup.loopRadius
  tangentIsUnit : ∀ point ∈ setup.wireLoopPath,
    ‖setup.positiveLoopTangentAt point‖ = 1

/-!
Ideal long-solenoid law.  The vector field is uniform inside the blue cylinder
and negligible outside; its scalar increase rate is `μ₀ n dI/dt`.  This law
does not mention flux, circulation, loop radius, or induced electric field.
-/
structure SatisfiesLongSolenoidFieldLaw
    (setup : SolenoidInductionSetup) : Prop where
  uniformInteriorField : ∀ time point,
    point ∈ setup.solenoidInterior →
      setup.magneticField time point =
        magneticFluxDensityInTeslas (setup.magneticFluxDensityAt time) •
          setup.positiveAxisDirection
  negligibleExteriorField : ∀ time point,
    point ∉ setup.solenoidInterior → setup.magneticField time point = 0
  fieldIncreaseRateLaw : ∀ time,
    magneticFluxDensityIncreaseRateInTeslasPerSecond
        (setup.magneticFluxDensityIncreaseRateAt time) =
      setup.electromagneticSystem.μ₀ *
        turnDensityInTurnsPerMeter setup.solenoidTurnsPerLength *
        currentIncreaseRateInAmperesPerSecond
          (setup.windingCurrentIncreaseRateAt time)

/-!
Because the wire loop encloses the whole blue solenoid cross-section, the flux
rate is the uniform interior field rate times the solenoid area.  The law does
not mention electric field or loop circumference.
-/
structure SatisfiesUniformSolenoidFluxLaw
    (setup : SolenoidInductionSetup) : Prop where
  loopEnclosesWholeSolenoidCrossSection :
    setup.figure.wireLoopSurroundsBlueCylinder = true
  fluxRateLaw : ∀ time,
    magneticFluxRateInWebersPerSecond
        (setup.magneticFluxChangeRateAt time) =
      magneticFluxDensityIncreaseRateInTeslasPerSecond
          (setup.magneticFluxDensityIncreaseRateAt time) *
        areaInSquareMeters setup.solenoidCrossSectionArea

/-!
Faraday's signed law for the chosen positive surface normal and boundary
orientation.  It does not mention the solenoid parameters or field magnitude.
-/
structure SatisfiesFaradayInductionLaw
    (setup : SolenoidInductionSetup) : Prop where
  faradayLaw : ∀ time,
    electricCirculationInVolts (setup.inducedElectricCirculationAt time) =
      -magneticFluxRateInWebersPerSecond
        (setup.magneticFluxChangeRateAt time)

/-!
Rotational symmetry makes the induced electric field tangential and constant
in signed component on the circular path.  The circulation is circumference
times that component, while the requested magnitude is its absolute value.
No numerical answer occurs in this law.
-/
structure SatisfiesCircularInducedElectricFieldLaw
    (setup : SolenoidInductionSetup) : Prop where
  fieldIsTangentialOnLoop : ∀ time point,
    point ∈ setup.wireLoopPath →
      setup.inducedElectricField time point =
        signedElectricFieldInVoltsPerMeter
            (setup.signedTangentialElectricFieldAt time) •
          setup.positiveLoopTangentAt point
  circulationLaw : ∀ time,
    electricCirculationInVolts (setup.inducedElectricCirculationAt time) =
      lengthInMeters setup.loopCircumference *
        signedElectricFieldInVoltsPerMeter
          (setup.signedTangentialElectricFieldAt time)
  magnitudeLaw : ∀ time,
    electricFieldMagnitudeInVoltsPerMeter
        (setup.inducedElectricFieldMagnitudeAt time) =
      |signedElectricFieldInVoltsPerMeter
        (setup.signedTangentialElectricFieldAt time)|

/-! ## Displayed choices and requested conclusion -/

/-- Answer labels printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed electric-field magnitude for each choice, in volts per metre. -/
def AnswerChoice.displayedElectricFieldInVoltsPerMeter :
    AnswerChoice → ℝ
  | .A => (22 : ℝ) / 10 ^ 5
  | .B => (2 : ℝ) / 10 ^ 4
  | .C => (1 : ℝ) / 10 ^ 4
  | .D => (26 : ℝ) / 10 ^ 5

/-- Answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
At the `2 cm` loop, the induced electric-field magnitude is
`2 * 10⁻⁴ V/m`, so the matching displayed and recorded answer is `B`.

This declaration formalizes `thm:physics:phyx_mini_0938:target`.  The numeric
field conclusion occurs only here and among the independently transcribed
answer-choice readouts, never in a governing-law or setup premise.
-/
theorem problem_phyx_mini_0938
    (setup : SolenoidInductionSetup)
    (hScenario : MatchesLongSolenoidLoopScenario setup)
    (hFigure : MatchesSuppliedSolenoidLoopFigure setup)
    (hPhysical : HasPhysicalSolenoidLoopParameters setup)
    (hData : HasStatedSolenoidLoopData setup)
    (hPermeability : HasTextbookVacuumPermeability setup)
    (hGeometry : SatisfiesCircularLoopGeometry setup)
    (hSolenoid : SatisfiesLongSolenoidFieldLaw setup)
    (hFlux : SatisfiesUniformSolenoidFluxLaw setup)
    (hFaraday : SatisfiesFaradayInductionLaw setup)
    (hCircularField : SatisfiesCircularInducedElectricFieldLaw setup) :
    electricFieldMagnitudeInVoltsPerMeter
        (setup.inducedElectricFieldMagnitudeAt setup.observationTime) =
        (2 : ℝ) / 10 ^ 4 ∧
      electricFieldMagnitudeInVoltsPerMeter
          (setup.inducedElectricFieldMagnitudeAt setup.observationTime) =
        AnswerChoice.B.displayedElectricFieldInVoltsPerMeter ∧
      recordedDatasetAnswer = .B := by
  have hFieldRate :=
    hSolenoid.fieldIncreaseRateLaw setup.observationTime
  rw [hPermeability.permeabilityInSI, hData.turnsPerMeter,
    hData.currentIncreaseRateInSI] at hFieldRate
  norm_num at hFieldRate
  have hFluxRate :=
    hFlux.fluxRateLaw setup.observationTime
  rw [hFieldRate, hData.crossSectionAreaInSquareMeters] at hFluxRate
  norm_num at hFluxRate
  have hFaradayLaw :=
    hFaraday.faradayLaw setup.observationTime
  rw [hFluxRate] at hFaradayLaw
  have hCircumference := hGeometry.circumferenceLaw
  rw [hData.loopRadiusInMeters] at hCircumference
  norm_num at hCircumference
  have hCirculation :=
    hCircularField.circulationLaw setup.observationTime
  rw [hFaradayLaw, hCircumference] at hCirculation
  have hSignedField :
      signedElectricFieldInVoltsPerMeter
          (setup.signedTangentialElectricFieldAt setup.observationTime) =
        -(1 : ℝ) / 5000 := by
    apply mul_left_cancel₀ (ne_of_gt Real.pi_pos)
    nlinarith [hCirculation]
  have hMagnitude :=
    hCircularField.magnitudeLaw setup.observationTime
  rw [hSignedField] at hMagnitude
  norm_num at hMagnitude
  constructor
  · rw [hMagnitude]
    norm_num
  constructor
  · rw [hMagnitude]
    norm_num [AnswerChoice.displayedElectricFieldInVoltsPerMeter]
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0938
