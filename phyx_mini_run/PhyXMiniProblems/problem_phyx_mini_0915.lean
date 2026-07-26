import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0915

open Dimension
open scoped BigOperators

/-!
# Electric-field strength beside an electric dipole

The primary raster `915.png` shows a positive `3.0 nC` point charge above a
negative `-3.0 nC` point charge.  Their vertical separation is `10 cm`, and
the observation dot is `5.0 cm` horizontally to the right of the positive
charge.  The two displayed separation arrows meet at a right angle.

Charges, lengths, positions, Coulomb's constant, and electric-field vectors
are represented by unit-independent Physlib dimensionful quantities.  Real
numbers and real vectors occur only at explicit named-unit readout boundaries
and as literal data printed in the figure or answer choices.  In particular,
the resultant field is an independent physical field of the setup; it is
constrained by Coulomb's law and superposition rather than defined from the
recorded answer.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Coulomb's constant has physical dimension `M L^3 T^-2 C^-2`. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Electric-field strength has physical dimension `M L T^-2 C^-1`. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical length, independent of its readout unit. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A physical position vector in the plane of the figure. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A physical electric-field vector in the plane of the figure. -/
abbrev PlanarElectricFieldQuantity : Type :=
  Dimensionful
    (WithDim electricFieldDimension (EuclideanSpace ℝ (Fin 2)))

/-- A nonnegative dimensionful value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a signed physical charge in nanocoulombs. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Read a planar physical position in coherent-SI metres. -/
def planarPositionInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Regard a dimensionful planar position's SI readout as a Physlib point. -/
def positionAsPhyslibSpace (position : PlanarPositionQuantity) : Space 2 :=
  ⟨fun i => planarPositionInMeters position i⟩

/-- Read a physical planar electric-field vector in newtons per coulomb. -/
def planarElectricFieldInNewtonsPerCoulomb
    (field : PlanarElectricFieldQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (field UnitChoices.SI).val

/-- Read Coulomb's constant in coherent SI `N m^2 / C^2`. -/
def coulombConstantInNewtonMetersSquaredPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-! ## Figure labels and independent electrostatic setup -/

/-- The two source charges distinguished by their vertical positions. -/
inductive ChargeSource where
  | upperPositive
  | lowerNegative
  deriving DecidableEq, Fintype, Repr

/-- All three marked positions in the supplied raster. -/
inductive FigureLocation where
  | upperPositiveCharge
  | lowerNegativeCharge
  | observationDot
  deriving DecidableEq, Fintype, Repr

/-- Regard a source label as the corresponding marked figure location. -/
def ChargeSource.figureLocation : ChargeSource → FigureLocation
  | .upperPositive => .upperPositiveCharge
  | .lowerNegative => .lowerNegativeCharge

/-- The two double-headed distance arrows shown in the raster. -/
inductive DistanceArrow where
  | upperChargeToDot
  | betweenCharges
  deriving DecidableEq, Fintype, Repr

/-- The visual role of a marker at a displayed location. -/
inductive MarkerKind where
  | positivePointCharge
  | negativePointCharge
  | observationDot
  deriving DecidableEq, Repr

/-- Marker colors distinguished in the primary image. -/
inductive MarkerColor where
  | red
  | teal
  | black
  deriving DecidableEq, Repr

/-- The sign glyph printed within a charged circle. -/
inductive ChargeSignGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The qualitative direction of a displayed distance arrow. -/
inductive ArrowOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The source idealization used in the elementary electrostatic model. -/
inductive ElectrostaticSourceModel where
  | stationaryPointCharges
  | other
  deriving DecidableEq, Repr

/-- The medium surrounding the source charges and observation dot. -/
inductive ElectrostaticMedium where
  | vacuum
  | other
  deriving DecidableEq, Repr

/-!
Literal presentation information from image `915.png`.  Its real fields are
unit-labelled printed readouts, not replacements for physical quantities.
There is deliberately no field-strength value in this figure structure.
-/
structure DipoleFieldFigure where
  markerShown : FigureLocation → Bool
  markerKind : FigureLocation → MarkerKind
  markerColor : FigureLocation → MarkerColor
  chargeLabelShown : ChargeSource → Bool
  chargeSignGlyph : ChargeSource → ChargeSignGlyph
  printedChargeNanocoulombs : ChargeSource → ℝ
  distanceArrowShown : DistanceArrow → Bool
  distanceArrowOrientation : DistanceArrow → ArrowOrientation
  printedDistanceCentimeters : DistanceArrow → ℝ
  rightAngleShown : Bool
  containsElectricFieldStrengthLabel : Bool

/-!
A charged source retains both its dimensionful charge and dimensionful planar
position.  This is a physical point-charge object, rather than a transparent
scalar alias for charge.
-/
structure PointChargeSource where
  position : PlanarPositionQuantity
  charge : SignedChargeQuantity

/-!
Independent physical data for the two-charge configuration.  The individual
field contributions and their resultant are independent quantities.  Neither
is manufactured from an answer value.
-/
structure DipoleFieldSetup where
  sourceModel : ElectrostaticSourceModel
  medium : ElectrostaticMedium
  sourcesStationary : Bool
  source : ChargeSource → PointChargeSource
  observationPosition : PlanarPositionQuantity
  horizontalSeparation : LengthQuantity
  verticalSeparation : LengthQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  coulombConstant : CoulombConstantQuantity
  observationTime : Time
  electricField : Electromagnetism.ElectricField 2
  fieldContribution : ChargeSource → PlanarElectricFieldQuantity
  resultantFieldAtDot : PlanarElectricFieldQuantity
  figure : DipoleFieldFigure

/-- Physical position of each marked location. -/
def DipoleFieldSetup.positionAt
    (setup : DipoleFieldSetup) : FigureLocation → PlanarPositionQuantity
  | .upperPositiveCharge => setup.source .upperPositive |>.position
  | .lowerNegativeCharge => setup.source .lowerNegative |>.position
  | .observationDot => setup.observationPosition

/-! ## Assumptions: scenario, figure data, geometry, and governing laws -/

/-- The two sources are stationary point charges in vacuum. -/
structure MatchesWrittenElectrostaticScenario
    (setup : DipoleFieldSetup) : Prop where
  sourcesAreModeledAsStationaryPointCharges :
    setup.sourceModel = .stationaryPointCharges
  surroundingMediumIsVacuum : setup.medium = .vacuum
  sourcesAreStationary : setup.sourcesStationary = true

/-!
Primary-raster evidence and calibration.  The upper red charge is `+3.0 nC`,
the lower teal charge is `-3.0 nC`, the dot is black, and the horizontal and
vertical arrows read `5.0 cm` and `10 cm`.  No resultant-field value or answer
label occurs in this structure.
-/
structure MatchesSuppliedDipoleFieldFigure
    (setup : DipoleFieldSetup) : Prop where
  everyMarkerIsShown : ∀ location,
    setup.figure.markerShown location = true
  upperMarkerIsPositive :
    setup.figure.markerKind .upperPositiveCharge = .positivePointCharge
  lowerMarkerIsNegative :
    setup.figure.markerKind .lowerNegativeCharge = .negativePointCharge
  observationMarkerIsDot :
    setup.figure.markerKind .observationDot = .observationDot
  upperMarkerIsRed : setup.figure.markerColor .upperPositiveCharge = .red
  lowerMarkerIsTeal : setup.figure.markerColor .lowerNegativeCharge = .teal
  observationMarkerIsBlack :
    setup.figure.markerColor .observationDot = .black
  bothChargeLabelsAreShown : ∀ source,
    setup.figure.chargeLabelShown source = true
  upperChargeHasPlusGlyph :
    setup.figure.chargeSignGlyph .upperPositive = .plus
  lowerChargeHasMinusGlyph :
    setup.figure.chargeSignGlyph .lowerNegative = .minus
  printedUpperCharge :
    setup.figure.printedChargeNanocoulombs .upperPositive = 3
  printedLowerCharge :
    setup.figure.printedChargeNanocoulombs .lowerNegative = -3
  chargeLabelsCalibratePhysicalCharges : ∀ source,
    chargeInNanocoulombs (setup.source source).charge =
      setup.figure.printedChargeNanocoulombs source
  bothDistanceArrowsAreShown : ∀ arrow,
    setup.figure.distanceArrowShown arrow = true
  upperChargeToDotArrowIsHorizontal :
    setup.figure.distanceArrowOrientation .upperChargeToDot = .horizontal
  betweenChargesArrowIsVertical :
    setup.figure.distanceArrowOrientation .betweenCharges = .vertical
  printedHorizontalDistance :
    setup.figure.printedDistanceCentimeters .upperChargeToDot = 5
  printedVerticalDistance :
    setup.figure.printedDistanceCentimeters .betweenCharges = 10
  horizontalLabelCalibratesPhysicalSeparation :
    lengthInCentimeters setup.horizontalSeparation =
      setup.figure.printedDistanceCentimeters .upperChargeToDot
  verticalLabelCalibratesPhysicalSeparation :
    lengthInCentimeters setup.verticalSeparation =
      setup.figure.printedDistanceCentimeters .betweenCharges
  displayedArrowsMeetAtRightAngle : setup.figure.rightAngleShown = true
  noFieldStrengthIsPrinted :
    setup.figure.containsElectricFieldStrengthLabel = false

/-!
Cartesian realization of the displayed geometry.  The origin is chosen at
the upper positive charge, the positive `x`-axis points toward the dot, and
the positive `y`-axis points upward.  Thus the lower negative charge has
vertical coordinate `-10 cm`.  These equations express only figure geometry.
-/
structure UsesDisplayedRightAngleGeometry
    (setup : DipoleFieldSetup) : Prop where
  upperChargeX :
    planarPositionInMeters (setup.source .upperPositive).position 0 = 0
  upperChargeY :
    planarPositionInMeters (setup.source .upperPositive).position 1 = 0
  lowerChargeX :
    planarPositionInMeters (setup.source .lowerNegative).position 0 = 0
  lowerChargeY :
    planarPositionInMeters (setup.source .lowerNegative).position 1 =
      -lengthInMeters setup.verticalSeparation
  observationX :
    planarPositionInMeters setup.observationPosition 0 =
      lengthInMeters setup.horizontalSeparation
  observationY :
    planarPositionInMeters setup.observationPosition 1 = 0

/-- Positivity and non-collision conditions for the physical configuration. -/
structure HasPhysicalElectrostaticParameters
    (setup : DipoleFieldSetup) : Prop where
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparation
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparation
  vacuumPermittivityPositive : 0 < setup.electromagneticSystem.ε₀
  coulombConstantPositive :
    0 < coulombConstantInNewtonMetersSquaredPerCoulombSquared
      setup.coulombConstant
  everySourceChargeNonzero : ∀ source,
    chargeInCoulombs (setup.source source).charge ≠ 0
  noSourceAtObservationPoint : ∀ source,
    planarPositionInMeters setup.observationPosition ≠
      planarPositionInMeters (setup.source source).position

/-!
The dimensionful Coulomb constant is linked to Physlib's electromagnetic
system and calibrated to the rounded textbook value
`9.0 * 10^9 N m^2/C^2`.  This contains no field-strength answer.
-/
structure UsesTextbookVacuumCoulombConstant
    (setup : DipoleFieldSetup) : Prop where
  dimensionfulConstantAgreesWithElectromagneticSystem :
    coulombConstantInNewtonMetersSquaredPerCoulombSquared
        setup.coulombConstant =
      setup.electromagneticSystem.coulombConstant
  textbookRoundedCalibration :
    setup.electromagneticSystem.coulombConstant = (9 : ℝ) * 10 ^ 9

/-!
The vector point-charge law is

`E = k q (r - r_source) / ‖r - r_source‖^3`.

The second field states linear superposition, and the third connects the
independent dimensionful resultant to Physlib's electric field at the
observation event.  These are general laws and contain no numerical
resultant, rounding interval, or answer choice.
-/
structure SatisfiesPointChargeCoulombLawAndSuperposition
    (setup : DipoleFieldSetup) : Prop where
  contributionFromPointCharge : ∀ source,
    planarElectricFieldInNewtonsPerCoulomb
        (setup.fieldContribution source) =
      let displacement :=
        planarPositionInMeters setup.observationPosition -
          planarPositionInMeters (setup.source source).position
      (coulombConstantInNewtonMetersSquaredPerCoulombSquared
            setup.coulombConstant *
          chargeInCoulombs (setup.source source).charge /
          ‖displacement‖ ^ 3) • displacement
  superpositionAtObservationDot :
    planarElectricFieldInNewtonsPerCoulomb
        setup.resultantFieldAtDot =
      ∑ source : ChargeSource,
        planarElectricFieldInNewtonsPerCoulomb
          (setup.fieldContribution source)
  agreesWithPhyslibElectricFieldAtObservation :
    planarElectricFieldInNewtonsPerCoulomb
        setup.resultantFieldAtDot =
      setup.electricField setup.observationTime
        (positionAsPhyslibSpace setup.observationPosition)

/-! ## Requested strength and displayed answer choices -/

/-- Magnitude of the resultant field at the dot, in newtons per coulomb. -/
def resultantFieldStrengthInNewtonsPerCoulomb
    (setup : DipoleFieldSetup) : ℝ :=
  ‖planarElectricFieldInNewtonsPerCoulomb
      setup.resultantFieldAtDot‖

/-- Labels of the four answer choices supplied with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The field strength printed for each choice, in newtons per coulomb. -/
def AnswerChoice.displayedFieldStrengthInNewtonsPerCoulomb :
    AnswerChoice → ℝ
  | .A => (13 : ℝ) / 10 * 10 ^ 3
  | .B => (53 : ℝ) / 10 * 10 ^ 3
  | .C => (10 : ℝ) / 10 * 10 ^ 4
  | .D => (35 : ℝ) / 10 * 10 ^ 3

/-- Resolution implied by the two significant digits printed in each choice. -/
def AnswerChoice.displayedResolutionInNewtonsPerCoulomb :
    AnswerChoice → ℝ
  | .A => 10 ^ 2
  | .B => 10 ^ 2
  | .C => 10 ^ 3
  | .D => 10 ^ 2

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A value rounds to a display at the stated positive resolution. -/
def RoundsToNearestResolution
    (value displayed resolution : ℝ) : Prop :=
  0 < resolution ∧
    displayed - resolution / 2 ≤ value ∧
    value < displayed + resolution / 2

/-- A choice displays the resultant field strength at its printed precision. -/
def AnswerMatchesResultantFieldStrength
    (setup : DipoleFieldSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestResolution
    (resultantFieldStrengthInNewtonsPerCoulomb setup)
    choice.displayedFieldStrengthInNewtonsPerCoulomb
    choice.displayedResolutionInNewtonsPerCoulomb

/-- A choice is the unique displayed answer matching the modeled strength. -/
def IsUniqueMatchingAnswer
    (setup : DipoleFieldSetup) (choice : AnswerChoice) : Prop :=
  AnswerMatchesResultantFieldStrength setup choice ∧
    ∀ other,
      AnswerMatchesResultantFieldStrength setup other → other = choice

/-!
The two vector contributions give a resultant strength between `9500` and
`10500 N/C`.  This is a derived numerical statement, not a premise.
-/
lemma resultantFieldStrength_rounding_bounds
    (setup : DipoleFieldSetup)
    (hFigure : MatchesSuppliedDipoleFieldFigure setup)
    (hGeometry : UsesDisplayedRightAngleGeometry setup)
    (hPhysical : HasPhysicalElectrostaticParameters setup)
    (hConstant : UsesTextbookVacuumCoulombConstant setup)
    (hCoulomb : SatisfiesPointChargeCoulombLawAndSuperposition setup) :
    9500 ≤ resultantFieldStrengthInNewtonsPerCoulomb setup ∧
      resultantFieldStrengthInNewtonsPerCoulomb setup < 10500 := by
  have hLengthUnits (length : LengthQuantity) :
      lengthInMeters length =
        (1 / 100 : ℝ) * lengthInCentimeters length := by
    let ucm : UnitChoices :=
      {UnitChoices.SI with length := LengthUnit.centimeters}
    let um : UnitChoices :=
      {UnitChoices.SI with length := LengthUnit.meters}
    have hScale :
        ucm.dimScale um L𝓭 =
          (⟨1 / 100, by norm_num⟩ : NNReal) := by
      norm_num [ucm, um, UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters]
    have hUnits :=
      congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
        (length.2 ucm um)
    rw [show dim (WithDim L𝓭 NNReal) = L𝓭 by rfl, hScale] at hUnits
    dsimp [um, ucm] at hUnits
    norm_num at hUnits
    exact hUnits
  have hHorizontal :
      lengthInMeters setup.horizontalSeparation = (1 : ℝ) / 20 := by
    rw [hLengthUnits,
      hFigure.horizontalLabelCalibratesPhysicalSeparation,
      hFigure.printedHorizontalDistance]
    norm_num
  have hVertical :
      lengthInMeters setup.verticalSeparation = (1 : ℝ) / 10 := by
    rw [hLengthUnits,
      hFigure.verticalLabelCalibratesPhysicalSeparation,
      hFigure.printedVerticalDistance]
    norm_num
  have hUpperCharge :
      chargeInCoulombs (setup.source .upperPositive).charge =
        (3 : ℝ) / 1000000000 := by
    have h :=
      hFigure.chargeLabelsCalibratePhysicalCharges .upperPositive
    rw [hFigure.printedUpperCharge] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have hLowerCharge :
      chargeInCoulombs (setup.source .lowerNegative).charge =
        -(3 : ℝ) / 1000000000 := by
    have h :=
      hFigure.chargeLabelsCalibratePhysicalCharges .lowerNegative
    rw [hFigure.printedLowerCharge] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have hConstantValue :
      coulombConstantInNewtonMetersSquaredPerCoulombSquared
          setup.coulombConstant =
        (9 : ℝ) * 10 ^ 9 := by
    calc
      coulombConstantInNewtonMetersSquaredPerCoulombSquared
          setup.coulombConstant =
          setup.electromagneticSystem.coulombConstant :=
        hConstant.dimensionfulConstantAgreesWithElectromagneticSystem
      _ = (9 : ℝ) * 10 ^ 9 := hConstant.textbookRoundedCalibration
  have hUpperDisplacement :
      planarPositionInMeters setup.observationPosition -
          planarPositionInMeters (setup.source .upperPositive).position =
        !₂[(1 : ℝ) / 20, 0] := by
    ext i
    fin_cases i <;>
      simp [hGeometry.observationX, hGeometry.observationY,
        hGeometry.upperChargeX, hGeometry.upperChargeY, hHorizontal]
  have hLowerDisplacement :
      planarPositionInMeters setup.observationPosition -
          planarPositionInMeters (setup.source .lowerNegative).position =
        !₂[(1 : ℝ) / 20, (1 : ℝ) / 10] := by
    ext i
    fin_cases i <;>
      simp [hGeometry.observationX, hGeometry.observationY,
        hGeometry.lowerChargeX, hGeometry.lowerChargeY, hHorizontal,
        hVertical]
  have hUpperNorm :
      ‖(!₂[(1 : ℝ) / 20, 0] :
          EuclideanSpace ℝ (Fin 2))‖ = (1 : ℝ) / 20 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hLowerNorm :
      ‖(!₂[(1 : ℝ) / 20, (1 : ℝ) / 10] :
          EuclideanSpace ℝ (Fin 2))‖ =
        Real.sqrt 5 / 20 := by
    have hNormSq :
        ‖(!₂[(1 : ℝ) / 20, (1 : ℝ) / 10] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
          (1 : ℝ) / 80 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
    have hSqrtSq : (Real.sqrt (5 : ℝ)) ^ 2 = 5 :=
      Real.sq_sqrt (by norm_num)
    have hNormNonnegative :
        0 ≤ ‖(!₂[(1 : ℝ) / 20, (1 : ℝ) / 10] :
          EuclideanSpace ℝ (Fin 2))‖ := norm_nonneg _
    have hSqrtNonnegative : 0 ≤ Real.sqrt (5 : ℝ) :=
      Real.sqrt_nonneg _
    nlinarith
  have hSourceSum
      (f : ChargeSource → EuclideanSpace ℝ (Fin 2)) :
      ∑ source : ChargeSource, f source =
        f .upperPositive + f .lowerNegative := by
    rw [show (Finset.univ : Finset ChargeSource) =
      {.upperPositive, .lowerNegative} by decide]
    simp
  have hUpperField :=
    hCoulomb.contributionFromPointCharge .upperPositive
  dsimp at hUpperField
  rw [hUpperDisplacement, hUpperNorm, hConstantValue,
    hUpperCharge] at hUpperField
  have hLowerField :=
    hCoulomb.contributionFromPointCharge .lowerNegative
  dsimp at hLowerField
  rw [hLowerDisplacement, hLowerNorm, hConstantValue,
    hLowerCharge] at hLowerField
  have hField := hCoulomb.superpositionAtObservationDot
  rw [hSourceSum, hUpperField, hLowerField] at hField
  have hSqrtSq : (Real.sqrt (5 : ℝ)) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hSqrtPositive : 0 < Real.sqrt (5 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hFieldComponents :
      planarElectricFieldInNewtonsPerCoulomb
          setup.resultantFieldAtDot =
        !₂[10800 - 432 * Real.sqrt 5, -864 * Real.sqrt 5] := by
    rw [hField]
    ext i
    fin_cases i <;> simp <;> field_simp <;> nlinarith
  have hResultantNormSq :
      resultantFieldStrengthInNewtonsPerCoulomb setup ^ 2 =
        (10800 - 432 * Real.sqrt 5) ^ 2 +
          (-864 * Real.sqrt 5) ^ 2 := by
    rw [resultantFieldStrengthInNewtonsPerCoulomb,
      hFieldComponents, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, Fin.sum_univ_two, sq_abs]
  have hSqrtLower : (2 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtUpper : Real.sqrt 5 < (9 : ℝ) / 4 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hNormSqLower :
      (9500 : ℝ) ^ 2 <
        resultantFieldStrengthInNewtonsPerCoulomb setup ^ 2 := by
    rw [hResultantNormSq]
    nlinarith [hSqrtSq]
  have hNormSqUpper :
      resultantFieldStrengthInNewtonsPerCoulomb setup ^ 2 <
        (10500 : ℝ) ^ 2 := by
    rw [hResultantNormSq]
    nlinarith [hSqrtSq]
  have hNormNonnegative :
      0 ≤ resultantFieldStrengthInNewtonsPerCoulomb setup :=
    norm_nonneg _
  constructor <;> nlinarith

/-!
At the observation dot, Coulomb's vector law and superposition give a field
strength of approximately 1.0 * 10^4 N/C, uniquely matching answer C at the
precision printed by the source.

This declaration formalizes blueprint label
thm:physics:phyx_mini_0915:target. Neither the rounded strength, choice C,
nor the rounding interval occurs in a physical premise.
-/
theorem problem_phyx_mini_0915
    (setup : DipoleFieldSetup)
    (hScenario : MatchesWrittenElectrostaticScenario setup)
    (hFigure : MatchesSuppliedDipoleFieldFigure setup)
    (hGeometry : UsesDisplayedRightAngleGeometry setup)
    (hPhysical : HasPhysicalElectrostaticParameters setup)
    (hConstant : UsesTextbookVacuumCoulombConstant setup)
    (hCoulomb : SatisfiesPointChargeCoulombLawAndSuperposition setup) :
    RoundsToNearestResolution
        (resultantFieldStrengthInNewtonsPerCoulomb setup)
        ((10 : ℝ) / 10 * 10 ^ 4) (10 ^ 3) ∧
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  have hBounds := resultantFieldStrength_rounding_bounds
    setup hFigure hGeometry hPhysical hConstant hCoulomb
  have hRounded :
      RoundsToNearestResolution
        (resultantFieldStrengthInNewtonsPerCoulomb setup)
        ((10 : ℝ) / 10 * 10 ^ 4) (10 ^ 3) := by
    norm_num [RoundsToNearestResolution]
    exact hBounds
  refine ⟨hRounded, ?_⟩
  unfold IsUniqueMatchingAnswer
  constructor
  · simpa [AnswerMatchesResultantFieldStrength, recordedDatasetAnswer,
      AnswerChoice.displayedFieldStrengthInNewtonsPerCoulomb,
      AnswerChoice.displayedResolutionInNewtonsPerCoulomb] using hRounded
  · intro other hOther
    fin_cases other
    · exfalso
      norm_num [AnswerMatchesResultantFieldStrength,
        RoundsToNearestResolution,
        AnswerChoice.displayedFieldStrengthInNewtonsPerCoulomb,
        AnswerChoice.displayedResolutionInNewtonsPerCoulomb] at hOther
      linarith [hBounds.1]
    · exfalso
      norm_num [AnswerMatchesResultantFieldStrength,
        RoundsToNearestResolution,
        AnswerChoice.displayedFieldStrengthInNewtonsPerCoulomb,
        AnswerChoice.displayedResolutionInNewtonsPerCoulomb] at hOther
      linarith [hBounds.1]
    · rfl
    · exfalso
      norm_num [AnswerMatchesResultantFieldStrength,
        RoundsToNearestResolution,
        AnswerChoice.displayedFieldStrengthInNewtonsPerCoulomb,
        AnswerChoice.displayedResolutionInNewtonsPerCoulomb] at hOther
      linarith [hBounds.1]

end PhyXMiniProblems.ProblemPhyXMini0915
