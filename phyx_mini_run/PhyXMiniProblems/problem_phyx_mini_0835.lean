import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0835

open Dimension

/-!
# Axial electric field of a uniformly charged thin rod

The primary image shows a horizontal thin rod with uniformly spaced positive
charge marks.  Its total length is labelled `L`.  The point `P` lies to the
right on the rod's axis, and the arrow labelled `r` starts at the rod's
midpoint and ends at `P`.  Thus `r` is a center-to-point distance, despite the
auxiliary caption's reference to the nearest end.  This reading is also the
one consistent with the recorded answer.

The rod occupies `[-L/2, L/2]` in an axial metre coordinate and has constant
linear charge density.  Coulomb superposition determines the field magnitude
at `P` by integrating the contribution of every charged element.  The
dimensionful quantities below are unit-independent Physlib quantities; real
numbers are used only for named-unit readouts, axial coordinate readouts, and
the printed numerical answers.

Assumption/target split:

* governing laws: constant line density, total-charge accounting, axial
  Coulomb superposition, and consistency between the magnitude and Physlib's
  spacetime-dependent electric vector field;
* previous-part results: none;
* figure/data readouts: a thin uniformly positively charged rod, the `L` arrow
  between endpoints, the center-to-`P` arrow `r`, `L = 5.0 cm`, `r = 3.0 cm`,
  `Q = 3.0 nC`, and the vacuum Coulomb-constant calibration;
* target conclusions: the finite-rod closed form, rounding of the field to
  `9.8 * 10^4 N/C`, and unique selection of answer D.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The dimension `C L⁻¹` of linear electric-charge density. -/
def linearChargeDensityDimension : Dimension := C𝓭 * L𝓭⁻¹

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L³ T⁻² C⁻²` of Coulomb's constant. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent linear charge density. -/
abbrev LinearChargeDensityQuantity : Type :=
  Dimensionful (WithDim linearChargeDensityDimension NNReal)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative, dimensionful value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used for the two printed length data. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- SI coulomb readout of a physical charge magnitude. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Nanocoulomb readout used by the printed total charge. -/
def chargeInNanocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  10 ^ 9 * chargeInCoulombs charge

/-- SI readout of linear charge density, in coulombs per metre. -/
def linearChargeDensityInCoulombsPerMeter
    (density : LinearChargeDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- SI readout of electric-field strength, in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- SI readout of Coulomb's constant, in newton-square-metres per coulomb squared. -/
def coulombConstantInNewtonSquareMetersPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-! ## Rod, field, and primary-image vocabulary -/

/-- The thin rod together with its independent charge observables. -/
structure ThinUniformChargedRod where
  totalLength : LengthQuantity
  totalCharge : ChargeMagnitudeQuantity
  linearChargeDensity : LinearChargeDensityQuantity

/-- Named axial markers appearing in, or geometrically determined by, the image. -/
inductive RodAxisMarker where
  | leftEndpoint
  | center
  | rightEndpoint
  | pointP
  deriving DecidableEq, Fintype, Repr

/-- Features explicitly visible in the supplied image `835.png`. -/
inductive FigureFeature where
  | thinHorizontalRod
  | uniformlySpacedPositiveChargeMarks
  | lengthArrow
  | lengthLabelL
  | observationPoint
  | pointLabelP
  | distanceArrow
  | distanceLabelR
  deriving DecidableEq, Fintype, Repr

/-!
The axial coordinates are explicit metre readouts of a schematic coordinate
chart.  The two label quantities themselves remain dimensionful.
-/
structure ChargedRodFigure where
  shows : FigureFeature → Bool
  axialCoordinateInMeters : RodAxisMarker → ℝ
  lengthArrowStart : RodAxisMarker
  lengthArrowEnd : RodAxisMarker
  distanceArrowStart : RodAxisMarker
  distanceArrowEnd : RodAxisMarker
  pointLabelMarker : RodAxisMarker
  lengthLabelQuantity : LengthQuantity
  distanceLabelQuantity : LengthQuantity

/-!
The independent physical apparatus and observables.  In particular, neither
the electric-field magnitude nor the vector field is defined from a displayed
answer choice.
-/
structure AxialChargedRodSetup where
  rod : ThinUniformChargedRod
  centerToPointDistance : LengthQuantity
  electricFieldMagnitudeAtP : ElectricFieldStrengthQuantity
  coulombConstant : CoulombConstantQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  observationPointP : Space 3
  positiveAxisDirection : EuclideanSpace ℝ (Fin 3)
  figure : ChargedRodFigure

/-! ## Figure evidence, problem data, and physical calibration -/

/-!
Primary-image transcription.  Crucially, the `r` arrow starts at the rod
center and ends at `P`; no electric-field value or answer label occurs here.
-/
structure MatchesPrimaryChargedRodFigure
    (setup : AxialChargedRodSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature, setup.figure.shows feature = true
  lengthArrowStartsAtLeftEndpoint :
    setup.figure.lengthArrowStart = .leftEndpoint
  lengthArrowEndsAtRightEndpoint :
    setup.figure.lengthArrowEnd = .rightEndpoint
  distanceArrowStartsAtRodCenter :
    setup.figure.distanceArrowStart = .center
  distanceArrowEndsAtP :
    setup.figure.distanceArrowEnd = .pointP
  printedPointLabelIsP :
    setup.figure.pointLabelMarker = .pointP
  lengthLabelDenotesRodLength :
    setup.figure.lengthLabelQuantity = setup.rod.totalLength
  distanceLabelDenotesCenterToPointDistance :
    setup.figure.distanceLabelQuantity = setup.centerToPointDistance
  rodCenterIsCoordinateOrigin :
    setup.figure.axialCoordinateInMeters .center = 0
  leftEndpointAtMinusHalfLength :
    setup.figure.axialCoordinateInMeters .leftEndpoint =
      -(lengthInMeters setup.rod.totalLength / 2)
  rightEndpointAtHalfLength :
    setup.figure.axialCoordinateInMeters .rightEndpoint =
      lengthInMeters setup.rod.totalLength / 2
  pointPAtPositiveCenterDistance :
    setup.figure.axialCoordinateInMeters .pointP =
      lengthInMeters setup.centerToPointDistance

/-- Numerical data stated in the question, retaining both printed and SI readouts. -/
structure MatchesChargedRodProblemData
    (setup : AxialChargedRodSetup) : Prop where
  rodLengthCentimeters :
    lengthInCentimeters setup.rod.totalLength = 5
  pointDistanceCentimeters :
    lengthInCentimeters setup.centerToPointDistance = 3
  totalChargeNanocoulombs :
    chargeInNanocoulombs setup.rod.totalCharge = 3
  rodLengthMeters :
    lengthInMeters setup.rod.totalLength = 5 / 100
  pointDistanceMeters :
    lengthInMeters setup.centerToPointDistance = 3 / 100
  totalChargeCoulombs :
    chargeInCoulombs setup.rod.totalCharge = 3 / 10 ^ 9

/-- Positivity and separation assumptions selecting the depicted external point. -/
structure HasPhysicalChargedRodParameters
    (setup : AxialChargedRodSetup) : Prop where
  rodLengthPositive :
    0 < lengthInMeters setup.rod.totalLength
  totalChargePositive :
    0 < chargeInCoulombs setup.rod.totalCharge
  linearChargeDensityPositive :
    0 < linearChargeDensityInCoulombsPerMeter setup.rod.linearChargeDensity
  pointPOutsideRightEndpoint :
    lengthInMeters setup.rod.totalLength / 2 <
      lengthInMeters setup.centerToPointDistance
  coulombConstantPositive :
    0 < coulombConstantInNewtonSquareMetersPerCoulombSquared
      setup.coulombConstant

/-!
The dimensionful Coulomb constant agrees with Physlib's electromagnetic
system and has the standard vacuum SI calibration.  This is reference data,
not the requested field value.
-/
structure UsesVacuumCoulombConstant
    (setup : AxialChargedRodSetup) : Prop where
  agreesWithElectromagneticSystem :
    coulombConstantInNewtonSquareMetersPerCoulombSquared
        setup.coulombConstant =
      setup.electromagneticSystem.coulombConstant
  vacuumSIReadout :
    setup.electromagneticSystem.coulombConstant = 89875517923 / 10

/-! ## Governing electrostatic laws -/

/-!
A uniform finite line charge has constant density `Q/L`, and integrating that
density over its centered support recovers `Q`.  Neither law mentions the
electric field or any answer choice.
-/
structure SatisfiesUniformFiniteLineChargeModel
    (setup : AxialChargedRodSetup) : Prop where
  densityIsChargePerLength :
    linearChargeDensityInCoulombsPerMeter setup.rod.linearChargeDensity =
      chargeInCoulombs setup.rod.totalCharge /
        lengthInMeters setup.rod.totalLength
  totalChargeIsDensityIntegral :
    chargeInCoulombs setup.rod.totalCharge =
      ∫ _xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
        linearChargeDensityInCoulombsPerMeter setup.rod.linearChargeDensity

/-!
Coulomb superposition for a point `P` on the positive rod axis.  A source
element at axial coordinate `x` is `r - x` metres from `P`, so its field
contribution has magnitude `k λ dx / (r - x)²`.  This integral law is general
for the stated rod data and does not assume the requested closed form or
numerical result.
-/
structure SatisfiesAxialCoulombSuperpositionLaw
    (setup : AxialChargedRodSetup) : Prop where
  fieldMagnitudeIsSourceIntegral :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldMagnitudeAtP =
      ∫ xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
        coulombConstantInNewtonSquareMetersPerCoulombSquared
            setup.coulombConstant *
          linearChargeDensityInCoulombsPerMeter
            setup.rod.linearChargeDensity /
          (lengthInMeters setup.centerToPointDistance - xMeters) ^ 2

/-!
The positive rod produces an electric field in the positive axial direction
at `P`.  This relates the dimensionful magnitude to Physlib's vector-field
object without fixing the magnitude numerically.
-/
structure FieldAtPHasStoredAxialMagnitude
    (setup : AxialChargedRodSetup) : Prop where
  positiveAxisDirectionIsUnit : ‖setup.positiveAxisDirection‖ = 1
  vectorFieldAtP :
    setup.electricField setup.observationTime setup.observationPointP =
      electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldMagnitudeAtP • setup.positiveAxisDirection

/-! ## Derived closed form and displayed numerical target -/

/-!
Integrating the axial Coulomb law for the uniform rod yields
`E = k Q / (r² - (L/2)²)`.  This is a derived lemma, not a premise of the main
numerical theorem.
-/
lemma axialElectricField_closedForm
    (setup : AxialChargedRodSetup)
    (hPhysical : HasPhysicalChargedRodParameters setup)
    (hUniform : SatisfiesUniformFiniteLineChargeModel setup)
    (hSuperposition : SatisfiesAxialCoulombSuperpositionLaw setup) :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldMagnitudeAtP =
      coulombConstantInNewtonSquareMetersPerCoulombSquared
          setup.coulombConstant *
        chargeInCoulombs setup.rod.totalCharge /
          (lengthInMeters setup.centerToPointDistance ^ 2 -
            (lengthInMeters setup.rod.totalLength / 2) ^ 2) := by
  let L := lengthInMeters setup.rod.totalLength
  let r := lengthInMeters setup.centerToPointDistance
  let Q := chargeInCoulombs setup.rod.totalCharge
  let ρ :=
    linearChargeDensityInCoulombsPerMeter setup.rod.linearChargeDensity
  let k :=
    coulombConstantInNewtonSquareMetersPerCoulombSquared
      setup.coulombConstant
  let E :=
    electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldMagnitudeAtP
  have hL : 0 < L := by
    simpa [L] using hPhysical.rodLengthPositive
  have hr : L / 2 < r := by
    simpa [L, r] using hPhysical.pointPOutsideRightEndpoint
  have hDensity : ρ = Q / L := by
    simpa [ρ, Q, L] using hUniform.densityIsChargePerLength
  have hField :
      E = ∫ x in -(L / 2)..L / 2, k * ρ / (r - x) ^ 2 := by
    simpa [E, k, ρ, r, L] using
      hSuperposition.fieldMagnitudeIsSourceIntegral
  change E = k * Q / (r ^ 2 - (L / 2) ^ 2)
  rw [hField, hDensity]
  have hab : -(L / 2) ≤ L / 2 := by
    linarith
  have hderiv : ∀ x ∈ Set.uIcc (-(L / 2)) (L / 2),
      HasDerivAt (fun y : ℝ => k * (Q / L) / (r - y))
        (k * (Q / L) / (r - x) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hdenom : r - x ≠ 0 := by
      linarith [hx.2]
    simpa [div_eq_mul_inv] using
      (((hasDerivAt_const x r).sub (hasDerivAt_id x)).inv hdenom).const_mul
        (k * (Q / L))
  have hint : IntervalIntegrable (fun x => k * (Q / L) / (r - x) ^ 2)
      MeasureTheory.volume (-(L / 2)) (L / 2) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hdenom : r - x ≠ 0 := by
      linarith [hx.2]
    exact (continuousAt_const.div
      ((continuousAt_const.sub continuousAt_id).pow 2)
      (pow_ne_zero 2 hdenom)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hLne : L ≠ 0 := ne_of_gt hL
  have hminus : r - L / 2 ≠ 0 := by
    linarith
  have hplus : r - (-(L / 2)) ≠ 0 := by
    linarith
  calc
    k * (Q / L) / (r - L / 2) - k * (Q / L) / (r - (-(L / 2))) =
        k * (Q / L) * (1 / (r - L / 2) - 1 / (r - (-(L / 2)))) := by
      ring
    _ = k * (Q / L) *
        ((1 * (r - (-(L / 2))) - (r - L / 2) * 1) /
          ((r - L / 2) * (r - (-(L / 2))))) := by
      rw [div_sub_div 1 1 hminus hplus]
    _ = k * (Q / L) * (L / (r ^ 2 - (L / 2) ^ 2)) := by
      congr 2 <;> ring
    _ = k * ((Q / L) * L) / (r ^ 2 - (L / 2) ^ 2) := by
      ring
    _ = k * Q / (r ^ 2 - (L / 2) ^ 2) := by
      rw [div_mul_cancel₀ Q hLne]

/-- Labels of the four field-strength answers printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed field magnitude, in newtons per coulomb, beside each choice. -/
def answerFieldStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 1.3 * 10 ^ 5
  | .B => 5.3 * 10 ^ 4
  | .C => 1.0 * 10 ^ 5
  | .D => 9.8 * 10 ^ 4

/-!
The answers are printed to the nearest `10^3 N/C`.  Strictly lying within
half that increment faithfully expresses rounding to a displayed value and
does not define the field itself.
-/
def RoundsToNearestThousand
    (fieldValue displayedValue : ℝ) : Prop :=
  |fieldValue - displayedValue| < 500

/-- A displayed choice is the unique one to which the computed field rounds. -/
def IsUniqueRoundedAnswer
    (fieldValue : ℝ) (choice : AnswerChoice) : Prop :=
  RoundsToNearestThousand fieldValue
      (answerFieldStrengthInNewtonsPerCoulomb choice) ∧
    ∀ otherChoice,
      RoundsToNearestThousand fieldValue
          (answerFieldStrengthInNewtonsPerCoulomb otherChoice) →
        otherChoice = choice

/-!
Blueprint declaration `thm:physics:phyx_mini_0835:target`.

For the stated rod and vacuum calibration, the axial field rounds to
`9.8 * 10^4 N/C`; among the printed values this uniquely selects D.
-/
theorem chargedRodElectricFieldAtP
    (setup : AxialChargedRodSetup)
    (hFigure : MatchesPrimaryChargedRodFigure setup)
    (hData : MatchesChargedRodProblemData setup)
    (hPhysical : HasPhysicalChargedRodParameters setup)
    (hVacuum : UsesVacuumCoulombConstant setup)
    (hUniform : SatisfiesUniformFiniteLineChargeModel setup)
    (hSuperposition : SatisfiesAxialCoulombSuperpositionLaw setup)
    (hVectorField : FieldAtPHasStoredAxialMagnitude setup) :
    RoundsToNearestThousand
        (electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldMagnitudeAtP)
        (9.8 * 10 ^ 4) ∧
      IsUniqueRoundedAnswer
        (electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldMagnitudeAtP) .D := by
  have hK :
      coulombConstantInNewtonSquareMetersPerCoulombSquared
          setup.coulombConstant =
        89875517923 / 10 :=
    hVacuum.agreesWithElectromagneticSystem.trans
      hVacuum.vacuumSIReadout
  have hClosed :=
    axialElectricField_closedForm setup hPhysical hUniform hSuperposition
  rw [hK, hData.totalChargeCoulombs, hData.pointDistanceMeters,
    hData.rodLengthMeters] at hClosed
  rw [hClosed]
  constructor
  · norm_num [RoundsToNearestThousand, abs_lt]
  · rw [IsUniqueRoundedAnswer]
    constructor
    · norm_num [RoundsToNearestThousand,
        answerFieldStrengthInNewtonsPerCoulomb, abs_lt]
    · intro otherChoice hOther
      cases otherChoice with
      | A =>
          norm_num [RoundsToNearestThousand,
            answerFieldStrengthInNewtonsPerCoulomb, abs_lt] at hOther
      | B =>
          norm_num [RoundsToNearestThousand,
            answerFieldStrengthInNewtonsPerCoulomb, abs_lt] at hOther
      | C =>
          norm_num [RoundsToNearestThousand,
            answerFieldStrengthInNewtonsPerCoulomb, abs_lt] at hOther
      | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0835
