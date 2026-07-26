import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0906

open Dimension

/-!
# Mass of two oppositely charged suspended spheres

The primary image shows two identical small spheres hanging from a common
point.  The left sphere has charge `+100 nC`, the right sphere has charge
`-100 nC`, both strings have length `50 cm`, and both make an angle of
`10°` with the vertical.  A uniform `100000 N/C` electric field points left.

Mass, length, charge, acceleration, electric-field strength, and force retain
unit-independent Physlib quantity types.  Real numbers occur only as explicit
unit readouts, dimensionless angles, vector components in Physlib's field
type, and displayed answer values.

Assumption/target split:

* governing laws: uniform-field calibration, `F = qE`, signed axial Coulomb
  force, weight `W = mg`, the suspension geometry, and static force balance;
* previous-part results: none;
* figure/data readouts: two identical small spheres, the `±100 nC` charge
  labels, two `50 cm` strings, two `10°` labels, a common support and dashed
  vertical, and uniformly spaced leftward field arrows; the prose supplies
  the `100000 N/C` field magnitude;
* current target: the mass of each sphere rounds to `4.1 g`, and choice C is
  the unique nearest displayed choice.

The two masses and all force observables are independent fields of the setup.
No premise gives either mass a numerical value or mentions the recorded
answer choice.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  forceDimension * C𝓭⁻¹

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A signed horizontal component of a physical force. -/
abbrev AxialForceComponentQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Kilogram readout used by the force laws. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Gram readout used by the displayed choices. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the two string labels. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Coherent-SI coulomb readout of a signed charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the two charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of electric-field strength in newtons per coulomb. -/
def fieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Newton readout of a nonnegative force magnitude. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Newton readout of a signed horizontal force component. -/
def forceComponentInNewtons (force : AxialForceComponentQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- Convert the dimensionless degree readout in the image to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Named spheres, figure vocabulary, and independent setup -/

/-- The two spheres, named by their positions and charge signs. -/
inductive SphereLabel where
  | leftPositive
  | rightNegative
  deriving DecidableEq, Fintype, Repr

/-- The sphere opposite a given sphere. -/
def SphereLabel.other : SphereLabel → SphereLabel
  | .leftPositive => .rightNegative
  | .rightNegative => .leftPositive

/-- Charge-sign glyph drawn inside a sphere. -/
inductive ChargeSignGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Fill colors visibly distinguishing the two charged spheres. -/
inductive SphereFillColor where
  | red
  | paleTeal
  deriving DecidableEq, Repr

/-- Horizontal directions needed to interpret the field arrows. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Sign of the horizontal direction away from the central vertical line. -/
def outwardHorizontalSign : SphereLabel → ℝ
  | .leftPositive => -1
  | .rightNegative => 1

/-- Sign of the horizontal direction toward the common suspension point. -/
def inwardHorizontalSign : SphereLabel → ℝ
  | .leftPositive => 1
  | .rightNegative => -1

/-- Charge glyph expected on each sphere in image `906.png`. -/
def expectedChargeSignGlyph : SphereLabel → ChargeSignGlyph
  | .leftPositive => .plus
  | .rightNegative => .minus

/-- Fill color expected for each sphere in the primary image. -/
def expectedSphereFillColor : SphereLabel → SphereFillColor
  | .leftPositive => .red
  | .rightNegative => .paleTeal

/-- Signed nanocoulomb label printed beside each sphere. -/
def expectedChargeInNanocoulombs : SphereLabel → ℝ
  | .leftPositive => 100
  | .rightNegative => -100

/-!
Literal presentation data transcribed from the supplied raster.  Numerical
labels remain separate from the dimensionful physical quantities to which
they are calibrated below.
-/
structure SuspendedSpheresFigure where
  sphereShown : SphereLabel → Bool
  sphereFillColor : SphereLabel → SphereFillColor
  chargeSignGlyph : SphereLabel → ChargeSignGlyph
  printedChargeNanocoulombs : SphereLabel → ℝ
  stringShown : SphereLabel → Bool
  printedStringLengthCentimeters : SphereLabel → ℝ
  printedAngleFromVerticalDegrees : SphereLabel → ℝ
  commonSuspensionPointShown : Bool
  dashedVerticalReferenceShown : Bool
  electricFieldArrowCount : ℕ
  electricFieldArrowsUniformlySpaced : Bool
  electricFieldArrowDirection : HorizontalDirection

/-!
Independent physical objects and observables for the equilibrium experiment.
Physlib's electric field retains its spacetime-dependent vector-field role;
the dimensionful scalar `electricFieldStrength` records its uniform magnitude.
The sphere masses are not defined from a force balance or answer choice.
-/
structure SuspendedChargedSpheresSetup where
  figure : SuspendedSpheresFigure
  electromagneticSystem : Electromagnetism.EMSystem
  mass : SphereLabel → MassQuantity
  charge : SphereLabel → SignedChargeQuantity
  stringLength : SphereLabel → LengthQuantity
  angleFromVerticalRadians : SphereLabel → ℝ
  sphereSeparation : LengthQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 2
  observationTime : Time
  suspensionPoint : Space 2
  spherePosition : SphereLabel → Space 2
  modeledAsSmallSphere : SphereLabel → Bool
  spheresAreIdentical : Bool
  electricForceX : SphereLabel → AxialForceComponentQuantity
  coulombForceX : SphereLabel → AxialForceComponentQuantity
  stringTensionMagnitude : SphereLabel → ForceMagnitudeQuantity
  weightMagnitude : SphereLabel → ForceMagnitudeQuantity

/-- Horizontal coordinate, interpreted in metres, of a planar point. -/
def xCoordinateInMeters (point : Space 2) : ℝ :=
  point.val 0

/-- Vertical coordinate, interpreted in metres, of a planar point. -/
def yCoordinateInMeters (point : Space 2) : ℝ :=
  point.val 1

/-- Horizontal displacement from the other sphere to the specified sphere. -/
def displacementFromOtherInMeters
    (setup : SuspendedChargedSpheresSetup) (sphere : SphereLabel) : ℝ :=
  xCoordinateInMeters (setup.spherePosition sphere) -
    xCoordinateInMeters (setup.spherePosition sphere.other)

/-! ## Scenario, primary-image evidence, and physical geometry -/

/-- The prose's assertion that the pictured objects are identical small spheres. -/
structure MatchesIdenticalSmallSphereScenario
    (setup : SuspendedChargedSpheresSetup) : Prop where
  bothObjectsAreSmallSpheres :
    ∀ sphere, setup.modeledAsSmallSphere sphere = true
  identicalConstructionRecorded : setup.spheresAreIdentical = true
  identicalMasses :
    setup.mass .leftPositive = setup.mass .rightNegative

/-!
Problem-statement and primary-image readouts, calibrated to the independent
physical quantities.  The image contains nine uniformly spaced arrows, all
pointing left.  No mass or force value occurs in this structure.
-/
structure MatchesProblemAndFigureReadouts
    (setup : SuspendedChargedSpheresSetup) : Prop where
  bothSpheresShown : ∀ sphere,
    setup.figure.sphereShown sphere = true
  fillColors : ∀ sphere,
    setup.figure.sphereFillColor sphere = expectedSphereFillColor sphere
  chargeSignGlyphs : ∀ sphere,
    setup.figure.chargeSignGlyph sphere = expectedChargeSignGlyph sphere
  printedChargeLabels : ∀ sphere,
    setup.figure.printedChargeNanocoulombs sphere =
      expectedChargeInNanocoulombs sphere
  physicalChargesMatchLabels : ∀ sphere,
    chargeInNanocoulombs (setup.charge sphere) =
      setup.figure.printedChargeNanocoulombs sphere
  bothStringsShown : ∀ sphere,
    setup.figure.stringShown sphere = true
  printedStringLengths : ∀ sphere,
    setup.figure.printedStringLengthCentimeters sphere = 50
  physicalStringLengthsMatchLabels : ∀ sphere,
    lengthInCentimeters (setup.stringLength sphere) =
      setup.figure.printedStringLengthCentimeters sphere
  printedAngles : ∀ sphere,
    setup.figure.printedAngleFromVerticalDegrees sphere = 10
  physicalAnglesMatchLabels : ∀ sphere,
    setup.angleFromVerticalRadians sphere =
      degreesToRadians
        (setup.figure.printedAngleFromVerticalDegrees sphere)
  commonSuspensionPointShown :
    setup.figure.commonSuspensionPointShown = true
  verticalReferenceShown :
    setup.figure.dashedVerticalReferenceShown = true
  nineFieldArrowsShown : setup.figure.electricFieldArrowCount = 9
  fieldArrowsAreUniform :
    setup.figure.electricFieldArrowsUniformlySpaced = true
  fieldArrowsPointLeft :
    setup.figure.electricFieldArrowDirection = .left
  fieldStrengthFromProblemStatement :
    fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength = 100000

/-!
The two strings meet at the common support, and their horizontal and vertical
projections are determined by their lengths and angles.  The last clause
calibrates the independent physical separation to the position coordinates.
-/
structure HasSymmetricSuspensionGeometry
    (setup : SuspendedChargedSpheresSetup) : Prop where
  leftSphereIsLeftOfSupport :
    xCoordinateInMeters (setup.spherePosition .leftPositive) <
      xCoordinateInMeters setup.suspensionPoint
  rightSphereIsRightOfSupport :
    xCoordinateInMeters setup.suspensionPoint <
      xCoordinateInMeters (setup.spherePosition .rightNegative)
  spheresHaveSameHeight :
    yCoordinateInMeters (setup.spherePosition .leftPositive) =
      yCoordinateInMeters (setup.spherePosition .rightNegative)
  horizontalStringProjection : ∀ sphere,
    xCoordinateInMeters (setup.spherePosition sphere) -
        xCoordinateInMeters setup.suspensionPoint =
      outwardHorizontalSign sphere *
        lengthInMeters (setup.stringLength sphere) *
          Real.sin (setup.angleFromVerticalRadians sphere)
  verticalStringProjection : ∀ sphere,
    yCoordinateInMeters setup.suspensionPoint -
        yCoordinateInMeters (setup.spherePosition sphere) =
      lengthInMeters (setup.stringLength sphere) *
        Real.cos (setup.angleFromVerticalRadians sphere)
  separationMatchesHorizontalCoordinates :
    lengthInMeters setup.sphereSeparation =
      xCoordinateInMeters (setup.spherePosition .rightNegative) -
        xCoordinateInMeters (setup.spherePosition .leftPositive)

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalSuspensionParameters
    (setup : SuspendedChargedSpheresSetup) : Prop where
  massesPositive : ∀ sphere,
    0 < massInKilograms (setup.mass sphere)
  stringLengthsPositive : ∀ sphere,
    0 < lengthInMeters (setup.stringLength sphere)
  separationPositive :
    0 < lengthInMeters setup.sphereSeparation
  anglesAcute : ∀ sphere,
    0 < setup.angleFromVerticalRadians sphere ∧
      setup.angleFromVerticalRadians sphere < Real.pi / 2
  fieldStrengthPositive :
    0 < fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  tensionsPositive : ∀ sphere,
    0 < forceMagnitudeInNewtons (setup.stringTensionMagnitude sphere)
  weightsPositive : ∀ sphere,
    0 < forceMagnitudeInNewtons (setup.weightMagnitude sphere)
  chargesNonzero : ∀ sphere,
    chargeInCoulombs (setup.charge sphere) ≠ 0
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
The rounded reference values conventionally used in the multiple-choice
calculation.  They calibrate governing constants and do not constrain a mass.
-/
structure UsesSchoolReferenceValues
    (setup : SuspendedChargedSpheresSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9
  gravitationalAccelerationCalibration :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 9.8

/-! ## Governing field and force laws -/

/-!
The arrows represent a spatially and temporally uniform field whose vector
has negative horizontal component and zero vertical component.  Components of
Physlib's field are interpreted here as coherent-SI `N/C` readouts.
-/
structure IsUniformLeftwardElectricField
    (setup : SuspendedChargedSpheresSetup) : Prop where
  fieldValue : ∀ time position,
    setup.electricField time position =
      !₂[-fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength, 0]

/-!
Electric force law `F = qE`, stated for the signed horizontal component at
each sphere's position.  The opposite charge signs therefore produce outward
forces in the common leftward field.
-/
structure SatisfiesElectricForceLaw
    (setup : SuspendedChargedSpheresSetup) : Prop where
  forceOnEachSphere : ∀ sphere,
    forceComponentInNewtons (setup.electricForceX sphere) =
      chargeInCoulombs (setup.charge sphere) *
        setup.electricField setup.observationTime
          (setup.spherePosition sphere) 0

/-!
Signed one-dimensional Coulomb force between the two spheres.  For sphere
`i`, with displacement `d = xᵢ - xⱼ`, the law is
`Fᵢ = k qᵢ qⱼ d / |d|³`; this retains both the inverse-square magnitude and
the attraction direction for opposite charges.
-/
structure SatisfiesCoulombInteractionLaw
    (setup : SuspendedChargedSpheresSetup) : Prop where
  forceOnEachSphere : ∀ sphere,
    displacementFromOtherInMeters setup sphere ≠ 0 →
      forceComponentInNewtons (setup.coulombForceX sphere) =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge sphere) *
          chargeInCoulombs (setup.charge sphere.other) *
          displacementFromOtherInMeters setup sphere /
          |displacementFromOtherInMeters setup sphere| ^ 3

/-- Weight magnitude obeys `W = mg` for each independently stored mass. -/
structure SatisfiesWeightLaw
    (setup : SuspendedChargedSpheresSetup) : Prop where
  weightOfEachSphere : ∀ sphere,
    forceMagnitudeInNewtons (setup.weightMagnitude sphere) =
      massInKilograms (setup.mass sphere) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration

/-!
Static equilibrium in horizontal and vertical components.  Tension points
toward the common support, electric and Coulomb forces are horizontal, and
weight points downward.  These are general balance equations rather than a
numerical mass conclusion.
-/
structure SatisfiesStaticForceBalance
    (setup : SuspendedChargedSpheresSetup) : Prop where
  horizontalBalance : ∀ sphere,
    forceComponentInNewtons (setup.electricForceX sphere) +
        forceComponentInNewtons (setup.coulombForceX sphere) +
        inwardHorizontalSign sphere *
          forceMagnitudeInNewtons (setup.stringTensionMagnitude sphere) *
          Real.sin (setup.angleFromVerticalRadians sphere) = 0
  verticalBalance : ∀ sphere,
    forceMagnitudeInNewtons (setup.stringTensionMagnitude sphere) *
        Real.cos (setup.angleFromVerticalRadians sphere) =
      forceMagnitudeInNewtons (setup.weightMagnitude sphere)

/-! ## Derived relations and displayed-answer target -/

/-!
The common-pivot geometry gives the horizontal separation as the sum of the
two horizontal string projections.  This is a useful intermediate statement
for the later Coulomb calculation.
-/
lemma sphereSeparation_eq_sum_horizontal_projections
    (setup : SuspendedChargedSpheresSetup)
    (_geometry : HasSymmetricSuspensionGeometry setup) :
    lengthInMeters setup.sphereSeparation =
      lengthInMeters (setup.stringLength .leftPositive) *
          Real.sin (setup.angleFromVerticalRadians .leftPositive) +
        lengthInMeters (setup.stringLength .rightNegative) *
          Real.sin (setup.angleFromVerticalRadians .rightNegative) := by
  rcases _geometry with ⟨_, _, _, hproj, _, hsep⟩
  rw [hsep]
  have hl := hproj SphereLabel.leftPositive
  have hr := hproj SphereLabel.rightNegative
  simp only [outwardHorizontalSign] at hl hr
  linarith

/-!
Eliminating tension from horizontal and vertical equilibrium yields the mass
in terms of the outward electric force, inward Coulomb attraction, gravity,
and the string angle.  All quantities on the right are independent
observables constrained by governing laws.
-/
lemma massInKilograms_eq_force_balance_expression
    (setup : SuspendedChargedSpheresSetup)
    (sphere : SphereLabel)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_geometry : HasSymmetricSuspensionGeometry setup)
    (_physical : HasPhysicalSuspensionParameters setup)
    (_uniformField : IsUniformLeftwardElectricField setup)
    (_electricForce : SatisfiesElectricForceLaw setup)
    (_coulombForce : SatisfiesCoulombInteractionLaw setup)
    (_weight : SatisfiesWeightLaw setup)
    (_equilibrium : SatisfiesStaticForceBalance setup) :
    massInKilograms (setup.mass sphere) =
      (|forceComponentInNewtons (setup.electricForceX sphere)| -
          |forceComponentInNewtons (setup.coulombForceX sphere)|) /
        (accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          Real.tan (setup.angleFromVerticalRadians sphere)) := by
  have hang := _physical.anglesAcute sphere
  have hsin : 0 < Real.sin (setup.angleFromVerticalRadians sphere) :=
    Real.sin_pos_of_pos_of_lt_pi hang.1
      (by linarith [hang.2, Real.pi_pos])
  have hcos : 0 < Real.cos (setup.angleFromVerticalRadians sphere) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hang.2⟩
  have hq := _readouts.physicalChargesMatchLabels sphere
  rw [_readouts.printedChargeLabels sphere] at hq
  have helectric := _electricForce.forceOnEachSphere sphere
  rw [_uniformField.fieldValue] at helectric
  simp only [Matrix.cons_val_zero] at helectric
  cases sphere with
  | leftPositive =>
    norm_num [expectedChargeInNanocoulombs, chargeInNanocoulombs] at hq
    have hqpos :
        0 < chargeInCoulombs (setup.charge .leftPositive) := by
      nlinarith
    have helectric_neg :
        forceComponentInNewtons (setup.electricForceX .leftPositive) < 0 := by
      rw [helectric]
      exact mul_neg_of_pos_of_neg hqpos
        (neg_neg_of_pos _physical.fieldStrengthPositive)
    have hqother :=
      _readouts.physicalChargesMatchLabels SphereLabel.rightNegative
    rw [_readouts.printedChargeLabels SphereLabel.rightNegative] at hqother
    norm_num [expectedChargeInNanocoulombs, chargeInNanocoulombs] at hqother
    have hqotherneg :
        chargeInCoulombs (setup.charge .rightNegative) < 0 := by
      nlinarith
    have hdispneg :
        displacementFromOtherInMeters setup .leftPositive < 0 := by
      simp only [displacementFromOtherInMeters, SphereLabel.other]
      linarith [_geometry.leftSphereIsLeftOfSupport,
        _geometry.rightSphereIsRightOfSupport]
    have hcoulomb :=
      _coulombForce.forceOnEachSphere SphereLabel.leftPositive
        (ne_of_lt hdispneg)
    simp only [SphereLabel.other] at hcoulomb
    have hcoulomb_pos :
        0 < forceComponentInNewtons (setup.coulombForceX .leftPositive) := by
      rw [hcoulomb]
      have hnum :
          0 < setup.electromagneticSystem.coulombConstant *
              chargeInCoulombs (setup.charge .leftPositive) *
              chargeInCoulombs (setup.charge .rightNegative) *
              displacementFromOtherInMeters setup .leftPositive :=
        mul_pos_of_neg_of_neg
          (mul_neg_of_pos_of_neg
            (mul_pos _physical.coulombConstantPositive hqpos) hqotherneg)
          hdispneg
      exact
        div_pos hnum
          (pow_pos (abs_pos.mpr (ne_of_lt hdispneg)) 3)
    have hhorizontal :=
      _equilibrium.horizontalBalance SphereLabel.leftPositive
    simp only [inwardHorizontalSign, one_mul] at hhorizontal
    have hdiff :
        -forceComponentInNewtons (setup.electricForceX .leftPositive) -
            forceComponentInNewtons (setup.coulombForceX .leftPositive) =
          forceMagnitudeInNewtons
              (setup.stringTensionMagnitude .leftPositive) *
            Real.sin (setup.angleFromVerticalRadians .leftPositive) := by
      linarith
    have hvertical :=
      _equilibrium.verticalBalance SphereLabel.leftPositive
    have hweight := _weight.weightOfEachSphere SphereLabel.leftPositive
    have hmass :
        massInKilograms (setup.mass .leftPositive) =
          forceMagnitudeInNewtons
                (setup.stringTensionMagnitude .leftPositive) *
              Real.cos (setup.angleFromVerticalRadians .leftPositive) /
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration := by
      apply
        (eq_div_iff
          (ne_of_gt _physical.gravitationalAccelerationPositive)).2
      linarith
    rw [hmass, abs_of_neg helectric_neg, abs_of_pos hcoulomb_pos, hdiff,
      Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hsin, ne_of_gt hcos,
      ne_of_gt _physical.gravitationalAccelerationPositive]
  | rightNegative =>
    norm_num [expectedChargeInNanocoulombs, chargeInNanocoulombs] at hq
    have hqneg :
        chargeInCoulombs (setup.charge .rightNegative) < 0 := by
      nlinarith
    have helectric_pos :
        0 < forceComponentInNewtons (setup.electricForceX .rightNegative) := by
      rw [helectric]
      exact mul_pos_of_neg_of_neg hqneg
        (neg_neg_of_pos _physical.fieldStrengthPositive)
    have hqother :=
      _readouts.physicalChargesMatchLabels SphereLabel.leftPositive
    rw [_readouts.printedChargeLabels SphereLabel.leftPositive] at hqother
    norm_num [expectedChargeInNanocoulombs, chargeInNanocoulombs] at hqother
    have hqotherpos :
        0 < chargeInCoulombs (setup.charge .leftPositive) := by
      nlinarith
    have hdisppos :
        0 < displacementFromOtherInMeters setup .rightNegative := by
      simp only [displacementFromOtherInMeters, SphereLabel.other]
      linarith [_geometry.leftSphereIsLeftOfSupport,
        _geometry.rightSphereIsRightOfSupport]
    have hcoulomb :=
      _coulombForce.forceOnEachSphere SphereLabel.rightNegative
        (ne_of_gt hdisppos)
    simp only [SphereLabel.other] at hcoulomb
    have hcoulomb_neg :
        forceComponentInNewtons (setup.coulombForceX .rightNegative) < 0 := by
      rw [hcoulomb]
      have hnum :
          setup.electromagneticSystem.coulombConstant *
                chargeInCoulombs (setup.charge .rightNegative) *
              chargeInCoulombs (setup.charge .leftPositive) *
            displacementFromOtherInMeters setup .rightNegative < 0 :=
        mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos
            (mul_neg_of_pos_of_neg
              _physical.coulombConstantPositive hqneg)
            hqotherpos)
          hdisppos
      exact div_neg_of_neg_of_pos hnum (by positivity)
    have hhorizontal :=
      _equilibrium.horizontalBalance SphereLabel.rightNegative
    simp only [inwardHorizontalSign, neg_mul] at hhorizontal
    have hdiff :
        forceComponentInNewtons (setup.electricForceX .rightNegative) +
            forceComponentInNewtons (setup.coulombForceX .rightNegative) =
          forceMagnitudeInNewtons
              (setup.stringTensionMagnitude .rightNegative) *
            Real.sin (setup.angleFromVerticalRadians .rightNegative) := by
      linarith
    have hvertical :=
      _equilibrium.verticalBalance SphereLabel.rightNegative
    have hweight := _weight.weightOfEachSphere SphereLabel.rightNegative
    have hmass :
        massInKilograms (setup.mass .rightNegative) =
          forceMagnitudeInNewtons
                (setup.stringTensionMagnitude .rightNegative) *
              Real.cos (setup.angleFromVerticalRadians .rightNegative) /
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration := by
      apply
        (eq_div_iff
          (ne_of_gt _physical.gravitationalAccelerationPositive)).2
      linarith
    rw [hmass, abs_of_pos helectric_pos, abs_of_neg hcoulomb_neg,
      Real.tan_eq_sin_div_cos]
    simp only [sub_neg_eq_add]
    rw [hdiff]
    field_simp [ne_of_gt hsin, ne_of_gt hcos,
      ne_of_gt _physical.gravitationalAccelerationPositive]

/-- Labels attached to the four displayed mass choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Mass in grams printed beside each answer label. -/
def AnswerChoice.massInGrams : AnswerChoice → ℝ
  | .A => 3
  | .B => 4.4
  | .C => 4.1
  | .D => 5.2

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- The actual mass rounds to a displayed value at the nearest `0.1 g`. -/
def RoundsToNearestTenthGram (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 20

/-- A choice is strictly nearer to the actual mass than every alternative. -/
def IsUniqueNearestDisplayedMass
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - choice.massInGrams| < |actual - other.massInGrams|

/-!
**Blueprint target** `thm:physics:phyx_mini_0906:target`.

The `50 cm`, `10°`, and `±100 nC` figure data, the `100000 N/C` uniform
field, Coulomb interaction, and component force balance imply a mass of about
`4.06 g` for each identical sphere.  Thus each mass rounds to `4.1 g`, and
the recorded choice C is the unique nearest displayed choice.
-/
theorem problem_phyx_mini_0906
    (setup : SuspendedChargedSpheresSetup)
    (_scenario : MatchesIdenticalSmallSphereScenario setup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_geometry : HasSymmetricSuspensionGeometry setup)
    (_physical : HasPhysicalSuspensionParameters setup)
    (_referenceValues : UsesSchoolReferenceValues setup)
    (_uniformField : IsUniformLeftwardElectricField setup)
    (_electricForce : SatisfiesElectricForceLaw setup)
    (_coulombForce : SatisfiesCoulombInteractionLaw setup)
    (_weight : SatisfiesWeightLaw setup)
    (_equilibrium : SatisfiesStaticForceBalance setup) :
    ∀ sphere,
      RoundsToNearestTenthGram
          (massInGrams (setup.mass sphere))
          recordedDatasetAnswer.massInGrams ∧
        IsUniqueNearestDisplayedMass
          (massInGrams (setup.mass sphere)) recordedDatasetAnswer := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have mass_grams_eq (mass : MassQuantity) :
      massInGrams mass = 1000 * massInKilograms mass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (mass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, massReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hangle :
      setup.angleFromVerticalRadians .leftPositive = Real.pi / 18 := by
    rw [_readouts.physicalAnglesMatchLabels,
      _readouts.printedAngles SphereLabel.leftPositive]
    norm_num [degreesToRadians]
    ring
  have hlength :
      lengthInMeters (setup.stringLength .leftPositive) = 1 / 2 := by
    have hconversion :=
      length_centimeters_eq (setup.stringLength .leftPositive)
    rw [_readouts.physicalStringLengthsMatchLabels,
      _readouts.printedStringLengths SphereLabel.leftPositive] at hconversion
    norm_num at hconversion ⊢
    linarith only [hconversion]
  have hlengthOther :
      lengthInMeters (setup.stringLength .rightNegative) = 1 / 2 := by
    have hconversion :=
      length_centimeters_eq (setup.stringLength .rightNegative)
    rw [_readouts.physicalStringLengthsMatchLabels,
      _readouts.printedStringLengths SphereLabel.rightNegative] at hconversion
    norm_num at hconversion ⊢
    linarith only [hconversion]
  have hangleOther :
      setup.angleFromVerticalRadians .rightNegative = Real.pi / 18 := by
    rw [_readouts.physicalAnglesMatchLabels,
      _readouts.printedAngles SphereLabel.rightNegative]
    norm_num [degreesToRadians]
    ring
  have hseparation :
      lengthInMeters setup.sphereSeparation =
        Real.sin (Real.pi / 18) := by
    rw [sphereSeparation_eq_sum_horizontal_projections setup _geometry,
      hlength, hlengthOther, hangle, hangleOther]
    ring
  have hxpos : 0 < Real.pi / 18 := by positivity
  have hxhalf : Real.pi / 18 < Real.pi / 2 := by
    nlinarith only [Real.pi_pos]
  have hsinpos : 0 < Real.sin (Real.pi / 18) :=
    Real.sin_pos_of_pos_of_lt_pi hxpos (by nlinarith only [Real.pi_pos])
  have hcospos : 0 < Real.cos (Real.pi / 18) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith only [Real.pi_pos], hxhalf⟩
  have hsinCubic :
      4 * Real.sin (Real.pi / 18) ^ 3 -
          3 * Real.sin (Real.pi / 18) + 1 / 2 = 0 := by
    have h := Real.sin_three_mul (Real.pi / 18)
    rw [show 3 * (Real.pi / 18) = Real.pi / 6 by ring,
      Real.sin_pi_div_six] at h
    nlinarith only [h]
  have hsinAboveOneSixth :
      (1 / 6 : ℝ) < Real.sin (Real.pi / 18) := by
    nlinarith only [hsinCubic, pow_pos hsinpos 3]
  have hsinCubeAboveOneSixth :
      (1 / 6 : ℝ) ^ 3 < Real.sin (Real.pi / 18) ^ 3 :=
    pow_lt_pow_left₀ hsinAboveOneSixth (by norm_num) (by norm_num)
  have hsinAboveFirstRefinement :
      (43 / 250 : ℝ) < Real.sin (Real.pi / 18) := by
    nlinarith only [hsinCubic, hsinCubeAboveOneSixth]
  have hsinCubeAboveFirstRefinement :
      (43 / 250 : ℝ) ^ 3 < Real.sin (Real.pi / 18) ^ 3 :=
    pow_lt_pow_left₀ hsinAboveFirstRefinement (by norm_num) (by norm_num)
  have hsinAboveSecondRefinement :
      (867 / 5000 : ℝ) < Real.sin (Real.pi / 18) := by
    nlinarith only [hsinCubic, hsinCubeAboveFirstRefinement]
  have hsinCubeAboveSecondRefinement :
      (867 / 5000 : ℝ) ^ 3 < Real.sin (Real.pi / 18) ^ 3 :=
    pow_lt_pow_left₀ hsinAboveSecondRefinement (by norm_num) (by norm_num)
  have hsinUpperEndpoint :
      Real.sin (1309 / 7500 : ℝ) < (1737 / 10000 : ℝ) := by
    have hbound :=
      Real.sin_bound (x := (1309 / 7500 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1309 / 7500)] at hbound
    rw [abs_le] at hbound
    norm_num at hbound ⊢
    nlinarith only [hbound.2]
  have hsinLower :
      (217 / 1250 : ℝ) < Real.sin (Real.pi / 18) := by
    nlinarith only [hsinCubic, hsinCubeAboveSecondRefinement]
  have hsinUpper :
      Real.sin (Real.pi / 18) < (1737 / 10000 : ℝ) := by
    apply lt_trans _ hsinUpperEndpoint
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · nlinarith only [Real.pi_pos]
    · nlinarith only [Real.pi_gt_d4]
    · nlinarith only [Real.pi_lt_d4]
  have hcosLowerEndpoint :
      (9847 / 10000 : ℝ) < Real.cos (1309 / 7500 : ℝ) := by
    have hbound :=
      Real.cos_bound (x := (1309 / 7500 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1309 / 7500)] at hbound
    rw [abs_le] at hbound
    norm_num at hbound ⊢
    nlinarith only [hbound.1]
  have hcosUpperEndpoint :
      Real.cos (6283 / 36000 : ℝ) < (9849 / 10000 : ℝ) := by
    have hbound :=
      Real.cos_bound (x := (6283 / 36000 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6283 / 36000)] at hbound
    rw [abs_le] at hbound
    norm_num at hbound ⊢
    nlinarith only [hbound.2]
  have hcosLower :
      (9847 / 10000 : ℝ) < Real.cos (Real.pi / 18) := by
    apply hcosLowerEndpoint.trans
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith only [Real.pi_gt_d4]
    · nlinarith only [Real.pi_lt_d4]
  have hcosUpper :
      Real.cos (Real.pi / 18) < (9849 / 10000 : ℝ) := by
    apply lt_trans _ hcosUpperEndpoint
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith only [Real.pi_pos]
    · nlinarith only [Real.pi_gt_d4]
  have hqLeft :
      chargeInCoulombs (setup.charge .leftPositive) = 1 / 10000000 := by
    have h := _readouts.physicalChargesMatchLabels SphereLabel.leftPositive
    rw [_readouts.printedChargeLabels SphereLabel.leftPositive] at h
    norm_num [expectedChargeInNanocoulombs, chargeInNanocoulombs] at h ⊢
    linarith only [h]
  have hqRight :
      chargeInCoulombs (setup.charge .rightNegative) = -1 / 10000000 := by
    have h := _readouts.physicalChargesMatchLabels SphereLabel.rightNegative
    rw [_readouts.printedChargeLabels SphereLabel.rightNegative] at h
    norm_num [expectedChargeInNanocoulombs, chargeInNanocoulombs] at h ⊢
    linarith only [h]
  have helectricLeft :
      forceComponentInNewtons (setup.electricForceX .leftPositive) =
        -1 / 100 := by
    have h := _electricForce.forceOnEachSphere SphereLabel.leftPositive
    rw [_uniformField.fieldValue] at h
    simp only [Matrix.cons_val_zero] at h
    rw [hqLeft, _readouts.fieldStrengthFromProblemStatement] at h
    norm_num at h ⊢
    exact h
  have hdisplacement :
      displacementFromOtherInMeters setup .leftPositive =
        -Real.sin (Real.pi / 18) := by
    rw [displacementFromOtherInMeters, SphereLabel.other, ← hseparation]
    linarith only [_geometry.separationMatchesHorizontalCoordinates]
  have hdisplacementNeg :
      displacementFromOtherInMeters setup .leftPositive < 0 := by
    rw [hdisplacement]
    exact neg_neg_of_pos hsinpos
  have hcoulombLeft :
      forceComponentInNewtons (setup.coulombForceX .leftPositive) =
        9 / (100000 * Real.sin (Real.pi / 18) ^ 2) := by
    have h :=
      _coulombForce.forceOnEachSphere SphereLabel.leftPositive
        (ne_of_lt hdisplacementNeg)
    simp only [SphereLabel.other] at h
    rw [_referenceValues.coulombConstantCalibration, hqLeft, hqRight,
      hdisplacement, abs_of_neg (neg_neg_of_pos hsinpos)] at h
    rw [h]
    field_simp [ne_of_gt hsinpos] <;> ring
  have hcoulombLeftPos :
      0 < forceComponentInNewtons (setup.coulombForceX .leftPositive) := by
    rw [hcoulombLeft]
    positivity
  have hmassKilograms :
      massInKilograms (setup.mass .leftPositive) =
        (1 / 100 - 9 / (100000 * Real.sin (Real.pi / 18) ^ 2)) /
          ((49 / 5) *
            (Real.sin (Real.pi / 18) / Real.cos (Real.pi / 18))) := by
    rw [massInKilograms_eq_force_balance_expression setup
      SphereLabel.leftPositive _readouts _geometry _physical _uniformField
      _electricForce _coulombForce _weight _equilibrium]
    rw [abs_of_pos hcoulombLeftPos, helectricLeft, hcoulombLeft,
      _referenceValues.gravitationalAccelerationCalibration, hangle,
      Real.tan_eq_sin_div_cos]
    norm_num
  have hmassRelation :
      massInGrams (setup.mass .leftPositive) *
          (980 * Real.sin (Real.pi / 18) ^ 3) =
        (1000 * Real.sin (Real.pi / 18) ^ 2 - 9) *
          Real.cos (Real.pi / 18) := by
    rw [mass_grams_eq, hmassKilograms]
    field_simp [ne_of_gt hsinpos, ne_of_gt hcospos] <;> ring
  have hdenominatorPos :
      0 < 980 * Real.sin (Real.pi / 18) ^ 3 := by positivity
  have hsinSquareLower :
      (217 / 1250 : ℝ) ^ 2 < Real.sin (Real.pi / 18) ^ 2 :=
    pow_lt_pow_left₀ hsinLower (by norm_num) (by norm_num)
  have hsinSquareUpper :
      Real.sin (Real.pi / 18) ^ 2 < (1737 / 10000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hsinUpper hsinpos.le (by norm_num)
  have hforceFactorPos :
      0 < 1000 * Real.sin (Real.pi / 18) ^ 2 - 9 := by
    nlinarith only [hsinSquareLower]
  have hnumeratorLower :
      (1000 * (217 / 1250 : ℝ) ^ 2 - 9) * (9847 / 10000) <
        (1000 * Real.sin (Real.pi / 18) ^ 2 - 9) *
          Real.cos (Real.pi / 18) := by
    have hfactorLower :
        1000 * (217 / 1250 : ℝ) ^ 2 - 9 <
          1000 * Real.sin (Real.pi / 18) ^ 2 - 9 := by
      nlinarith only [hsinSquareLower]
    exact mul_lt_mul hfactorLower hcosLower.le (by norm_num)
      (le_of_lt hforceFactorPos)
  have hnumeratorUpper :
      (1000 * Real.sin (Real.pi / 18) ^ 2 - 9) *
          Real.cos (Real.pi / 18) <
        (1000 * (1737 / 10000 : ℝ) ^ 2 - 9) * (9849 / 10000) := by
    have hfactorUpper :
        1000 * Real.sin (Real.pi / 18) ^ 2 - 9 <
          1000 * (1737 / 10000 : ℝ) ^ 2 - 9 := by
      nlinarith only [hsinSquareUpper]
    exact mul_lt_mul hfactorUpper hcosUpper.le hcospos
      (by norm_num)
  have hmassLower :
      (81 / 20 : ℝ) < massInGrams (setup.mass .leftPositive) := by
    apply
      (mul_lt_mul_iff_of_pos_right hdenominatorPos).mp
    rw [hmassRelation]
    calc
      (81 / 20 : ℝ) * (980 * Real.sin (Real.pi / 18) ^ 3) <
          (81 / 20) * (980 * (1737 / 10000 : ℝ) ^ 3) := by
            gcongr
      _ < (1000 * (217 / 1250 : ℝ) ^ 2 - 9) * (9847 / 10000) := by
            norm_num
      _ < _ := hnumeratorLower
  have hmassUpper :
      massInGrams (setup.mass .leftPositive) < (83 / 20 : ℝ) := by
    apply
      (mul_lt_mul_iff_of_pos_right hdenominatorPos).mp
    rw [hmassRelation]
    calc
      (1000 * Real.sin (Real.pi / 18) ^ 2 - 9) *
          Real.cos (Real.pi / 18) <
          (1000 * (1737 / 10000 : ℝ) ^ 2 - 9) * (9849 / 10000) :=
            hnumeratorUpper
      _ < (83 / 20) * (980 * (217 / 1250 : ℝ) ^ 3) := by
            norm_num
      _ < (83 / 20) * (980 * Real.sin (Real.pi / 18) ^ 3) := by
            gcongr
  intro sphere
  have hmassSame :
      massInGrams (setup.mass sphere) =
        massInGrams (setup.mass .leftPositive) := by
    cases sphere with
    | leftPositive => rfl
    | rightNegative =>
      rw [_scenario.identicalMasses]
  rw [hmassSame]
  constructor
  · rw [RoundsToNearestTenthGram, recordedDatasetAnswer,
      AnswerChoice.massInGrams, abs_lt]
    constructor <;> norm_num <;>
      nlinarith only [hmassLower, hmassUpper]
  · intro other hother
    cases other with
    | A =>
      norm_num [recordedDatasetAnswer, AnswerChoice.massInGrams]
      exact sq_lt_sq.mp (by nlinarith only [hmassLower])
    | B =>
      norm_num [recordedDatasetAnswer, AnswerChoice.massInGrams]
      exact sq_lt_sq.mp (by nlinarith only [hmassUpper])
    | C => exact (hother rfl).elim
    | D =>
      norm_num [recordedDatasetAnswer, AnswerChoice.massInGrams]
      exact sq_lt_sq.mp (by nlinarith only [hmassUpper])

end PhyXMiniProblems.ProblemPhyXMini0906
