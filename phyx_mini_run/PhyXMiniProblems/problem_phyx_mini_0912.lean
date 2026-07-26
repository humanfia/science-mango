import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0912

open Dimension

/-!
# Charge of a metal ball that binds a proton in a circular orbit

In a vacuum chamber, a proton moves in a circular orbit around a metal ball.
The ball has diameter `1.0 cm`, the orbit is `1.0 mm` above its surface, and
the period is `1.0 μs`.  The primary raster shows negative marks on the ball,
an orbiting positive marker labelled `e`, inward electric-field and electric-
force arrows, a tangential velocity arrow, and the center-to-particle radius
label `r`.

The auxiliary caption calls the orbiting marker an electron and describes the
central charge as positive.  Those claims conflict with both the prose and the
primary raster.  This file follows the prose (proton) and primary raster
(negative ball, inward field).

Physical lengths, durations, mass, charge, field strength, velocity, and force
are unit-independent Physlib `Dimensionful` quantities.  Real numbers occur
only at explicit coherent-SI readout boundaries or as printed numerical data.

Assumption/target split:

* governing laws: exterior spherical Coulomb field, electric force on a
  positive charge, circular-orbit kinematics, and centripetal force;
* previous-part results: none;
* figure/data readouts: ball diameter `1.0 cm`, clearance `1.0 mm`, period
  `1.0 μs`, the raster labels `Q`, `e`, `E`, `F_elec`, `v`, and `r`, and
  standard rounded values for the proton constants and Coulomb's constant;
* current target: the ball charge is negative and rounds to
  `-9.9 * 10^-12 C`, uniquely selecting answer C.

No setup field, source-data predicate, or governing-law predicate assigns the
requested numerical charge to the ball.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  forceDimension * C𝓭⁻¹

/-- The physical dimension `L T⁻¹` of velocity. -/
def velocityDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A unit-independent spatial velocity vector. -/
abbrev SpatialVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 3)))

/-- A unit-independent spatial force vector. -/
abbrev SpatialForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 3)))

/-- Coherent-SI readout of a length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used for the ball-diameter datum. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Millimetre readout used for the proton's surface clearance. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  1000 * lengthInMeters length

/-- Coherent-SI readout of a duration, in seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Microsecond readout used for the orbital-period datum. -/
def durationInMicroseconds (duration : DurationQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * durationInSeconds duration

/-- Coherent-SI readout of a mass, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed charge, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Coherent-SI readout of electric-field magnitude, in newtons per coulomb. -/
def electricFieldMagnitudeInNewtonsPerCoulomb
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of velocity, in metres per second. -/
def velocityVectorInMetersPerSecond
    (velocity : SpatialVelocityQuantity) : EuclideanSpace ℝ (Fin 3) :=
  (velocity UnitChoices.SI).val

/-- Speed obtained as the norm of the coherent-SI velocity vector. -/
def speedInMetersPerSecond (velocity : SpatialVelocityQuantity) : ℝ :=
  ‖velocityVectorInMetersPerSecond velocity‖

/-- Coherent-SI readout of force, in newtons. -/
def forceVectorInNewtons
    (force : SpatialForceQuantity) : EuclideanSpace ℝ (Fin 3) :=
  (force UnitChoices.SI).val

/-- Force magnitude obtained as the norm of the coherent-SI force vector. -/
def forceMagnitudeInNewtons (force : SpatialForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-! ## Physical roles and literal primary-raster content -/

/-- Medium in which the charged-particle motion takes place. -/
inductive ChamberMedium where
  | vacuum
  | material
  deriving DecidableEq, Repr

/-- Particle species relevant to the prose/figure discrepancy. -/
inductive ParticleSpecies where
  | proton
  | electron
  | other
  deriving DecidableEq, Repr

/-- Model assigned to the central charged body. -/
inductive CentralBodyModel where
  | conductingSphere
  | pointParticle
  | other
  deriving DecidableEq, Repr

/-- Named vector arrows visible in image `912.png`. -/
inductive FigureArrow where
  | electricField
  | electricForce
  | velocity
  deriving DecidableEq, Fintype, Repr

/-- Qualitative direction of a physical or depicted vector. -/
inductive VectorDirection where
  | radiallyInward
  | radiallyOutward
  | tangential
  deriving DecidableEq, Repr

/-!
Literal content transcribed from the primary raster.  The raster's orbiting
marker is labelled `e` and contains a plus sign; it does not contain the word
"electron".  Charge values and answer choices do not occur in this structure.
-/
structure ChargedBallOrbitFigure where
  centralSphereShown : Bool
  centralSphereLabel : String
  negativeSurfaceMarksShown : Bool
  orbitingParticleShown : Bool
  orbitingParticleLabel : String
  positiveGlyphOnOrbitingParticle : Bool
  arrowShown : FigureArrow → Bool
  arrowDirection : FigureArrow → VectorDirection
  velocityPerpendicularToForce : Bool
  centerToParticleRadiusLineShown : Bool
  radiusLineLabel : String

/-!
Independent physical quantities in the proton-orbit experiment.  In
particular, `ballCharge` is not defined from an answer choice or from the
recorded value `-9.9 * 10^-12 C`.
-/
structure ProtonOrbitSetup where
  chamberMedium : ChamberMedium
  orbitingParticleSpecies : ParticleSpecies
  centralBodyModel : CentralBodyModel
  ballDiameter : LengthQuantity
  clearanceAboveSurface : LengthQuantity
  orbitRadius : LengthQuantity
  orbitalPeriod : DurationQuantity
  protonMass : MassQuantity
  protonCharge : SignedChargeQuantity
  ballCharge : SignedChargeQuantity
  protonVelocity : SpatialVelocityQuantity
  electricFieldMagnitudeAtProton : ElectricFieldMagnitudeQuantity
  electricForceOnProton : SpatialForceQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  ballCenter : Space 3
  protonPosition : Space 3
  inwardRadialUnit : EuclideanSpace ℝ (Fin 3)
  tangentUnit : EuclideanSpace ℝ (Fin 3)
  electricFieldDirection : VectorDirection
  electricForceDirection : VectorDirection
  velocityDirection : VectorDirection
  figure : ChargedBallOrbitFigure

/-! ## Source data, primary-image evidence, and physical geometry -/

/-- The prose's object and environment identifications. -/
structure MatchesWrittenScenario (setup : ProtonOrbitSetup) : Prop where
  chamberIsVacuum : setup.chamberMedium = .vacuum
  orbitingParticleIsProton : setup.orbitingParticleSpecies = .proton
  centralBodyIsMetalBall : setup.centralBodyModel = .conductingSphere

/-!
The three numerical readouts printed in the prose.  They contain no charge
readout for the ball.
-/
structure MatchesProblemReadouts (setup : ProtonOrbitSetup) : Prop where
  ballDiameterCentimeters :
    lengthInCentimeters setup.ballDiameter = 1
  clearanceMillimeters :
    lengthInMillimeters setup.clearanceAboveSurface = 1
  periodMicroseconds :
    durationInMicroseconds setup.orbitalPeriod = 1

/-!
Primary-raster evidence.  Inward field and force arrows and the ball's
negative marks are recorded as observations, while the physical reason for
their directions is supplied separately by the Coulomb and force laws.
-/
structure MatchesPrimaryOrbitFigure (setup : ProtonOrbitSetup) : Prop where
  centralSphereShown : setup.figure.centralSphereShown = true
  centralSphereLabel : setup.figure.centralSphereLabel = "Q"
  negativeMarksShown : setup.figure.negativeSurfaceMarksShown = true
  orbitingMarkerShown : setup.figure.orbitingParticleShown = true
  orbitingMarkerLabel : setup.figure.orbitingParticleLabel = "e"
  orbitingMarkerHasPlusSign :
    setup.figure.positiveGlyphOnOrbitingParticle = true
  everyNamedArrowShown : ∀ arrow, setup.figure.arrowShown arrow = true
  fieldArrowPointsInward :
    setup.figure.arrowDirection .electricField = .radiallyInward
  forceArrowPointsInward :
    setup.figure.arrowDirection .electricForce = .radiallyInward
  velocityArrowIsTangential :
    setup.figure.arrowDirection .velocity = .tangential
  velocityAndForceDrawnPerpendicular :
    setup.figure.velocityPerpendicularToForce = true
  radiusLineShown : setup.figure.centerToParticleRadiusLineShown = true
  radiusLabel : setup.figure.radiusLineLabel = "r"
  physicalFieldMatchesArrow :
    setup.electricFieldDirection =
      setup.figure.arrowDirection .electricField
  physicalForceMatchesArrow :
    setup.electricForceDirection =
      setup.figure.arrowDirection .electricForce
  physicalVelocityMatchesArrow :
    setup.velocityDirection = setup.figure.arrowDirection .velocity

/-!
The center-to-proton radius is the ball radius plus the stated clearance.
This is the geometric interpretation of "1.0 mm above the surface", not a
charge conclusion.
-/
structure SatisfiesOrbitRadiusGeometry (setup : ProtonOrbitSetup) : Prop where
  orbitRadiusFromDiameterAndClearance :
    lengthInMeters setup.orbitRadius =
      lengthInMeters setup.ballDiameter / 2 +
        lengthInMeters setup.clearanceAboveSurface
  protonPositionAtOrbitRadius :
    ‖setup.protonPosition - setup.ballCenter‖ =
      lengthInMeters setup.orbitRadius

/-! ## Physical constants, positivity, and governing laws -/

/-!
Rounded school values used for the numerical multiple-choice calculation.
They are independent calibration data and contain no value for `ballCharge`.
-/
structure UsesTextbookProtonAndCoulombConstants
    (setup : ProtonOrbitSetup) : Prop where
  protonMassKilograms :
    massInKilograms setup.protonMass = (1.67 : ℝ) / 10 ^ 27
  protonChargeCoulombs :
    chargeInCoulombs setup.protonCharge = (1.60 : ℝ) / 10 ^ 19
  coulombConstantSI :
    setup.electromagneticSystem.coulombConstant =
      (8.99 : ℝ) * 10 ^ 9

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalProtonOrbitParameters
    (setup : ProtonOrbitSetup) : Prop where
  diameterPositive : 0 < lengthInMeters setup.ballDiameter
  clearancePositive : 0 < lengthInMeters setup.clearanceAboveSurface
  orbitRadiusPositive : 0 < lengthInMeters setup.orbitRadius
  orbitalPeriodPositive : 0 < durationInSeconds setup.orbitalPeriod
  protonMassPositive : 0 < massInKilograms setup.protonMass
  protonChargePositive : 0 < chargeInCoulombs setup.protonCharge
  ballChargeNonzero : chargeInCoulombs setup.ballCharge ≠ 0
  fieldMagnitudePositive :
    0 < electricFieldMagnitudeInNewtonsPerCoulomb
      setup.electricFieldMagnitudeAtProton
  forceMagnitudePositive :
    0 < forceMagnitudeInNewtons setup.electricForceOnProton
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  inwardRadialDirectionIsUnit : ‖setup.inwardRadialUnit‖ = 1
  tangentDirectionIsUnit : ‖setup.tangentUnit‖ = 1

/-!
Exterior spherical Coulomb law for the charged conducting ball.  The field
magnitude is `k |Q| / r²`, and its inward/outward orientation records the sign
of the source charge.  This is a general law and does not assign a numerical
value to `Q`.
-/
structure SatisfiesExteriorSphericalCoulombFieldLaw
    (setup : ProtonOrbitSetup) : Prop where
  fieldMagnitudeFromBallCharge :
    electricFieldMagnitudeInNewtonsPerCoulomb
        setup.electricFieldMagnitudeAtProton =
      setup.electromagneticSystem.coulombConstant *
        |chargeInCoulombs setup.ballCharge| /
        lengthInMeters setup.orbitRadius ^ 2
  inwardFieldIffBallChargeNegative :
    setup.electricFieldDirection = .radiallyInward ↔
      chargeInCoulombs setup.ballCharge < 0
  electricFieldVectorAtProton :
    setup.electricField setup.observationTime setup.protonPosition =
      (electricFieldMagnitudeInNewtonsPerCoulomb
          setup.electricFieldMagnitudeAtProton) • setup.inwardRadialUnit

/-!
For the positive proton, the electric force has magnitude `q E` and points in
the same direction as the electric field.  No orbital-charge answer occurs in
this force law.
-/
structure SatisfiesElectricForceLawOnProton
    (setup : ProtonOrbitSetup) : Prop where
  forceMagnitudeIsChargeTimesField :
    forceMagnitudeInNewtons setup.electricForceOnProton =
      chargeInCoulombs setup.protonCharge *
        electricFieldMagnitudeInNewtonsPerCoulomb
          setup.electricFieldMagnitudeAtProton
  forceDirectionMatchesField :
    setup.electricForceDirection = setup.electricFieldDirection
  forceVectorPointsInward :
    forceVectorInNewtons setup.electricForceOnProton =
      (forceMagnitudeInNewtons setup.electricForceOnProton) •
        setup.inwardRadialUnit

/-!
Uniform circular motion: the speed is circumference divided by period, the
inward electric force supplies `m v² / r`, and the velocity is tangent to the
orbit and perpendicular to the radius.
-/
structure SatisfiesUniformCircularOrbitLaws
    (setup : ProtonOrbitSetup) : Prop where
  speedFromPeriod :
    speedInMetersPerSecond setup.protonVelocity =
      2 * Real.pi * lengthInMeters setup.orbitRadius /
        durationInSeconds setup.orbitalPeriod
  electricForceSuppliesCentripetalForce :
    forceMagnitudeInNewtons setup.electricForceOnProton =
      massInKilograms setup.protonMass *
        speedInMetersPerSecond setup.protonVelocity ^ 2 /
        lengthInMeters setup.orbitRadius
  forcePointsTowardCenter :
    setup.electricForceDirection = .radiallyInward
  velocityIsTangential : setup.velocityDirection = .tangential
  velocityVectorIsTangential :
    velocityVectorInMetersPerSecond setup.protonVelocity =
      (speedInMetersPerSecond setup.protonVelocity) • setup.tangentUnit
  tangentPerpendicularToRadius :
    inner ℝ setup.tangentUnit setup.inwardRadialUnit = 0

/-! ## Derived orbit relations and multiple-choice target -/

/-- The stated diameter and surface clearance give an orbital radius of `6 mm`. -/
lemma orbit_radius_in_meters
    (setup : ProtonOrbitSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_geometry : SatisfiesOrbitRadiusGeometry setup) :
    lengthInMeters setup.orbitRadius = 6 / 1000 := by
  rcases _readouts with ⟨hdiameter, hclearance, _⟩
  rcases _geometry with ⟨hradius, _⟩
  unfold lengthInCentimeters at hdiameter
  unfold lengthInMillimeters at hclearance
  norm_num at hdiameter hclearance ⊢
  linarith [hradius]

/-!
Eliminating the field, force, and speed from the governing laws gives the
signed source-charge formula.  Its leading minus sign is derived from the
inward field and the sign clause of Coulomb's law.
-/
lemma signed_ball_charge_from_circular_orbit
    (setup : ProtonOrbitSetup)
    (_figure : MatchesPrimaryOrbitFigure setup)
    (_physical : HasPhysicalProtonOrbitParameters setup)
    (_coulomb : SatisfiesExteriorSphericalCoulombFieldLaw setup)
    (_electricForce : SatisfiesElectricForceLawOnProton setup)
    (_circular : SatisfiesUniformCircularOrbitLaws setup) :
    chargeInCoulombs setup.ballCharge =
      -(massInKilograms setup.protonMass *
          (2 * Real.pi * lengthInMeters setup.orbitRadius /
            durationInSeconds setup.orbitalPeriod) ^ 2 *
          lengthInMeters setup.orbitRadius /
          (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs setup.protonCharge)) := by
  have hfieldIn :
      setup.electricFieldDirection = .radiallyInward := by
    rw [_figure.physicalFieldMatchesArrow, _figure.fieldArrowPointsInward]
  have hchargeNegative :
      chargeInCoulombs setup.ballCharge < 0 :=
    _coulomb.inwardFieldIffBallChargeNegative.mp hfieldIn
  have hradius :
      lengthInMeters setup.orbitRadius ≠ 0 :=
    ne_of_gt _physical.orbitRadiusPositive
  have hperiod :
      durationInSeconds setup.orbitalPeriod ≠ 0 :=
    ne_of_gt _physical.orbitalPeriodPositive
  have hprotonCharge :
      chargeInCoulombs setup.protonCharge ≠ 0 :=
    ne_of_gt _physical.protonChargePositive
  have hcoulombConstant :
      setup.electromagneticSystem.coulombConstant ≠ 0 :=
    ne_of_gt _physical.coulombConstantPositive
  have hfieldMagnitude := _coulomb.fieldMagnitudeFromBallCharge
  rw [abs_of_neg hchargeNegative] at hfieldMagnitude
  have hforceBalance :=
    _circular.electricForceSuppliesCentripetalForce
  rw [_electricForce.forceMagnitudeIsChargeTimesField,
    hfieldMagnitude, _circular.speedFromPeriod] at hforceBalance
  field_simp [hradius, hperiod, hprotonCharge, hcoulombConstant] at hforceBalance ⊢
  ring_nf at hforceBalance ⊢
  nlinarith

/-- Labels attached to the four displayed charge choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed charge in coulombs printed beside each answer label. -/
def answerChargeInCoulombs : AnswerChoice → ℝ
  | .A => -(1.3 : ℝ) / 10 ^ 12
  | .B => (5.3 : ℝ) / 10 ^ 14
  | .C => -(9.9 : ℝ) / 10 ^ 12
  | .D => (3.5 : ℝ) / 10 ^ 14

/-- The answer label recorded by the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Half of the last displayed decimal place in choice C. -/
def choiceCDisplayToleranceInCoulombs : ℝ :=
  (0.05 : ℝ) / 10 ^ 12

/-- The physical charge agrees with choice C to its displayed precision. -/
def BallChargeRoundsToChoiceC (setup : ProtonOrbitSetup) : Prop :=
  |chargeInCoulombs setup.ballCharge - answerChargeInCoulombs .C| <
    choiceCDisplayToleranceInCoulombs

/-- A choice is at least as close to the physical charge as every alternative. -/
def IsClosestDisplayedCharge
    (setup : ProtonOrbitSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |chargeInCoulombs setup.ballCharge - answerChargeInCoulombs choice| ≤
      |chargeInCoulombs setup.ballCharge -
        answerChargeInCoulombs alternative|

/-!
The textbook constants and orbit data put the charge between
`-9.95 * 10^-12 C` and `-9.85 * 10^-12 C`, so it displays as
`-9.9 * 10^-12 C`.
-/
lemma ball_charge_choiceC_rounding_bounds
    (setup : ProtonOrbitSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_geometry : SatisfiesOrbitRadiusGeometry setup)
    (_constants : UsesTextbookProtonAndCoulombConstants setup)
    (_figure : MatchesPrimaryOrbitFigure setup)
    (_physical : HasPhysicalProtonOrbitParameters setup)
    (_coulomb : SatisfiesExteriorSphericalCoulombFieldLaw setup)
    (_electricForce : SatisfiesElectricForceLawOnProton setup)
    (_circular : SatisfiesUniformCircularOrbitLaws setup) :
    -(9.95 : ℝ) / 10 ^ 12 < chargeInCoulombs setup.ballCharge ∧
      chargeInCoulombs setup.ballCharge < -(9.85 : ℝ) / 10 ^ 12 := by
  have hradius := orbit_radius_in_meters setup _readouts _geometry
  have hperiod :
      durationInSeconds setup.orbitalPeriod = 1 / (10 : ℝ) ^ 6 := by
    have hreadout := _readouts.periodMicroseconds
    unfold durationInMicroseconds at hreadout
    norm_num at hreadout ⊢
    linarith
  have hcharge :=
    signed_ball_charge_from_circular_orbit setup _figure _physical
      _coulomb _electricForce _circular
  rw [hradius, _constants.protonMassKilograms,
    _constants.protonChargeCoulombs, _constants.coulombConstantSI,
    hperiod] at hcharge
  norm_num at hcharge ⊢
  ring_nf at hcharge ⊢
  rw [hcharge]
  have hpiUpper : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by
    apply (sq_lt_sq).2
    rw [abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 3.1416)]
    exact Real.pi_lt_d4
  have hpiLower : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by
    apply (sq_lt_sq).2
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3.14),
      abs_of_pos Real.pi_pos]
    exact Real.pi_gt_d2
  norm_num at hpiUpper hpiLower
  constructor <;> linarith

/-!
**Blueprint target** `thm:physics:phyx_mini_0912:target`.

The ball's charge is negative and rounds to `-9.9 * 10^-12 C`; among the
four displayed values, this uniquely selects the dataset's recorded answer C.
The target sign, rounded value, and answer label occur only in conclusions and
answer-display definitions, never in the physical setup or laws.
-/
theorem problem_phyx_mini_0912
    (setup : ProtonOrbitSetup)
    (_scenario : MatchesWrittenScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryOrbitFigure setup)
    (_geometry : SatisfiesOrbitRadiusGeometry setup)
    (_constants : UsesTextbookProtonAndCoulombConstants setup)
    (_physical : HasPhysicalProtonOrbitParameters setup)
    (_coulomb : SatisfiesExteriorSphericalCoulombFieldLaw setup)
    (_electricForce : SatisfiesElectricForceLawOnProton setup)
    (_circular : SatisfiesUniformCircularOrbitLaws setup) :
    chargeInCoulombs setup.ballCharge < 0 ∧
      BallChargeRoundsToChoiceC setup ∧
      IsClosestDisplayedCharge setup recordedDatasetAnswer ∧
      ∀ choice : AnswerChoice,
        IsClosestDisplayedCharge setup choice ↔ choice = .C := by
  rcases ball_charge_choiceC_rounding_bounds setup _readouts _geometry
      _constants _figure _physical _coulomb _electricForce _circular with
    ⟨hlower, hupper⟩
  have hnegative : chargeInCoulombs setup.ballCharge < 0 := by
    norm_num at hupper ⊢
    linarith
  have hrounds : BallChargeRoundsToChoiceC setup := by
    unfold BallChargeRoundsToChoiceC
    rw [abs_lt]
    unfold answerChargeInCoulombs choiceCDisplayToleranceInCoulombs
    norm_num at hlower hupper ⊢
    constructor <;> linarith
  have hfarA :
      choiceCDisplayToleranceInCoulombs <
        |chargeInCoulombs setup.ballCharge -
          answerChargeInCoulombs .A| := by
    rw [abs_of_neg]
    · unfold answerChargeInCoulombs choiceCDisplayToleranceInCoulombs
      norm_num at hupper ⊢
      linarith
    · unfold answerChargeInCoulombs
      norm_num at hupper ⊢
      linarith
  have hfarB :
      choiceCDisplayToleranceInCoulombs <
        |chargeInCoulombs setup.ballCharge -
          answerChargeInCoulombs .B| := by
    rw [abs_of_neg]
    · unfold answerChargeInCoulombs choiceCDisplayToleranceInCoulombs
      norm_num at hupper ⊢
      linarith
    · unfold answerChargeInCoulombs
      norm_num at hupper ⊢
      linarith
  have hfarD :
      choiceCDisplayToleranceInCoulombs <
        |chargeInCoulombs setup.ballCharge -
          answerChargeInCoulombs .D| := by
    rw [abs_of_neg]
    · unfold answerChargeInCoulombs choiceCDisplayToleranceInCoulombs
      norm_num at hupper ⊢
      linarith
    · unfold answerChargeInCoulombs
      norm_num at hupper ⊢
      linarith
  have hclosestC : IsClosestDisplayedCharge setup .C := by
    intro alternative
    cases alternative with
    | A => exact le_trans (le_of_lt hrounds) (le_of_lt hfarA)
    | B => exact le_trans (le_of_lt hrounds) (le_of_lt hfarB)
    | C => exact le_rfl
    | D => exact le_trans (le_of_lt hrounds) (le_of_lt hfarD)
  refine ⟨hnegative, hrounds, ?_, ?_⟩
  · simpa [recordedDatasetAnswer] using hclosestC
  · intro choice
    constructor
    · intro hclosest
      cases choice with
      | A =>
          exfalso
          exact (not_lt_of_ge (hclosest .C)) (lt_trans hrounds hfarA)
      | B =>
          exfalso
          exact (not_lt_of_ge (hclosest .C)) (lt_trans hrounds hfarB)
      | C => rfl
      | D =>
          exfalso
          exact (not_lt_of_ge (hclosest .C)) (lt_trans hrounds hfarD)
    · intro hchoice
      subst choice
      exact hclosestC

end PhyXMiniProblems.ProblemPhyXMini0912
