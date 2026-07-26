import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0783

open Dimension

/-!
# Angular acceleration of a massive Atwood wheel

The supplied figure shows block `A` on the right, block `B` on the left, and
the suspended wheel `C` above them.  The prose gives masses `4.00 kg` and
`2.00 kg`, wheel inertia `0.220 kg m²`, wheel radius `0.120 m`, and states
that the cord does not slip on the wheel.

Physical masses, lengths, accelerations, tensions, and moment of inertia are
unit-independent Physlib quantities.  Real numbers appear only at coherent
unit-readout boundaries and for the displayed answer data.  The cord
tensions and both acceleration magnitudes are independent observables; the
requested angular acceleration is not defined from the recorded answer.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- Linear acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A scalar moment of inertia has physical dimension `M L²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- Radians are dimensionless, so angular acceleration has dimension `T⁻²`. -/
def angularAccelerationDimension : Dimension :=
  T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative linear-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude, used for the two cord tensions. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative moment of inertia about the wheel axle. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative angular-acceleration magnitude. -/
abbrev AngularAccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim angularAccelerationDimension NNReal)

/-- Read a mass in the coherent mass unit selected by `units`. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  ((mass units).val : ℝ)

/-- Read a length in the coherent length unit selected by `units`. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read linear acceleration in the coherent units selected by `units`. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-- Read a force magnitude in the coherent units selected by `units`. -/
def forceReadout
    (units : UnitChoices) (force : ForceMagnitudeQuantity) : ℝ :=
  ((force units).val : ℝ)

/-- Read moment of inertia in coherent mass and length units. -/
def momentOfInertiaReadout
    (units : UnitChoices) (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia units).val : ℝ)

/-- Read angular acceleration in inverse-square selected-time units. -/
def angularAccelerationReadout
    (units : UnitChoices)
    (acceleration : AngularAccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-- SI kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout UnitChoices.SI mass

/-- SI metre readout of a length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- SI metre-per-second-squared readout of linear acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  accelerationReadout UnitChoices.SI acceleration

/-- SI newton readout of a force magnitude. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  forceReadout UnitChoices.SI force

/-- SI kilogram-square-metre readout of moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout UnitChoices.SI inertia

/-- SI readout of angular acceleration, numerically in radians per second squared. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationMagnitudeQuantity) : ℝ :=
  angularAccelerationReadout UnitChoices.SI acceleration

/-! ## Apparatus roles and primary-figure vocabulary -/

/-- The two hanging blocks carrying the figure labels `A` and `B`. -/
inductive Block where
  | A
  | B
  deriving DecidableEq, Repr, Fintype

/-- Labels printed in the supplied raster. -/
inductive FigureLabel where
  | A
  | B
  | C
  deriving DecidableEq, Repr, Fintype

/-- Horizontal positions relative to the wheel in the front-view diagram. -/
inductive HorizontalSide where
  | left
  | center
  | right
  deriving DecidableEq, Repr

/-- Positive directions used for scalar block equations. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Positive sense used for the wheel's angular acceleration. -/
inductive RotationDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Idealization of the single cord joining the two blocks. -/
inductive CordModel where
  | masslessInextensibleTaut
  | other
  deriving DecidableEq, Repr

/-- Contact model between the cord and the wheel surface. -/
inductive CordWheelContactModel where
  | noSlip
  | slipping
  deriving DecidableEq, Repr

/-- Support and bearing model for wheel `C`. -/
inductive WheelAxleModel where
  | fixedFrictionless
  | other
  deriving DecidableEq, Repr

/-!
Qualitative evidence read from the primary raster.  Pixel distances are not
treated as metric data, and the bitmap contains neither numerical values nor
motion arrows.
-/
structure SuppliedAtwoodFigure where
  showsBlock : Block → Bool
  showsWheel : Bool
  showsCord : Bool
  blockLabel : Block → FigureLabel
  wheelLabel : FigureLabel
  blockSideOfWheel : Block → HorizontalSide
  wheelIsAboveBothBlocks : Bool
  wheelIsSuspendedFromCeiling : Bool
  cordRunsOverWheel : Bool
  cordSegmentAtBlockIsVertical : Block → Bool
  eachBlockIsAttachedToCord : Bool
  blockAAppearsLargerThanBlockB : Bool
  centralAxleIsVisible : Bool

/-!
Independent physical quantities and response observables of the apparatus.
The common linear acceleration, wheel angular acceleration, and two tensions
are fields constrained below by mechanics; none is defined from an answer
choice.
-/
structure AtwoodWheelSetup where
  blockMass : Block → MassQuantity
  wheelRadius : LengthQuantity
  wheelMomentOfInertiaAboutAxle : MomentOfInertiaQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  commonCordAccelerationMagnitude : AccelerationMagnitudeQuantity
  wheelAngularAccelerationMagnitude : AngularAccelerationMagnitudeQuantity
  tensionOnSide : Block → ForceMagnitudeQuantity
  positiveBlockDirection : Block → VerticalDirection
  positiveWheelDirection : RotationDirection
  cordModel : CordModel
  contactModel : CordWheelContactModel
  axleModel : WheelAxleModel
  figure : SuppliedAtwoodFigure

/-! ## Scenario, prose data, and figure readouts -/

/-!
The ideal Atwood-machine model and component-sign convention.  Positive
translation is downward for the heavier-side coordinate `A`, upward for `B`,
and clockwise for wheel `C` in the supplied front view.  These are coordinate
choices, not numerical acceleration conclusions.
-/
structure MatchesAtwoodScenario (setup : AtwoodWheelSetup) : Prop where
  cordIsMasslessInextensibleAndTaut :
    setup.cordModel = .masslessInextensibleTaut
  cordDoesNotSlipOnWheel : setup.contactModel = .noSlip
  wheelAxleIsFixedAndFrictionless : setup.axleModel = .fixedFrictionless
  blockAPositiveDirection : setup.positiveBlockDirection .A = .downward
  blockBPositiveDirection : setup.positiveBlockDirection .B = .upward
  wheelPositiveDirection : setup.positiveWheelDirection = .clockwise

/-!
Numerical readouts supplied in the prose.  The requested wheel angular
acceleration and the cord tensions do not occur in this structure.
-/
structure MatchesProblemReadouts (setup : AtwoodWheelSetup) : Prop where
  blockAMassKilograms : massInKilograms (setup.blockMass .A) = 4
  blockBMassKilograms : massInKilograms (setup.blockMass .B) = 2
  wheelInertiaKilogramMetersSquared :
    momentOfInertiaInKilogramMetersSquared
      setup.wheelMomentOfInertiaAboutAxle = 11 / 50
  wheelRadiusMeters : lengthInMeters setup.wheelRadius = 3 / 25

/-!
Primary-image evidence: `B` is left of wheel `C`, `A` is right of it, the
wheel is suspended above both attached blocks, and `A` is drawn larger.  No
numerical mechanics result is read from the image.
-/
structure MatchesSuppliedAtwoodFigure (setup : AtwoodWheelSetup) : Prop where
  bothBlocksShown : ∀ block : Block, setup.figure.showsBlock block = true
  wheelShown : setup.figure.showsWheel = true
  cordShown : setup.figure.showsCord = true
  blockALabel : setup.figure.blockLabel .A = .A
  blockBLabel : setup.figure.blockLabel .B = .B
  wheelCLabel : setup.figure.wheelLabel = .C
  blockAOnRight : setup.figure.blockSideOfWheel .A = .right
  blockBOnLeft : setup.figure.blockSideOfWheel .B = .left
  wheelAboveBlocks : setup.figure.wheelIsAboveBothBlocks = true
  wheelSuspended : setup.figure.wheelIsSuspendedFromCeiling = true
  cordPassesOverWheel : setup.figure.cordRunsOverWheel = true
  verticalCordSegments :
    ∀ block : Block, setup.figure.cordSegmentAtBlockIsVertical block = true
  blocksAttached : setup.figure.eachBlockIsAttachedToCord = true
  blockAAppearsLarger : setup.figure.blockAAppearsLargerThanBlockB = true
  axleVisible : setup.figure.centralAxleIsVisible = true

/-!
The multiple-choice value uses the conventional introductory-mechanics
calibration `g = 9.8 m/s²`, which is implicit rather than printed in the
source.
-/
structure MatchesTerrestrialGravityCalibration
    (setup : AtwoodWheelSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude = 49 / 5

/-- Positivity and nondegeneracy of the physical input parameters. -/
structure HasPhysicalAtwoodParameters (setup : AtwoodWheelSetup) : Prop where
  blockAMassPositive : 0 < massInKilograms (setup.blockMass .A)
  blockBMassPositive : 0 < massInKilograms (setup.blockMass .B)
  wheelRadiusPositive : 0 < lengthInMeters setup.wheelRadius
  wheelInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.wheelMomentOfInertiaAboutAxle
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  tensionAPositive : 0 < forceInNewtons (setup.tensionOnSide .A)
  tensionBPositive : 0 < forceInNewtons (setup.tensionOnSide .B)

/-! ## Governing translational and rotational mechanics -/

/-!
Scalar-component laws for the positive directions fixed above:

* `m_A g - T_A = m_A a` for descending-side block `A`;
* `T_B - m_B g = m_B a` for ascending-side block `B`;
* `(T_A - T_B) r = I α` for wheel `C`;
* `a = r α` from no slipping.

The two tensions remain distinct because the wheel has nonzero moment of
inertia.  All equations hold in any coherent choice of mechanical units.
-/
structure SatisfiesAtwoodWheelDynamics (setup : AtwoodWheelSetup) : Prop where
  blockANewtonSecondLaw :
    ∀ units : UnitChoices,
      massReadout units (setup.blockMass .A) *
            accelerationReadout units
              setup.gravitationalAccelerationMagnitude -
          forceReadout units (setup.tensionOnSide .A) =
        massReadout units (setup.blockMass .A) *
          accelerationReadout units setup.commonCordAccelerationMagnitude
  blockBNewtonSecondLaw :
    ∀ units : UnitChoices,
      forceReadout units (setup.tensionOnSide .B) -
          massReadout units (setup.blockMass .B) *
            accelerationReadout units
              setup.gravitationalAccelerationMagnitude =
        massReadout units (setup.blockMass .B) *
          accelerationReadout units setup.commonCordAccelerationMagnitude
  wheelTorqueLaw :
    ∀ units : UnitChoices,
      (forceReadout units (setup.tensionOnSide .A) -
            forceReadout units (setup.tensionOnSide .B)) *
          lengthReadout units setup.wheelRadius =
        momentOfInertiaReadout units
            setup.wheelMomentOfInertiaAboutAxle *
          angularAccelerationReadout units
            setup.wheelAngularAccelerationMagnitude
  noSlipAccelerationConstraint :
    ∀ units : UnitChoices,
      accelerationReadout units setup.commonCordAccelerationMagnitude =
        lengthReadout units setup.wheelRadius *
          angularAccelerationReadout units
            setup.wheelAngularAccelerationMagnitude

/-! ## Derived acceleration and answer selection -/

/-!
Eliminating the two tensions and the common linear acceleration gives the
standard massive-pulley Atwood formula.  This is a derived lemma, not a field
of the governing-law structure.
-/
lemma wheelAngularAccelerationFormula
    (setup : AtwoodWheelSetup)
    (hPhysical : HasPhysicalAtwoodParameters setup)
    (hDynamics : SatisfiesAtwoodWheelDynamics setup) :
    ∀ units : UnitChoices,
      angularAccelerationReadout units
          setup.wheelAngularAccelerationMagnitude =
        ((massReadout units (setup.blockMass .A) -
              massReadout units (setup.blockMass .B)) *
            accelerationReadout units
              setup.gravitationalAccelerationMagnitude *
            lengthReadout units setup.wheelRadius) /
          (momentOfInertiaReadout units
                setup.wheelMomentOfInertiaAboutAxle +
            (massReadout units (setup.blockMass .A) +
                massReadout units (setup.blockMass .B)) *
              lengthReadout units setup.wheelRadius ^ 2) := by
  intro units
  have hInertiaPositive :
      0 <
        momentOfInertiaReadout units
          setup.wheelMomentOfInertiaAboutAxle := by
    have hScale :
        0 <
          (UnitChoices.dimScale UnitChoices.SI units
              momentOfInertiaDimension : ℝ) := by
      exact_mod_cast
        UnitChoices.dimScale_pos UnitChoices.SI units
          momentOfInertiaDimension
    have hCoherence :=
      setup.wheelMomentOfInertiaAboutAxle.2 UnitChoices.SI units
    rw [momentOfInertiaReadout, hCoherence]
    change
      0 <
        (UnitChoices.dimScale UnitChoices.SI units
              momentOfInertiaDimension : ℝ) *
          momentOfInertiaReadout UnitChoices.SI
            setup.wheelMomentOfInertiaAboutAxle
    exact mul_pos hScale hPhysical.wheelInertiaPositive
  have hDenominatorPositive :
      0 <
        momentOfInertiaReadout units
              setup.wheelMomentOfInertiaAboutAxle +
          (massReadout units (setup.blockMass .A) +
              massReadout units (setup.blockMass .B)) *
            lengthReadout units setup.wheelRadius ^ 2 := by
    have hMassANonnegative :
        0 ≤ massReadout units (setup.blockMass .A) := by
      exact NNReal.coe_nonneg _
    have hMassBNonnegative :
        0 ≤ massReadout units (setup.blockMass .B) := by
      exact NNReal.coe_nonneg _
    have hRadiusSquaredNonnegative :
        0 ≤ lengthReadout units setup.wheelRadius ^ 2 := sq_nonneg _
    positivity
  have hBlockA := hDynamics.blockANewtonSecondLaw units
  have hBlockB := hDynamics.blockBNewtonSecondLaw units
  have hTorque := hDynamics.wheelTorqueLaw units
  have hNoSlip := hDynamics.noSlipAccelerationConstraint units
  have hNetForce :
      (massReadout units (setup.blockMass .A) -
            massReadout units (setup.blockMass .B)) *
          accelerationReadout units setup.gravitationalAccelerationMagnitude =
        (forceReadout units (setup.tensionOnSide .A) -
            forceReadout units (setup.tensionOnSide .B)) +
          (massReadout units (setup.blockMass .A) +
              massReadout units (setup.blockMass .B)) *
            accelerationReadout units setup.commonCordAccelerationMagnitude := by
    linarith
  have hPolynomial :
      (massReadout units (setup.blockMass .A) -
            massReadout units (setup.blockMass .B)) *
          accelerationReadout units setup.gravitationalAccelerationMagnitude *
          lengthReadout units setup.wheelRadius =
        (momentOfInertiaReadout units
                setup.wheelMomentOfInertiaAboutAxle +
            (massReadout units (setup.blockMass .A) +
                massReadout units (setup.blockMass .B)) *
              lengthReadout units setup.wheelRadius ^ 2) *
          angularAccelerationReadout units
            setup.wheelAngularAccelerationMagnitude := by
    calc
      _ =
          ((forceReadout units (setup.tensionOnSide .A) -
                forceReadout units (setup.tensionOnSide .B)) +
            (massReadout units (setup.blockMass .A) +
                massReadout units (setup.blockMass .B)) *
              accelerationReadout units
                setup.commonCordAccelerationMagnitude) *
            lengthReadout units setup.wheelRadius := by rw [hNetForce]
      _ =
          (forceReadout units (setup.tensionOnSide .A) -
                forceReadout units (setup.tensionOnSide .B)) *
              lengthReadout units setup.wheelRadius +
            (massReadout units (setup.blockMass .A) +
                massReadout units (setup.blockMass .B)) *
              accelerationReadout units
                setup.commonCordAccelerationMagnitude *
              lengthReadout units setup.wheelRadius := by ring
      _ =
          momentOfInertiaReadout units
                setup.wheelMomentOfInertiaAboutAxle *
              angularAccelerationReadout units
                setup.wheelAngularAccelerationMagnitude +
            (massReadout units (setup.blockMass .A) +
                massReadout units (setup.blockMass .B)) *
              (lengthReadout units setup.wheelRadius *
                angularAccelerationReadout units
                  setup.wheelAngularAccelerationMagnitude) *
              lengthReadout units setup.wheelRadius := by
            rw [hTorque, hNoSlip]
      _ = _ := by ring
  apply (eq_div_iff (ne_of_gt hDenominatorPositive)).2
  nlinarith

/-- With the supplied SI data, the exact acceleration is `2940/383 rad/s²`. -/
lemma wheelAngularAccelerationExactSI
    (setup : AtwoodWheelSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : MatchesTerrestrialGravityCalibration setup)
    (hPhysical : HasPhysicalAtwoodParameters setup)
    (hDynamics : SatisfiesAtwoodWheelDynamics setup) :
    angularAccelerationInRadiansPerSecondSquared
        setup.wheelAngularAccelerationMagnitude = 2940 / 383 := by
  have hMassA := hReadouts.blockAMassKilograms
  have hMassB := hReadouts.blockBMassKilograms
  have hInertia := hReadouts.wheelInertiaKilogramMetersSquared
  have hRadius := hReadouts.wheelRadiusMeters
  have hGravitationalAcceleration :=
    hGravity.gravityMetersPerSecondSquared
  change
    massReadout UnitChoices.SI (setup.blockMass .A) = 4 at hMassA
  change
    massReadout UnitChoices.SI (setup.blockMass .B) = 2 at hMassB
  change
    momentOfInertiaReadout UnitChoices.SI
      setup.wheelMomentOfInertiaAboutAxle = 11 / 50 at hInertia
  change
    lengthReadout UnitChoices.SI setup.wheelRadius = 3 / 25 at hRadius
  change
    accelerationReadout UnitChoices.SI
      setup.gravitationalAccelerationMagnitude = 49 / 5 at hGravitationalAcceleration
  change
    angularAccelerationReadout UnitChoices.SI
      setup.wheelAngularAccelerationMagnitude = 2940 / 383
  rw [wheelAngularAccelerationFormula setup hPhysical hDynamics UnitChoices.SI]
  rw [hMassA, hMassB, hInertia, hRadius, hGravitationalAcceleration]
  norm_num

/-- The four response labels printed beside the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr, Fintype

/-- Displayed angular-acceleration readout for each answer choice. -/
def answerChoiceRadiansPerSecondSquared : AnswerChoice → ℝ
  | .A => 607 / 50
  | .B => 192 / 25
  | .C => 132 / 25
  | .D => 167 / 25

/-!
An exact acceleration matches a two-decimal displayed answer when the error
is below half of one hundredth.  This generic rounding criterion does not
single out any answer choice by definition.
-/
def MatchesDisplayedAnswer
    (setup : AtwoodWheelSetup) (choice : AnswerChoice) : Prop :=
  abs
      (angularAccelerationInRadiansPerSecondSquared
          setup.wheelAngularAccelerationMagnitude -
        answerChoiceRadiansPerSecondSquared choice) <
    1 / 200

/-!
The wheel's exact SI angular acceleration is `2940/383 rad/s²`, which rounds
to `7.68 rad/s²`; hence the recorded multiple-choice answer is `B`.

This declaration formalizes
`thm:physics:phyx_mini_0783:target` from the blueprint chapter.
-/
theorem atwoodWheelAngularAcceleration
    (setup : AtwoodWheelSetup)
    (hScenario : MatchesAtwoodScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedAtwoodFigure setup)
    (hGravity : MatchesTerrestrialGravityCalibration setup)
    (hPhysical : HasPhysicalAtwoodParameters setup)
    (hDynamics : SatisfiesAtwoodWheelDynamics setup) :
    angularAccelerationInRadiansPerSecondSquared
          setup.wheelAngularAccelerationMagnitude = 2940 / 383 ∧
      MatchesDisplayedAnswer setup .B := by
  clear hScenario hFigure
  have hExact :=
    wheelAngularAccelerationExactSI setup hReadouts hGravity hPhysical hDynamics
  constructor
  · exact hExact
  · rw [MatchesDisplayedAnswer, hExact]
    norm_num [answerChoiceRadiansPerSecondSquared, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0783
