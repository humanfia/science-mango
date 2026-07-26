import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0705

open Dimension

/-!
# Initial angular acceleration of an eccentrically supported disk

The primary image resolves an ambiguity in its auxiliary caption.  The
`10.0 cm` label is the disk's diameter.  The fixed axle is `2.5 cm` to the
right of the disk center, and the cable contact at the right rim is another
`2.5 cm` to the right of the axle.  Consequently both the upward cable force
and the downward weight exert counterclockwise torque about the axle.

Physical mass, length, force, acceleration, moment of inertia, torque, and
angular acceleration are represented by Physlib's unit-covariant
`Dimensionful (WithDim ...)` quantities.  Real numbers occur only as named
readouts in coherent units, signed planar components, and displayed answer
values.  Radians carry no additional physical dimension, so angular
acceleration has inverse-time-squared dimension.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` contains only stated data, image labels,
  metric readouts, and the pin-release condition;
* `UsesStandardEarthGravity` supplies `9.8 m/s²`;
* `SatisfiesDiskGeometry` states the radius/diameter relation;
* `SatisfiesPlanarRotationalDynamics` states the solid-disk inertia law,
  parallel-axis theorem, moment-arm torque laws, torque summation, and
  `τ = I α`;
* there are no previous-part results; and
* `initialAngularAcceleration_matches_choice_C` alone concludes the requested
  acceleration, its sense, and the nearest displayed choice.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative scalar moment of inertia about an axis normal to the disk. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A signed planar torque component about the fixed axle. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A signed angular acceleration; positive means counterclockwise. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def nonnegativeQuantityReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed dimensionful quantity in a coherent unit system. -/
def signedQuantityReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI length

/-- Centimetre readout used by the prose and the primary figure. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  nonnegativeQuantityReadout centimeterUnitChoices length

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI force

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI acceleration

/-- Kilogram-square-metre readout of a scalar moment of inertia. -/
def momentOfInertiaInKilogramSquareMeters
    (momentOfInertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI momentOfInertia

/-- Signed newton-metre readout of torque, positive counterclockwise. -/
def signedTorqueInNewtonMeters (torque : SignedTorqueQuantity) : ℝ :=
  signedQuantityReadout UnitChoices.SI torque

/-- Signed radians-per-second-squared readout of angular acceleration. -/
def angularAccelerationInRadiansPerSecondSquared
    (angularAcceleration : AngularAccelerationQuantity) : ℝ :=
  signedQuantityReadout UnitChoices.SI angularAcceleration

/-! ## Primary-figure labels and physical setup -/

/-- Labelled or mechanically distinguished points in image `705.png`. -/
inductive FigurePoint where
  | leftRimAtPin
  | diskCenter
  | axle
  | cableContactAtRightRim
  deriving DecidableEq, Fintype, Repr

/-- External forces acting immediately after the pin is removed. -/
inductive ReleaseForce where
  | cableTension
  | diskWeight
  | axleReaction
  deriving DecidableEq, Fintype, Repr

/-- Cardinal directions of the arrows in the supplied planar figure. -/
inductive PlanarDirection where
  | upward
  | downward
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Sense of rotation about the axle, viewed as in the figure. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Qualitative incidence, ordering, and arrow data carried by the image. -/
structure PrimaryDiskFigure where
  pointOnHorizontalDiameter : FigurePoint → Prop
  liesToRightOf : FigurePoint → FigurePoint → Prop
  forceApplicationPoint : ReleaseForce → FigurePoint
  forceArrowDirection : ReleaseForce → PlanarDirection
  pinRemovalArrowDirection : PlanarDirection
  diameterLineShown : Bool
  cableVerticalAtRightRim : Bool
  axleMarked : Bool
  diskCenterMarked : Bool

/-!
The disk and its independent physical observables.  In particular, the
moments of inertia, release torques, and initial angular acceleration are not
assigned numerical values here; the governing laws below constrain them.
-/
structure DiskMachineSetup where
  figure : PrimaryDiskFigure
  diskMass : MassQuantity
  diskDiameter : LengthQuantity
  diskRadius : LengthQuantity
  axleOffsetFromCenter : LengthQuantity
  cableOffsetFromAxle : LengthQuantity
  cableTensionMagnitude : ForceQuantity
  gravitationalAcceleration : AccelerationQuantity
  momentOfInertiaAboutCenter : MomentOfInertiaQuantity
  momentOfInertiaAboutAxle : MomentOfInertiaQuantity
  releaseTorqueAboutAxle : ReleaseForce → SignedTorqueQuantity
  netReleaseTorqueAboutAxle : SignedTorqueQuantity
  initialAngularAcceleration : AngularAccelerationQuantity
  initialRotationSense : RotationSense
  pinInitiallyPreventsRotation : Bool
  pinRemovedAtRelease : Bool
  diskInitiallyAtRest : Bool
  axleIsFixed : Bool

/-!
Numerical and categorical information stated in the prose or read from the
primary bitmap.  The two `2.5 cm` fields are respectively the center-to-axle
and axle-to-cable-contact segments.  No angular acceleration or answer label
appears in these premises.
-/
structure MatchesProblemAndPrimaryFigure (setup : DiskMachineSetup) : Prop where
  diskMassKilograms : massInKilograms setup.diskMass = 5
  diskDiameterCentimeters : lengthInCentimeters setup.diskDiameter = 10
  axleOffsetCentimeters :
    lengthInCentimeters setup.axleOffsetFromCenter = 5 / 2
  cableOffsetCentimeters :
    lengthInCentimeters setup.cableOffsetFromAxle = 5 / 2
  cableTensionNewtons : forceInNewtons setup.cableTensionMagnitude = 100
  everyDistinguishedPointOnDiameter :
    ∀ point : FigurePoint, setup.figure.pointOnHorizontalDiameter point
  axleRightOfCenter :
    setup.figure.liesToRightOf .axle .diskCenter
  cableContactRightOfAxle :
    setup.figure.liesToRightOf .cableContactAtRightRim .axle
  centerRightOfPin :
    setup.figure.liesToRightOf .diskCenter .leftRimAtPin
  tensionAppliedAtCableContact :
    setup.figure.forceApplicationPoint .cableTension =
      .cableContactAtRightRim
  weightAppliedAtCenter :
    setup.figure.forceApplicationPoint .diskWeight = .diskCenter
  axleReactionAppliedAtAxle :
    setup.figure.forceApplicationPoint .axleReaction = .axle
  tensionArrowUpward :
    setup.figure.forceArrowDirection .cableTension = .upward
  weightArrowDownward :
    setup.figure.forceArrowDirection .diskWeight = .downward
  axleReactionArrowDownward :
    setup.figure.forceArrowDirection .axleReaction = .downward
  pinRemovalArrowLeftward :
    setup.figure.pinRemovalArrowDirection = .leftward
  diameterLineVisible : setup.figure.diameterLineShown = true
  cableVerticalAtRightEdge : setup.figure.cableVerticalAtRightRim = true
  axleLabelVisible : setup.figure.axleMarked = true
  centerMarkVisible : setup.figure.diskCenterMarked = true
  pinInitiallyEngaged : setup.pinInitiallyPreventsRotation = true
  pinRemovedForRequestedInstant : setup.pinRemovedAtRelease = true
  initiallyAtRest : setup.diskInitiallyAtRest = true
  fixedAxle : setup.axleIsFixed = true

/-- The conventional textbook near-Earth gravitational acceleration. -/
structure UsesStandardEarthGravity (setup : DiskMachineSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-- Positivity and nondegeneracy conditions for the pictured apparatus. -/
structure HasPhysicalDiskParameters (setup : DiskMachineSetup) : Prop where
  diskMassPositive : 0 < massInKilograms setup.diskMass
  diskDiameterPositive : 0 < lengthInMeters setup.diskDiameter
  diskRadiusPositive : 0 < lengthInMeters setup.diskRadius
  axleOffsetPositive : 0 < lengthInMeters setup.axleOffsetFromCenter
  cableOffsetPositive : 0 < lengthInMeters setup.cableOffsetFromAxle
  tensionPositive : 0 < forceInNewtons setup.cableTensionMagnitude
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  axleMomentOfInertiaPositive :
    0 < momentOfInertiaInKilogramSquareMeters
      setup.momentOfInertiaAboutAxle

/-! ## Governing geometry and rotational dynamics -/

/-- Radius/diameter geometry for the circular disk. -/
structure SatisfiesDiskGeometry (setup : DiskMachineSetup) : Prop where
  radiusIsHalfDiameter :
    lengthInMeters setup.diskRadius =
      lengthInMeters setup.diskDiameter / 2
  centerToRimDecomposition :
    lengthInMeters setup.axleOffsetFromCenter +
        lengthInMeters setup.cableOffsetFromAxle =
      lengthInMeters setup.diskRadius

/-!
Scalar planar laws about the fixed axle, with counterclockwise torque positive.

The solid-disk law gives `I_center = (1/2) M R²`.  The parallel-axis law gives
`I_axle = I_center + M d²`.  Because the cable force is upward to the right of
the axle and the weight is downward to its left, both moment-arm products are
positive.  The axle reaction acts at the axle and therefore has zero moment.
After summing these release torques, Newton's rotational law is
`τ_net = I_axle α`.

These are generic governing relations.  They contain neither the numerical
answer nor any answer-choice label.
-/
structure SatisfiesPlanarRotationalDynamics
    (setup : DiskMachineSetup) : Prop where
  solidDiskCenterMomentOfInertia :
    momentOfInertiaInKilogramSquareMeters
        setup.momentOfInertiaAboutCenter =
      (1 / 2 : ℝ) * massInKilograms setup.diskMass *
        (lengthInMeters setup.diskRadius) ^ 2
  parallelAxisMomentOfInertia :
    momentOfInertiaInKilogramSquareMeters
        setup.momentOfInertiaAboutAxle =
      momentOfInertiaInKilogramSquareMeters
          setup.momentOfInertiaAboutCenter +
        massInKilograms setup.diskMass *
          (lengthInMeters setup.axleOffsetFromCenter) ^ 2
  cableMomentArmTorque :
    signedTorqueInNewtonMeters
        (setup.releaseTorqueAboutAxle .cableTension) =
      lengthInMeters setup.cableOffsetFromAxle *
        forceInNewtons setup.cableTensionMagnitude
  gravitationalMomentArmTorque :
    signedTorqueInNewtonMeters
        (setup.releaseTorqueAboutAxle .diskWeight) =
      lengthInMeters setup.axleOffsetFromCenter *
        massInKilograms setup.diskMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration
  axleReactionHasZeroMoment :
    signedTorqueInNewtonMeters
        (setup.releaseTorqueAboutAxle .axleReaction) = 0
  releaseTorqueSum :
    signedTorqueInNewtonMeters setup.netReleaseTorqueAboutAxle =
      signedTorqueInNewtonMeters
          (setup.releaseTorqueAboutAxle .cableTension) +
        signedTorqueInNewtonMeters
          (setup.releaseTorqueAboutAxle .diskWeight) +
        signedTorqueInNewtonMeters
          (setup.releaseTorqueAboutAxle .axleReaction)
  rotationalNewtonsSecondLaw :
    signedTorqueInNewtonMeters setup.netReleaseTorqueAboutAxle =
      momentOfInertiaInKilogramSquareMeters
          setup.momentOfInertiaAboutAxle *
        angularAccelerationInRadiansPerSecondSquared
          setup.initialAngularAcceleration
  positiveAccelerationMeansCounterclockwise :
    0 < angularAccelerationInRadiansPerSecondSquared
        setup.initialAngularAcceleration →
      setup.initialRotationSense = .counterclockwise

/-! ## Displayed choices and derived values -/

/-- The four answer labels in source order. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed acceleration value for each answer, in `rad/s²`. -/
def displayedAngularAcceleration : AnswerChoice → ℝ
  | .A => 500
  | .B => 300
  | .C => 400
  | .D => 450

/-- A choice minimizes absolute error against a computed acceleration. -/
def IsNearestDisplayedChoice
    (computedAcceleration : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |computedAcceleration - displayedAngularAcceleration choice| ≤
      |computedAcceleration - displayedAngularAcceleration other|

/-- The disk radius forced by the diameter label and circular geometry. -/
lemma diskRadiusInMeters
    (setup : DiskMachineSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hGeometry : SatisfiesDiskGeometry setup) :
    lengthInMeters setup.diskRadius = 1 / 20 := by
  have lengthInMeters_eq_lengthInCentimeters_div_hundred
      (length : LengthQuantity) :
      lengthInMeters length = lengthInCentimeters length / 100 := by
    change
      ((length UnitChoices.SI).val : ℝ) =
        ((length
          {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) /
          100
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
          (dim (WithDim L𝓭 NNReal)) = 100 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  rw [hGeometry.radiusIsHalfDiameter,
    lengthInMeters_eq_lengthInCentimeters_div_hundred,
    hData.diskDiameterCentimeters]
  norm_num

/-- Parallel-axis moment of inertia about the eccentric axle. -/
lemma diskMomentOfInertiaAboutAxle
    (setup : DiskMachineSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hGeometry : SatisfiesDiskGeometry setup)
    (hDynamics : SatisfiesPlanarRotationalDynamics setup) :
    momentOfInertiaInKilogramSquareMeters
      setup.momentOfInertiaAboutAxle = 3 / 320 := by
  have lengthInMeters_eq_lengthInCentimeters_div_hundred
      (length : LengthQuantity) :
      lengthInMeters length = lengthInCentimeters length / 100 := by
    change
      ((length UnitChoices.SI).val : ℝ) =
        ((length
          {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) /
          100
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
          (dim (WithDim L𝓭 NNReal)) = 100 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have hRadius : lengthInMeters setup.diskRadius = 1 / 20 :=
    diskRadiusInMeters setup hData hGeometry
  have hAxleOffset :
      lengthInMeters setup.axleOffsetFromCenter = 1 / 40 := by
    rw [lengthInMeters_eq_lengthInCentimeters_div_hundred,
      hData.axleOffsetCentimeters]
    norm_num
  have hCenter := hDynamics.solidDiskCenterMomentOfInertia
  rw [hData.diskMassKilograms, hRadius] at hCenter
  norm_num at hCenter
  have hAxle := hDynamics.parallelAxisMomentOfInertia
  rw [hCenter, hData.diskMassKilograms, hAxleOffset] at hAxle
  norm_num at hAxle ⊢
  exact hAxle

/-- Total counterclockwise torque immediately after the pin is removed. -/
lemma netReleaseTorqueAboutAxle
    (setup : DiskMachineSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hDynamics : SatisfiesPlanarRotationalDynamics setup) :
    signedTorqueInNewtonMeters setup.netReleaseTorqueAboutAxle =
      149 / 40 := by
  have lengthInMeters_eq_lengthInCentimeters_div_hundred
      (length : LengthQuantity) :
      lengthInMeters length = lengthInCentimeters length / 100 := by
    change
      ((length UnitChoices.SI).val : ℝ) =
        ((length
          {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) /
          100
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
          (dim (WithDim L𝓭 NNReal)) = 100 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have hAxleOffset :
      lengthInMeters setup.axleOffsetFromCenter = 1 / 40 := by
    rw [lengthInMeters_eq_lengthInCentimeters_div_hundred,
      hData.axleOffsetCentimeters]
    norm_num
  have hCableOffset :
      lengthInMeters setup.cableOffsetFromAxle = 1 / 40 := by
    rw [lengthInMeters_eq_lengthInCentimeters_div_hundred,
      hData.cableOffsetCentimeters]
    norm_num
  have hCable := hDynamics.cableMomentArmTorque
  rw [hCableOffset, hData.cableTensionNewtons] at hCable
  norm_num at hCable
  have hWeight := hDynamics.gravitationalMomentArmTorque
  rw [hAxleOffset, hData.diskMassKilograms,
    hGravity.gravityMetersPerSecondSquared] at hWeight
  norm_num at hWeight
  have hSum := hDynamics.releaseTorqueSum
  rw [hCable, hWeight, hDynamics.axleReactionHasZeroMoment] at hSum
  norm_num at hSum ⊢
  exact hSum

/-!
With `g = 9.8 m/s²`, the unrounded acceleration is
`(149/40) / (3/320) = 1192/3 rad/s²`, approximately `397.3 rad/s²`.
Among the displayed values, `400 rad/s²` (choice C) is therefore nearest.
-/
theorem initialAngularAcceleration_matches_choice_C
    (setup : DiskMachineSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hPhysical : HasPhysicalDiskParameters setup)
    (hGeometry : SatisfiesDiskGeometry setup)
    (hDynamics : SatisfiesPlanarRotationalDynamics setup) :
    angularAccelerationInRadiansPerSecondSquared
          setup.initialAngularAcceleration = 1192 / 3 ∧
      setup.initialRotationSense = .counterclockwise ∧
      IsNearestDisplayedChoice
        (angularAccelerationInRadiansPerSecondSquared
          setup.initialAngularAcceleration)
        .C := by
  have hInertia :=
    diskMomentOfInertiaAboutAxle setup hData hGeometry hDynamics
  have hTorque :=
    netReleaseTorqueAboutAxle setup hData hGravity hDynamics
  have hAcceleration :
      angularAccelerationInRadiansPerSecondSquared
          setup.initialAngularAcceleration = 1192 / 3 := by
    have hLaw := hDynamics.rotationalNewtonsSecondLaw
    rw [hTorque, hInertia] at hLaw
    norm_num at hLaw ⊢
    linarith
  refine ⟨hAcceleration, ?_, ?_⟩
  · apply hDynamics.positiveAccelerationMeansCounterclockwise
    rw [hAcceleration]
    norm_num
  · rw [hAcceleration]
    simp only [IsNearestDisplayedChoice]
    intro other
    cases other <;> norm_num [displayedAngularAcceleration]

end PhyXMiniProblems.ProblemPhyXMini0705
