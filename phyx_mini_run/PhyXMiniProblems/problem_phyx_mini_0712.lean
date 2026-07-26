import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0712

open Dimension

/-!
# A circular loop dropped onto a rotating solid disk

A `2.0 kg`, `20 cm` diameter solid disk initially rotates at `200 rpm`.
A nonrotating `1.0 kg`, `20 cm` diameter thin circular loop is dropped
straight down onto it.  Friction transfers angular momentum between the two
bodies until they rotate together about their common vertical symmetry axis.

Mass, length, axial angular velocity, moment of inertia, and angular momentum
are represented by unit-independent Physlib quantities.  Real numbers occur
only as coherent-SI readouts, revolutions-per-minute readouts, schematic image
coordinates, and displayed answer values.

Assumption/target split:

* governing laws: the solid-disk and thin-loop axial moments of inertia,
  `L = I * omega` for the before and after stages, and conservation of axial
  angular momentum when the frictional interaction has negligible external
  torque;
* previous-part results: none;
* figure/data readouts: equal `20 cm` diameters, masses `2.0 kg` and `1.0 kg`,
  disk initial angular velocity `200 rpm`, an initially nonrotating loop, a
  shared vertical axis, upward `L_i` and `L_f` arrows, and frictional coupling;
* target conclusions: the solved final angular velocity and its agreement
  with displayed answer choice C, `100 rpm`.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The physical dimension of axial moment of inertia, `mass * length^2`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- The physical dimension of angular momentum, `mass * length^2 / time`. -/
def angularMomentumDimension : Dimension :=
  momentOfInertiaDimension * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-!
A signed axial angular velocity.  Its sign records orientation relative to
the upward symmetry axis shown in the figure; radians are dimensionless, so
the physical dimension is inverse time.
-/
abbrev AxialAngularVelocity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A nonnegative axial moment of inertia. -/
abbrev AxialMomentOfInertia : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A signed component of angular momentum along the common symmetry axis. -/
abbrev AxialAngularMomentum : Type :=
  Dimensionful (WithDim angularMomentumDimension ℝ)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Radian-per-second readout of a signed axial angular velocity. -/
def angularVelocityInRadiansPerSecond
    (angularVelocity : AxialAngularVelocity) : ℝ :=
  signedSIReadout angularVelocity

/-!
Revolutions-per-minute readout of a signed axial angular velocity.  Since one
revolution is `2 * pi` radians and one minute is `60` seconds, the conversion
factor from radians per second is `30 / pi`.
-/
def angularVelocityInRevolutionsPerMinute
    (angularVelocity : AxialAngularVelocity) : ℝ :=
  angularVelocityInRadiansPerSecond angularVelocity * 30 / Real.pi

/-- Kilogram-metre-squared readout of an axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (momentOfInertia : AxialMomentOfInertia) : ℝ :=
  nonnegativeSIReadout momentOfInertia

/-- Kilogram-metre-squared-per-second readout of axial angular momentum. -/
def angularMomentumInKilogramMetersSquaredPerSecond
    (angularMomentum : AxialAngularMomentum) : ℝ :=
  signedSIReadout angularMomentum

/-! ## Physical roles and primary-image vocabulary -/

/-- The two rigid bodies named in the problem. -/
inductive RotatingBody where
  | disk
  | loop
  deriving DecidableEq, Fintype, Repr

/-- The body shapes needed by the standard axial inertia formulas. -/
inductive RotatingBodyShape where
  | solidDisk
  | thinCircularLoop
  deriving DecidableEq, Repr

/-- The two stages explicitly labelled in the supplied image. -/
inductive FigureStage where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- Orientation of an arrow along the common vertical symmetry axis. -/
inductive AxialDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Text and symbol labels printed in the primary image. -/
inductive DiskLoopFigureLabel where
  | before
  | after
  | diameterTwentyCentimeters
  | loopMassOneKilogram
  | diskMassTwoKilograms
  | initialAngularVelocityTwoHundredRpm
  | initialAngularMomentumLi
  | finalAngularVelocityOmegaF
  | finalAngularMomentumLf
  | symmetryAxis
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and schematic evidence transcribed from image `712.png`.
Coordinates are drawing coordinates and are deliberately kept separate from
the physical lengths.  The image's `omega_i = 200 rpm` label is attached to
the before stage; the prose identifies the disk as the initially rotating
body.
-/
structure DiskLoopFigure where
  bodyIsShown : FigureStage → RotatingBody → Bool
  verticalDrawingCoordinate : FigureStage → RotatingBody → ℝ
  labelIsShown : DiskLoopFigureLabel → Bool
  showsCommonVerticalSymmetryAxis : FigureStage → Bool
  showsRotationArrow : FigureStage → Bool
  showsAngularMomentumArrow : FigureStage → Bool
  angularMomentumArrowDirection : FigureStage → AxialDirection
  showsTwoDownwardDropArrowsBesideLoop : Bool
  depictsLoopRidingOnDiskAfter : Bool

/-!
Independent physical quantities for the initial bodies and the coupled final
system.  The final angular velocity is stored as an unknown observable; it is
not defined from angular-momentum conservation or from an answer choice.
-/
structure DiskLoopRotationSetup where
  figure : DiskLoopFigure
  bodyShape : RotatingBody → RotatingBodyShape
  diameter : RotatingBody → LengthQuantity
  radius : RotatingBody → LengthQuantity
  mass : RotatingBody → MassQuantity
  initialAngularVelocity : RotatingBody → AxialAngularVelocity
  finalCommonAngularVelocity : AxialAngularVelocity
  axialMomentOfInertia : RotatingBody → AxialMomentOfInertia
  initialTotalAngularMomentum : AxialAngularMomentum
  finalTotalAngularMomentum : AxialAngularMomentum
  loopIsDroppedStraightDown : Bool
  contactFrictionActsBetweenBodies : Bool
  bodiesRotateTogetherAfterContact : Bool
  externalTorqueAboutSymmetryAxisIsNegligible : Bool

/-! ## Figure evidence, problem data, and admissibility -/

/-!
Facts visible in the primary image.  The before-stage loop is above the disk,
both bodies share the drawn axis, the loop moves downward, and the after-stage
picture shows it riding on the disk.  Both angular-momentum arrows point
upward.  No metric value is inferred from a drawing coordinate.
-/
structure MatchesPrimaryDiskLoopFigure
    (setup : DiskLoopRotationSetup) : Prop where
  everyBodyShownAtEveryStage :
    ∀ stage body, setup.figure.bodyIsShown stage body = true
  loopAboveDiskBefore :
    setup.figure.verticalDrawingCoordinate .before .disk <
      setup.figure.verticalDrawingCoordinate .before .loop
  everyPrintedLabelShown :
    ∀ label, setup.figure.labelIsShown label = true
  sharedAxisShownAtEveryStage :
    ∀ stage, setup.figure.showsCommonVerticalSymmetryAxis stage = true
  rotationArrowShownAtEveryStage :
    ∀ stage, setup.figure.showsRotationArrow stage = true
  angularMomentumArrowShownAtEveryStage :
    ∀ stage, setup.figure.showsAngularMomentumArrow stage = true
  initialAngularMomentumPointsUpward :
    setup.figure.angularMomentumArrowDirection .before = .upward
  finalAngularMomentumPointsUpward :
    setup.figure.angularMomentumArrowDirection .after = .upward
  downwardDropArrowsShown :
    setup.figure.showsTwoDownwardDropArrowsBesideLoop = true
  loopRidingOnDiskAfter :
    setup.figure.depictsLoopRidingOnDiskAfter = true

/-!
Numerical and qualitative data supplied by the problem statement.  The disk,
not the dropped loop, has the stated initial `200 rpm` rotation.  "Dropped
straight down" is modeled as no initial spin of the loop about the vertical
axis.  Friction then brings both bodies to one common final angular velocity.
-/
structure MatchesDiskLoopProblemData
    (setup : DiskLoopRotationSetup) : Prop where
  diskShape : setup.bodyShape .disk = .solidDisk
  loopShape : setup.bodyShape .loop = .thinCircularLoop
  diskDiameterMeters : lengthInMeters (setup.diameter .disk) = 1 / 5
  loopDiameterMeters : lengthInMeters (setup.diameter .loop) = 1 / 5
  diskRadiusIsHalfDiameter :
    lengthInMeters (setup.radius .disk) =
      lengthInMeters (setup.diameter .disk) / 2
  loopRadiusIsHalfDiameter :
    lengthInMeters (setup.radius .loop) =
      lengthInMeters (setup.diameter .loop) / 2
  diskMassKilograms : massInKilograms (setup.mass .disk) = 2
  loopMassKilograms : massInKilograms (setup.mass .loop) = 1
  diskInitialAngularVelocityRpm :
    angularVelocityInRevolutionsPerMinute
        (setup.initialAngularVelocity .disk) = 200
  loopInitiallyNotRotating :
    angularVelocityInRadiansPerSecond
        (setup.initialAngularVelocity .loop) = 0
  loopDroppedStraightDown : setup.loopIsDroppedStraightDown = true
  frictionActsDuringContact : setup.contactFrictionActsBetweenBodies = true
  commonFinalRotation : setup.bodiesRotateTogetherAfterContact = true

/-!
Positivity and nondegeneracy conditions for the physical branch shown in the
image.  They contain no solved final angular velocity.
-/
structure HasPhysicalDiskLoopParameters
    (setup : DiskLoopRotationSetup) : Prop where
  everyDiameterPositive :
    ∀ body, 0 < lengthInMeters (setup.diameter body)
  everyRadiusPositive :
    ∀ body, 0 < lengthInMeters (setup.radius body)
  everyMassPositive :
    ∀ body, 0 < massInKilograms (setup.mass body)
  everyMomentOfInertiaPositive :
    ∀ body,
      0 < momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia body)
  diskInitiallyRotatesInPositiveDirection :
    0 < angularVelocityInRadiansPerSecond
      (setup.initialAngularVelocity .disk)
  initialAngularMomentumPointsUpward :
    0 < angularMomentumInKilogramMetersSquaredPerSecond
      setup.initialTotalAngularMomentum
  finalAngularMomentumPointsUpward :
    0 < angularMomentumInKilogramMetersSquaredPerSecond
      setup.finalTotalAngularMomentum

/-! ## Governing rigid-body laws -/

/-!
The standard moments about the central symmetry axis:

* a uniform solid disk has `I = (1 / 2) * M * R^2`;
* a thin circular loop has `I = M * R^2`.

These are shape laws, not solved values for the final angular velocity.
-/
structure SatisfiesDiskAndLoopMomentOfInertiaLaws
    (setup : DiskLoopRotationSetup) : Prop where
  solidDiskMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia .disk) =
      (1 / 2 : ℝ) * massInKilograms (setup.mass .disk) *
        lengthInMeters (setup.radius .disk) ^ 2
  thinLoopMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia .loop) =
      massInKilograms (setup.mass .loop) *
        lengthInMeters (setup.radius .loop) ^ 2

/-!
Axial angular momentum for the before and after stages and its conservation.
Friction is internal to the disk-loop system, and external torque about the
vertical axis is taken to be negligible.  Thus the initial total is the sum
of each body's `I * omega`, while after coupling both moments multiply the
same common angular velocity.  None of these fields contains `100 rpm` or an
answer label.
-/
structure SatisfiesIsolatedFrictionalAngularMomentumLaw
    (setup : DiskLoopRotationSetup) : Prop where
  frictionTransfersAngularMomentumInternally :
    setup.contactFrictionActsBetweenBodies = true
  negligibleExternalTorqueConfirmed :
    setup.externalTorqueAboutSymmetryAxisIsNegligible = true
  initialAngularMomentumLaw :
    angularMomentumInKilogramMetersSquaredPerSecond
        setup.initialTotalAngularMomentum =
      momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .disk) *
          angularVelocityInRadiansPerSecond
            (setup.initialAngularVelocity .disk) +
        momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .loop) *
          angularVelocityInRadiansPerSecond
            (setup.initialAngularVelocity .loop)
  finalAngularMomentumLaw :
    angularMomentumInKilogramMetersSquaredPerSecond
        setup.finalTotalAngularMomentum =
      (momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .disk) +
        momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .loop)) *
        angularVelocityInRadiansPerSecond
          setup.finalCommonAngularVelocity
  axialAngularMomentumConserved :
    angularMomentumInKilogramMetersSquaredPerSecond
        setup.initialTotalAngularMomentum =
      angularMomentumInKilogramMetersSquaredPerSecond
        setup.finalTotalAngularMomentum

/-! ## Derived angular velocity and displayed answers -/

/-!
For the equal radii and stated masses, the disk and loop have equal axial
moments of inertia: `(1 / 2) * 2 * R^2 = 1 * R^2`.
-/
lemma diskMomentOfInertia_equals_loopMomentOfInertia
    (setup : DiskLoopRotationSetup)
    (hData : MatchesDiskLoopProblemData setup)
    (hPhysical : HasPhysicalDiskLoopParameters setup)
    (hInertia : SatisfiesDiskAndLoopMomentOfInertiaLaws setup) :
    momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia .disk) =
      momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia .loop) := by
  norm_num [hInertia.solidDiskMomentOfInertia,
    hInertia.thinLoopMomentOfInertia, hData.diskMassKilograms,
    hData.loopMassKilograms, hData.diskRadiusIsHalfDiameter,
    hData.loopRadiusIsHalfDiameter, hData.diskDiameterMeters,
    hData.loopDiameterMeters]

/-!
Solving the conserved-angular-momentum relation gives the common final axial
angular velocity as total initial `I * omega` divided by the total inertia.
This is a derived formula, not a premise of the numerical theorem.
-/
lemma finalCommonAngularVelocity_formula
    (setup : DiskLoopRotationSetup)
    (hPhysical : HasPhysicalDiskLoopParameters setup)
    (hAngularMomentum :
      SatisfiesIsolatedFrictionalAngularMomentumLaw setup) :
    angularVelocityInRadiansPerSecond
        setup.finalCommonAngularVelocity =
      (momentOfInertiaInKilogramMetersSquared
            (setup.axialMomentOfInertia .disk) *
            angularVelocityInRadiansPerSecond
              (setup.initialAngularVelocity .disk) +
          momentOfInertiaInKilogramMetersSquared
            (setup.axialMomentOfInertia .loop) *
            angularVelocityInRadiansPerSecond
              (setup.initialAngularVelocity .loop)) /
        (momentOfInertiaInKilogramMetersSquared
            (setup.axialMomentOfInertia .disk) +
          momentOfInertiaInKilogramMetersSquared
            (setup.axialMomentOfInertia .loop)) := by
  have hDenPos :
      0 <
        momentOfInertiaInKilogramMetersSquared
            (setup.axialMomentOfInertia .disk) +
          momentOfInertiaInKilogramMetersSquared
            (setup.axialMomentOfInertia .loop) :=
    add_pos (hPhysical.everyMomentOfInertiaPositive .disk)
      (hPhysical.everyMomentOfInertiaPositive .loop)
  apply (eq_div_iff (ne_of_gt hDenPos)).2
  nlinarith [hAngularMomentum.initialAngularMomentumLaw,
    hAngularMomentum.finalAngularMomentumLaw,
    hAngularMomentum.axialAngularMomentumConserved]

/-- Labels of the four angular-velocity choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Revolutions-per-minute value printed beside each answer label. -/
def AnswerChoice.revolutionsPerMinute : AnswerChoice → ℝ
  | .A => 122
  | .B => 88
  | .C => 100
  | .D => 134

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
An independently stored final angular velocity matches an answer choice when
its revolutions-per-minute readout equals the printed value.
-/
def MatchesAnswerChoice
    (angularVelocity : AxialAngularVelocity) (choice : AnswerChoice) : Prop :=
  angularVelocityInRevolutionsPerMinute angularVelocity =
    choice.revolutionsPerMinute

/-!
Conservation of axial angular momentum, together with the two shape-inertia
laws, makes the final common angular velocity half the disk's initial value:
`100 rpm`.  It therefore agrees uniquely with recorded choice C.

This formalizes `thm:physics:phyx_mini_0712:target`.
-/
theorem finalAngularVelocity_is_100_rpm
    (setup : DiskLoopRotationSetup)
    (hFigure : MatchesPrimaryDiskLoopFigure setup)
    (hData : MatchesDiskLoopProblemData setup)
    (hPhysical : HasPhysicalDiskLoopParameters setup)
    (hInertia : SatisfiesDiskAndLoopMomentOfInertiaLaws setup)
    (hAngularMomentum :
      SatisfiesIsolatedFrictionalAngularMomentumLaw setup) :
    angularVelocityInRevolutionsPerMinute
        setup.finalCommonAngularVelocity = 100 ∧
      MatchesAnswerChoice
        setup.finalCommonAngularVelocity recordedDatasetAnswer ∧
      ∀ choice,
        MatchesAnswerChoice setup.finalCommonAngularVelocity choice →
          choice = recordedDatasetAnswer := by
  have hI :=
    diskMomentOfInertia_equals_loopMomentOfInertia
      setup hData hPhysical hInertia
  have hFormula :=
    finalCommonAngularVelocity_formula setup hPhysical hAngularMomentum
  rw [hI, hData.loopInitiallyNotRotating] at hFormula
  have hILoopPos :=
    hPhysical.everyMomentOfInertiaPositive .loop
  have hFinalHalf :
      angularVelocityInRadiansPerSecond
          setup.finalCommonAngularVelocity =
        angularVelocityInRadiansPerSecond
            (setup.initialAngularVelocity .disk) / 2 := by
    field_simp [ne_of_gt hILoopPos] at hFormula
    nlinarith
  have hFinalRpm :
      angularVelocityInRevolutionsPerMinute
          setup.finalCommonAngularVelocity = 100 := by
    have hDiskRpm := hData.diskInitialAngularVelocityRpm
    unfold angularVelocityInRevolutionsPerMinute at hDiskRpm ⊢
    rw [hFinalHalf]
    field_simp [Real.pi_ne_zero] at hDiskRpm ⊢
    linarith
  refine ⟨hFinalRpm, ?_, ?_⟩
  · exact hFinalRpm
  · intro choice hChoice
    unfold MatchesAnswerChoice at hChoice
    rw [hFinalRpm] at hChoice
    cases choice with
    | A => norm_num [AnswerChoice.revolutionsPerMinute] at hChoice
    | B => norm_num [AnswerChoice.revolutionsPerMinute] at hChoice
    | C => rfl
    | D => norm_num [AnswerChoice.revolutionsPerMinute] at hChoice

end PhyXMiniProblems.ProblemPhyXMini0712
