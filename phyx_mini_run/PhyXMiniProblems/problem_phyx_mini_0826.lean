import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0826

open Dimension

/-!
# Flywheel and clutch plate brought into frictional contact

An engine flywheel `A` and a clutch plate `B` rotate about one common axis.
Axial forces press the two bodies together without exerting torque about that
axis.  Friction transfers angular momentum internally until the bodies rotate
together at one final angular velocity.

The apparently opposite circular arrows in the supplied image are drawn on
opposite exposed faces of the coaxial bodies.  The prose states that the two
initial rotations have the same physical direction.  Consequently the model
uses signed axial angular velocities relative to one oriented common axis and
requires both initial readouts to be positive.

Moments of inertia, angular velocities, angular momenta, forces, and torques
are unit-independent Physlib quantities.  Real numbers occur only as coherent
SI readouts and as the scalar formulas printed among the answer choices.

Assumption/target split:

* governing laws: the two pressing forces are equal and opposite along the
  common axis, their axial torques vanish, the coupled axial moment of inertia
  is `I_A + I_B`, axial angular momentum is `I * omega` before and after
  contact, and total axial angular momentum is conserved;
* previous-part results: none;
* figure/data readouts: the `BEFORE` and `AFTER` labels, the `I_A`, `I_B`,
  `omega_A`, `omega_B`, `F`, `-F`, `I_A + I_B`, and `omega` labels, aligned
  axes, separate bodies before contact, contact afterward, the displayed
  screen-arrow senses, steady same-direction initial rotation, axial pressing,
  rubbing, and eventual common rotation;
* target conclusions: the inertia-weighted expression for the final common
  angular velocity and agreement with recorded answer choice B.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The dimension of an axial moment of inertia, `mass * length^2`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- The dimension of angular momentum, `mass * length^2 / time`. -/
def angularMomentumDimension : Dimension :=
  momentOfInertiaDimension * T𝓭⁻¹

/-- The dimension of force, `mass * length / time^2`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension of torque, `mass * length^2 / time^2`. -/
def torqueDimension : Dimension :=
  forceDimension * L𝓭

/-!
A signed angular velocity component along the oriented common axis.  Radians
are dimensionless, so this has inverse-time dimension.
-/
abbrev AxialAngularVelocity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A nonnegative scalar moment of inertia about the common axis. -/
abbrev AxialMomentOfInertia : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A signed angular-momentum component along the common axis. -/
abbrev AxialAngularMomentum : Type :=
  Dimensionful (WithDim angularMomentumDimension ℝ)

/-- A signed force component along the common axis. -/
abbrev AxialForce : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- A signed torque component about the common axis. -/
abbrev AxialTorque : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Radian-per-second readout of an axial angular velocity. -/
def angularVelocityInRadiansPerSecond
    (angularVelocity : AxialAngularVelocity) : ℝ :=
  signedSIReadout angularVelocity

/-- Kilogram-metre-squared readout of an axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (momentOfInertia : AxialMomentOfInertia) : ℝ :=
  nonnegativeSIReadout momentOfInertia

/-- Kilogram-metre-squared-per-second readout of axial angular momentum. -/
def angularMomentumInKilogramMetersSquaredPerSecond
    (angularMomentum : AxialAngularMomentum) : ℝ :=
  signedSIReadout angularMomentum

/-- Newton readout of a signed axial force. -/
def axialForceInNewtons (force : AxialForce) : ℝ :=
  signedSIReadout force

/-- Newton-metre readout of a signed axial torque. -/
def axialTorqueInNewtonMeters (torque : AxialTorque) : ℝ :=
  signedSIReadout torque

/-! ## Physical roles and primary-image vocabulary -/

/-- The two coaxial rotating bodies named in the problem. -/
inductive RotatingBody where
  | engineFlywheelA
  | clutchPlateB
  deriving DecidableEq, Fintype, Repr

/-- The two stages printed at the left of the supplied image. -/
inductive FigureStage where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- Rotation sense as it appears on the two-dimensional image. -/
inductive ScreenRotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- The two force symbols printed beside the bodies. -/
inductive PressingForceLabel where
  | forceF
  | oppositeForceNegF
  deriving DecidableEq, Repr

/-- Text and mathematical labels visible in image `826.png`. -/
inductive DiskClutchFigureLabel where
  | before
  | after
  | inertiaIA
  | inertiaIB
  | angularVelocityOmegaA
  | angularVelocityOmegaB
  | forceF
  | oppositeForceNegF
  | combinedInertiaIAPlusIB
  | finalAngularVelocityOmega
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from the primary image.  Screen rotation
sense is kept distinct from signed physical axial direction because the two
initial arrows are drawn on opposite exposed faces.
-/
structure DiskClutchFigure where
  labelIsShown : DiskClutchFigureLabel → Bool
  bodyIsShown : FigureStage → RotatingBody → Bool
  axesAreDrawnAligned : FigureStage → Bool
  beforeRotationArrowSense : RotatingBody → ScreenRotationSense
  afterRotationArrowSense : ScreenRotationSense
  pressingForceLabel : RotatingBody → PressingForceLabel
  forceArrowPointsTowardContact : FigureStage → RotatingBody → Bool
  bodiesAreDepictedInContact : FigureStage → Bool

/-!
Independent physical quantities for the initial bodies and coupled final
assembly.  In particular, `finalCommonAngularVelocity` is an unknown
observable; it is not defined from conservation or from an answer choice.
-/
structure DiskClutchSetup where
  figure : DiskClutchFigure
  axialMomentOfInertia : RotatingBody → AxialMomentOfInertia
  initialAngularVelocity : RotatingBody → AxialAngularVelocity
  finalCommonAngularVelocity : AxialAngularVelocity
  coupledAxialMomentOfInertia : AxialMomentOfInertia
  pressingForce : RotatingBody → AxialForce
  pressingForceTorqueAboutAxis : RotatingBody → AxialTorque
  netExternalTorqueAboutAxis : AxialTorque
  initialTotalAngularMomentum : AxialAngularMomentum
  finalTotalAngularMomentum : AxialAngularMomentum
  initialRotationIsSteady : RotatingBody → Bool
  bodiesShareCommonAxis : Bool
  pressingForcesActAlongAxis : Bool
  disksRubDuringContact : Bool
  contactFrictionIsInternalToTwoBodySystem : Bool
  bodiesRotateTogetherAfterContact : Bool

/-! ## Figure evidence, problem data, and physical admissibility -/

/-- Facts read directly from the supplied `BEFORE`/`AFTER` image. -/
structure MatchesPrimaryDiskClutchFigure
    (setup : DiskClutchSetup) : Prop where
  everyPrintedLabelShown :
    ∀ label, setup.figure.labelIsShown label = true
  bothBodiesShownAtEveryStage :
    ∀ stage body, setup.figure.bodyIsShown stage body = true
  commonAxisShownAtEveryStage :
    ∀ stage, setup.figure.axesAreDrawnAligned stage = true
  flywheelArrowAppearsCounterclockwiseBefore :
    setup.figure.beforeRotationArrowSense .engineFlywheelA =
      .counterclockwise
  clutchArrowAppearsClockwiseBefore :
    setup.figure.beforeRotationArrowSense .clutchPlateB = .clockwise
  coupledArrowAppearsCounterclockwiseAfter :
    setup.figure.afterRotationArrowSense = .counterclockwise
  flywheelForceHasLabelF :
    setup.figure.pressingForceLabel .engineFlywheelA = .forceF
  clutchForceHasLabelNegF :
    setup.figure.pressingForceLabel .clutchPlateB = .oppositeForceNegF
  everyForceArrowPointsInward :
    ∀ stage body,
      setup.figure.forceArrowPointsTowardContact stage body = true
  bodiesSeparateBefore :
    setup.figure.bodiesAreDepictedInContact .before = false
  bodiesInContactAfter :
    setup.figure.bodiesAreDepictedInContact .after = true

/-!
Qualitative data stated in the problem.  Positivity relative to the chosen
axis encodes that both initial rotations have the same physical direction.
The final angular velocity remains unconstrained here beyond being a common
observable after frictional coupling.
-/
structure MatchesDiskClutchProblemData
    (setup : DiskClutchSetup) : Prop where
  bothInitialRotationsSteady :
    ∀ body, setup.initialRotationIsSteady body = true
  flywheelInitialRotationPositive :
    0 < angularVelocityInRadiansPerSecond
      (setup.initialAngularVelocity .engineFlywheelA)
  clutchInitialRotationPositive :
    0 < angularVelocityInRadiansPerSecond
      (setup.initialAngularVelocity .clutchPlateB)
  bodiesAreCoaxial : setup.bodiesShareCommonAxis = true
  forcesAreAxial : setup.pressingForcesActAlongAxis = true
  disksRub : setup.disksRubDuringContact = true
  frictionInternalToSystem :
    setup.contactFrictionIsInternalToTwoBodySystem = true
  commonRotationReached : setup.bodiesRotateTogetherAfterContact = true

/-!
Nondegeneracy conditions for the displayed physical branch.  They ensure the
sum `I_A + I_B` is nonzero but state no solved final angular velocity.
-/
structure HasPhysicalDiskClutchParameters
    (setup : DiskClutchSetup) : Prop where
  everyInitialMomentOfInertiaPositive :
    ∀ body,
      0 < momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia body)
  coupledMomentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.coupledAxialMomentOfInertia
  flywheelPressingForcePointsTowardClutch :
    0 < axialForceInNewtons (setup.pressingForce .engineFlywheelA)
  clutchPressingForcePointsTowardFlywheel :
    axialForceInNewtons (setup.pressingForce .clutchPlateB) < 0

/-! ## Governing torque and angular-momentum laws -/

/-!
The axial pressing forces are equal and opposite, so each has zero moment
about the common axis and the net external torque about that axis vanishes.
Friction may torque each body, but it is internal to the two-body system.
Consequently total axial angular momentum is conserved while the two moments
of inertia add in the coupled assembly.

These are governing relations.  No field states the requested quotient for
`finalCommonAngularVelocity` or identifies an answer choice.
-/
structure SatisfiesTorqueFreeClutchAngularMomentumLaws
    (setup : DiskClutchSetup) : Prop where
  pressingForcesEqualAndOpposite :
    axialForceInNewtons (setup.pressingForce .clutchPlateB) =
      -axialForceInNewtons (setup.pressingForce .engineFlywheelA)
  eachPressingForceHasZeroAxialTorque :
    ∀ body,
      axialTorqueInNewtonMeters
        (setup.pressingForceTorqueAboutAxis body) = 0
  netExternalAxialTorqueVanishes :
    axialTorqueInNewtonMeters setup.netExternalTorqueAboutAxis = 0
  coupledMomentOfInertiaIsAdditive :
    momentOfInertiaInKilogramMetersSquared
        setup.coupledAxialMomentOfInertia =
      momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .engineFlywheelA) +
        momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .clutchPlateB)
  initialAngularMomentumLaw :
    angularMomentumInKilogramMetersSquaredPerSecond
        setup.initialTotalAngularMomentum =
      momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .engineFlywheelA) *
          angularVelocityInRadiansPerSecond
            (setup.initialAngularVelocity .engineFlywheelA) +
        momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .clutchPlateB) *
          angularVelocityInRadiansPerSecond
            (setup.initialAngularVelocity .clutchPlateB)
  finalAngularMomentumLaw :
    angularMomentumInKilogramMetersSquaredPerSecond
        setup.finalTotalAngularMomentum =
      momentOfInertiaInKilogramMetersSquared
          setup.coupledAxialMomentOfInertia *
        angularVelocityInRadiansPerSecond
          setup.finalCommonAngularVelocity
  totalAxialAngularMomentumConserved :
    angularMomentumInKilogramMetersSquaredPerSecond
        setup.initialTotalAngularMomentum =
      angularMomentumInKilogramMetersSquaredPerSecond
        setup.finalTotalAngularMomentum

/-! ## Printed answer choices and target conclusion -/

/-- Labels of the four expressions printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The scalar angular-velocity expression printed beside each answer label.
These definitions encode the supplied options; they do not define the
independently stored final physical angular velocity.
-/
def AnswerChoice.proposedAngularVelocityInRadiansPerSecond
    (choice : AnswerChoice) (setup : DiskClutchSetup) : ℝ :=
  let inertiaA :=
    momentOfInertiaInKilogramMetersSquared
      (setup.axialMomentOfInertia .engineFlywheelA)
  let inertiaB :=
    momentOfInertiaInKilogramMetersSquared
      (setup.axialMomentOfInertia .clutchPlateB)
  let omegaA :=
    angularVelocityInRadiansPerSecond
      (setup.initialAngularVelocity .engineFlywheelA)
  let omegaB :=
    angularVelocityInRadiansPerSecond
      (setup.initialAngularVelocity .clutchPlateB)
  match choice with
  | .A => (inertiaA * omegaA + inertiaB * omegaB) / (inertiaA - inertiaB)
  | .B => (inertiaA * omegaA + inertiaB * omegaB) / (inertiaA + inertiaB)
  | .C => (inertiaA * omegaB + inertiaB * omegaA) / (inertiaA + inertiaB)
  | .D => (inertiaA * omegaB + inertiaB * omegaA) / (inertiaA - inertiaB)

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- An unknown final readout agrees with the expression printed at a choice. -/
def MatchesAnswerChoice
    (setup : DiskClutchSetup) (choice : AnswerChoice) : Prop :=
  angularVelocityInRadiansPerSecond setup.finalCommonAngularVelocity =
    choice.proposedAngularVelocityInRadiansPerSecond setup

/-!
Torque-free conservation of axial angular momentum gives the common final
angular velocity as the inertia-weighted mean of the two initial angular
velocities.  This is exactly recorded answer choice B.

This formalizes `thm:physics:phyx_mini_0826:target`.
-/
theorem finalCommonAngularVelocity_formula_and_choice_B
    (setup : DiskClutchSetup)
    (hFigure : MatchesPrimaryDiskClutchFigure setup)
    (hData : MatchesDiskClutchProblemData setup)
    (hPhysical : HasPhysicalDiskClutchParameters setup)
    (hLaws : SatisfiesTorqueFreeClutchAngularMomentumLaws setup) :
    angularVelocityInRadiansPerSecond
        setup.finalCommonAngularVelocity =
      (momentOfInertiaInKilogramMetersSquared
              (setup.axialMomentOfInertia .engineFlywheelA) *
            angularVelocityInRadiansPerSecond
              (setup.initialAngularVelocity .engineFlywheelA) +
          momentOfInertiaInKilogramMetersSquared
              (setup.axialMomentOfInertia .clutchPlateB) *
            angularVelocityInRadiansPerSecond
              (setup.initialAngularVelocity .clutchPlateB)) /
        (momentOfInertiaInKilogramMetersSquared
              (setup.axialMomentOfInertia .engineFlywheelA) +
          momentOfInertiaInKilogramMetersSquared
            (setup.axialMomentOfInertia .clutchPlateB)) ∧
      MatchesAnswerChoice setup recordedDatasetAnswer := by
  have hInertiaA : 0 < momentOfInertiaInKilogramMetersSquared
      (setup.axialMomentOfInertia .engineFlywheelA) :=
    hPhysical.everyInitialMomentOfInertiaPositive .engineFlywheelA
  have hInertiaB : 0 < momentOfInertiaInKilogramMetersSquared
      (setup.axialMomentOfInertia .clutchPlateB) :=
    hPhysical.everyInitialMomentOfInertiaPositive .clutchPlateB
  have hDenominator : 0 <
      momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .engineFlywheelA) +
        momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .clutchPlateB) :=
    add_pos hInertiaA hInertiaB
  have hFormula :
      angularVelocityInRadiansPerSecond setup.finalCommonAngularVelocity =
        (momentOfInertiaInKilogramMetersSquared
                (setup.axialMomentOfInertia .engineFlywheelA) *
              angularVelocityInRadiansPerSecond
                (setup.initialAngularVelocity .engineFlywheelA) +
            momentOfInertiaInKilogramMetersSquared
                (setup.axialMomentOfInertia .clutchPlateB) *
              angularVelocityInRadiansPerSecond
                (setup.initialAngularVelocity .clutchPlateB)) /
          (momentOfInertiaInKilogramMetersSquared
                (setup.axialMomentOfInertia .engineFlywheelA) +
            momentOfInertiaInKilogramMetersSquared
              (setup.axialMomentOfInertia .clutchPlateB)) := by
    apply (eq_div_iff (ne_of_gt hDenominator)).2
    rw [← hLaws.coupledMomentOfInertiaIsAdditive]
    nlinarith [hLaws.initialAngularMomentumLaw,
      hLaws.finalAngularMomentumLaw,
      hLaws.totalAxialAngularMomentumConserved]
  constructor
  · exact hFormula
  · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      AnswerChoice.proposedAngularVelocityInRadiansPerSecond] using hFormula

end PhyXMiniProblems.ProblemPhyXMini0826
