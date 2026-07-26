import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0813

open Dimension Time

/-!
# Velocity of a glider returning toward spring equilibrium

A `0.200 kg` glider is attached to a horizontal spring of stiffness
`5.00 N/m` on a frictionless air track.  The glider is released from rest at
`x₁ = 0.100 m`, where `x = 0` is the relaxed-spring equilibrium, and moves
back toward equilibrium.  The question asks for its signed x-velocity when
`x = 0.080 m`.

Physical mass, signed position, signed velocity, and spring stiffness are
represented by unit-independent Physlib quantities.  The governing law uses
Physlib's one-dimensional `ClassicalMechanics.HarmonicOscillator.energy` after
explicitly connecting its SI trajectory to those quantities.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the numerical source data, the
  release condition, motion toward equilibrium, and the labels and geometry
  visible in `813.png`;
* `HasPhysicalParameters` records positivity of the physical mass and spring
  stiffness;
* `SatisfiesFrictionlessHarmonicMotion` connects the physical quantities to a
  Physlib harmonic oscillator and states conservation of its mechanical
  energy between release and the queried state;
* there are no previous-part results; and
* the exact queried velocity `-0.30 m/s` and answer choice B occur only in
  conclusions.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed position along the horizontal x-axis. -/
abbrev SignedPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed horizontal velocity, with physical dimension `L T⁻¹`. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative spring stiffness, with dimension `M T⁻²` (`N/m`). -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a signed x-position in a selected length unit. -/
def positionReadout
    (unit : LengthUnit) (position : SignedPositionQuantity) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a signed x-velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read spring stiffness in coherent selected mass and time units. -/
def springStiffnessReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout of the glider mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout of a signed x-position. -/
def positionInMeters (position : SignedPositionQuantity) : ℝ :=
  positionReadout LengthUnit.meters position

/-- Metres-per-second readout, positive in the figure's positive x-direction. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Newton-per-metre readout of the spring stiffness. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  springStiffnessReadout MassUnit.kilograms TimeUnit.seconds stiffness

/-! ## Process states and primary-figure vocabulary -/

/-- The release state and the later state asked about in the problem. -/
inductive ProcessInstant where
  | release
  | queriedPosition
  deriving DecidableEq, Fintype, Repr

/-- Features visibly drawn in the supplied image. -/
inductive FigureFeature where
  | pointOne
  | coilSpring
  | equilibriumMarker
  | glider
  | horizontalXAxis
  deriving DecidableEq, Fintype, Repr

/-- Text and mathematical labels printed in the supplied image. -/
inductive FigureLabel where
  | pointOne
  | springConstantFive
  | springRelaxed
  | equilibriumXZero
  | initialPositionXOne
  | initialVelocityVOneX
  | gliderMassPointTwo
  deriving DecidableEq, Fintype, Repr

/-- Physical meanings of the labels in image `813.png`. -/
inductive FigureLabelRole where
  | fixedLeftSpringEndpoint
  | springStiffness
  | relaxedSpringEndpoint
  | equilibriumPosition
  | releasePosition
  | releaseVelocity
  | gliderMass
  deriving DecidableEq, Repr

/-- Horizontal orientations used for the track and x-axis. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The idealized support condition stated in the prose. -/
inductive TrackCondition where
  | frictionlessHorizontalAirTrack
  | resistiveTrack
  deriving DecidableEq, Repr

/-- Qualitative transcription of the primary image. -/
structure GliderSpringFigure where
  featureShown : FigureFeature → Bool
  labelShown : FigureLabel → Bool
  labelRole : FigureLabel → FigureLabelRole
  positiveXAxisDirection : HorizontalDirection
  pointOneMarksLeftSpringEnd : Bool
  equilibriumLiesBetweenPointOneAndGlider : Bool
  gliderIsRightOfEquilibrium : Bool
  relaxedSpringEndpointMarkedAtEquilibrium : Bool

/-!
Independent physical quantities and the associated one-dimensional Physlib
trajectory.  The velocity at the queried position is an unconstrained
physical quantity here; it is not defined from an answer choice.
-/
structure GliderSpringSetup where
  gliderMass : MassQuantity
  springStiffness : SpringStiffnessQuantity
  equilibriumPosition : SignedPositionQuantity
  positionAt : ProcessInstant → SignedPositionQuantity
  xVelocityAt : ProcessInstant → SignedVelocityQuantity
  timeAt : ProcessInstant → Time
  trajectorySI : Time → EuclideanSpace ℝ (Fin 1)
  oscillatorSI : ClassicalMechanics.HarmonicOscillator
  trackCondition : TrackCondition
  gliderAttachedToSpring : Bool
  figure : GliderSpringFigure

/-! ## Source data, primary-image evidence, and governing laws -/

/-!
Numerical and qualitative data stated by the source and shown in image
`813.png`.  The strict negative velocity records only the stated direction
"back toward equilibrium" from the positive-x side; it does not prescribe
the requested speed.
-/
structure MatchesProblemAndPrimaryFigure (setup : GliderSpringSetup) : Prop where
  massKilograms : massInKilograms setup.gliderMass = 1 / 5
  springStiffnessNewtonsPerMeter :
    springStiffnessInNewtonsPerMeter setup.springStiffness = 5
  equilibriumAtZero : positionInMeters setup.equilibriumPosition = 0
  releasePositionMeters :
    positionInMeters (setup.positionAt .release) = 1 / 10
  releasedFromRest :
    velocityInMetersPerSecond (setup.xVelocityAt .release) = 0
  queriedPositionMeters :
    positionInMeters (setup.positionAt .queriedPosition) = 2 / 25
  movingTowardEquilibriumAtQuery :
    velocityInMetersPerSecond (setup.xVelocityAt .queriedPosition) < 0
  frictionlessHorizontalTrack :
    setup.trackCondition = .frictionlessHorizontalAirTrack
  gliderIsAttachedToSpring : setup.gliderAttachedToSpring = true
  everyFeatureIsShown : ∀ feature, setup.figure.featureShown feature = true
  everyLabelIsShown : ∀ label, setup.figure.labelShown label = true
  pointOneLabelRole :
    setup.figure.labelRole .pointOne = .fixedLeftSpringEndpoint
  springConstantLabelRole :
    setup.figure.labelRole .springConstantFive = .springStiffness
  springRelaxedLabelRole :
    setup.figure.labelRole .springRelaxed = .relaxedSpringEndpoint
  equilibriumLabelRole :
    setup.figure.labelRole .equilibriumXZero = .equilibriumPosition
  initialPositionLabelRole :
    setup.figure.labelRole .initialPositionXOne = .releasePosition
  initialVelocityLabelRole :
    setup.figure.labelRole .initialVelocityVOneX = .releaseVelocity
  massLabelRole :
    setup.figure.labelRole .gliderMassPointTwo = .gliderMass
  xAxisPointsRight : setup.figure.positiveXAxisDirection = .right
  pointOneAtLeftSpringEnd : setup.figure.pointOneMarksLeftSpringEnd = true
  equilibriumBetweenPointOneAndGlider :
    setup.figure.equilibriumLiesBetweenPointOneAndGlider = true
  gliderRightOfEquilibrium : setup.figure.gliderIsRightOfEquilibrium = true
  relaxedEndpointAtEquilibrium :
    setup.figure.relaxedSpringEndpointMarkedAtEquilibrium = true

/-- Positivity conditions selecting a physical oscillator. -/
structure HasPhysicalParameters (setup : GliderSpringSetup) : Prop where
  massPositive : 0 < massInKilograms setup.gliderMass
  springStiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness

/-!
The physical readouts realize a one-dimensional Physlib harmonic oscillator.
Its coordinate is displacement from the relaxed-spring equilibrium, its time
derivative is the signed x-velocity, and its total mechanical energy is equal
at release and at the queried position because the horizontal track is
frictionless.

The energy equality is a governing conservation law.  It does not contain a
numerical value for the queried velocity.
-/
structure SatisfiesFrictionlessHarmonicMotion
    (setup : GliderSpringSetup) : Prop where
  oscillatorMassIsGliderMass :
    setup.oscillatorSI.m = massInKilograms setup.gliderMass
  oscillatorStiffnessIsSpringStiffness :
    setup.oscillatorSI.k =
      springStiffnessInNewtonsPerMeter setup.springStiffness
  trajectoryCoordinate : ∀ instant,
    setup.trajectorySI (setup.timeAt instant) 0 =
      positionInMeters (setup.positionAt instant) -
        positionInMeters setup.equilibriumPosition
  trajectoryVelocity : ∀ instant,
    (∂ₜ setup.trajectorySI (setup.timeAt instant)) 0 =
      velocityInMetersPerSecond (setup.xVelocityAt instant)
  mechanicalEnergyConservation :
    setup.oscillatorSI.energy setup.trajectorySI (setup.timeAt .release) =
      setup.oscillatorSI.energy setup.trajectorySI
        (setup.timeAt .queriedPosition)

/-! ## Derived velocity and displayed answer -/

/-!
Conservation of `1/2 m v² + 1/2 k x²` gives the squared queried speed
`(0.30 m/s)² = 9/100 (m/s)²`.  This magnitude is derived rather than assumed.
-/
lemma queriedVelocitySquared_eq_nineHundredths
    (setup : GliderSpringSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hMotion : SatisfiesFrictionlessHarmonicMotion setup) :
    velocityInMetersPerSecond (setup.xVelocityAt .queriedPosition) ^ 2 =
      9 / 100 := by
  have hEnergy := hMotion.mechanicalEnergyConservation
  simp [ClassicalMechanics.HarmonicOscillator.energy,
    ClassicalMechanics.HarmonicOscillator.kineticEnergy,
    ClassicalMechanics.HarmonicOscillator.potentialEnergy,
    hMotion.oscillatorMassIsGliderMass,
    hMotion.oscillatorStiffnessIsSpringStiffness,
    hData.massKilograms, hData.springStiffnessNewtonsPerMeter] at hEnergy
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one] at hEnergy
  rw [hMotion.trajectoryCoordinate, hMotion.trajectoryCoordinate,
    hMotion.trajectoryVelocity, hMotion.trajectoryVelocity] at hEnergy
  rw [hData.equilibriumAtZero, hData.releasePositionMeters,
    hData.queriedPositionMeters, hData.releasedFromRest] at hEnergy
  norm_num at hEnergy ⊢
  nlinarith

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed x-velocity in metres per second printed beside each choice. -/
def AnswerChoice.velocityInMetersPerSecond : AnswerChoice → ℝ
  | .A => -(7 / 10)
  | .B => -(3 / 10)
  | .C => -(6 / 5)
  | .D => -(23 / 10)

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswerChoice : AnswerChoice := .B

/-- A displayed choice reports the glider's queried signed x-velocity. -/
def AnswerChoiceReportsQueriedVelocity
    (setup : GliderSpringSetup) (choice : AnswerChoice) : Prop :=
  velocityInMetersPerSecond (setup.xVelocityAt .queriedPosition) =
    choice.velocityInMetersPerSecond

/-!
The energy law gives speed `0.30 m/s`; since the glider is on the positive-x
side and moving back toward equilibrium, its signed x-velocity is
`-0.30 m/s`, answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0813:target`.
-/
theorem problem_phyx_mini_0813
    (setup : GliderSpringSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hMotion : SatisfiesFrictionlessHarmonicMotion setup) :
    velocityInMetersPerSecond (setup.xVelocityAt .queriedPosition) =
        -(3 / 10) ∧
      AnswerChoiceReportsQueriedVelocity setup recordedDatasetAnswerChoice := by
  have hSq := queriedVelocitySquared_eq_nineHundredths setup hData hMotion
  have hNeg := hData.movingTowardEquilibriumAtQuery
  have hVelocity : velocityInMetersPerSecond
      (setup.xVelocityAt .queriedPosition) = -(3 / 10) := by
    norm_num at hSq hNeg ⊢
    nlinarith
  constructor
  · exact hVelocity
  · simpa [AnswerChoiceReportsQueriedVelocity,
      recordedDatasetAnswerChoice, AnswerChoice.velocityInMetersPerSecond]
      using hVelocity

end PhyXMiniProblems.ProblemPhyXMini0813
