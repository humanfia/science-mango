import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/- The assigned source file did not exist when this autoformalization began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0718

open Dimension

/-!
# Velocity of a student on a vertical bungee spring

An `83 kg` student is released from rest when a bungee cord, modeled as an
ideal spring of stiffness `270 N/m`, is extended `5.0 m` from its unstretched
length.  The primary image places equilibrium between the unstretched and
release levels.  Its oscillation axis has upward-positive coordinate `y`,
equilibrium at `0`, and release at `-A`.

Dimensionful Physlib quantities represent mass, length, duration, stiffness,
acceleration, and signed vertical velocity.  Physlib's scalar harmonic
oscillator is connected explicitly to their coherent SI readouts.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The physical dimension of velocity, `L T⁻¹`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of linear spring stiffness, `M T⁻²`. -/
def springStiffnessDimension : Dimension := M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration elapsed since release. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical linear-spring stiffness. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim springStiffnessDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed vertical displacement from equilibrium. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A signed vertical velocity, positive in the displayed upward direction. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Kilogram readout of the student's physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Second readout of a physical elapsed duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  nonnegativeSIReadout duration

/-- Newton-per-metre readout of the cord's spring stiffness. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  nonnegativeSIReadout stiffness

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Metre readout of a signed upward-positive displacement. -/
def signedLengthInMeters (displacement : SignedLengthQuantity) : ℝ :=
  signedSIReadout displacement

/-- Metre-per-second readout of a signed upward-positive velocity. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  signedSIReadout velocity

/-! ## Primary-image labels and geometry -/

/-- Physical and graphical objects visibly present in the supplied image. -/
inductive FigureObject where
  | ceiling
  | bungeeCord
  | student
  | equilibriumDashedLine
  | releaseDashedLine
  | extensionArrow
  | verticalOscillationAxis
  | oscillationArrows
  deriving DecidableEq, Repr

/-- Text and mathematical labels printed in the supplied image. -/
inductive FigureTextLabel where
  | cordModeledAsSpring
  | springConstant270NewtonsPerMeter
  | extensionFiveMeters
  | equilibrium
  | release
  | studentMass83Kilograms
  | verticalCoordinateY
  | positiveAmplitudeA
  | equilibriumZero
  | negativeAmplitude
  | oscillation
  deriving DecidableEq, Repr

/-- Distinguished vertical levels in the supplied bungee drawing. -/
inductive FigureLevel where
  | ceiling
  | unstretchedCordEnd
  | equilibrium
  | release
  | positiveAmplitudeMarker
  | zeroMarker
  | negativeAmplitudeMarker
  deriving DecidableEq, Repr

/-!
The categorical incidences and scalar labels transcribed from the primary
image.  `verticalCoordinate` is only a schematic figure coordinate; it is not
a replacement for any dimensionful length in the physical setup.
-/
structure BungeeFigureReadout where
  objectShown : FigureObject → Prop
  textLabelShown : FigureTextLabel → Prop
  verticalCoordinate : FigureLevel → ℝ
  extensionArrowUpperEndpoint : FigureLevel
  extensionArrowLowerEndpoint : FigureLevel
  cordUpperAttachmentLevel : FigureLevel
  cordLowerEndLevel : FigureLevel
  studentLevel : FigureLevel
  springConstantLabelNewtonsPerMeter : ℝ
  extensionLabelMeters : ℝ
  studentMassLabelKilograms : ℝ

/-! ## Physical setup and model roles -/

/-- The sign and origin convention shown by the vertical `y` axis. -/
inductive VerticalCoordinateConvention where
  | upwardPositiveWithOriginAtEquilibrium
  | other
  deriving DecidableEq, Repr

/-- Idealization used for the bungee cord over the modeled interval. -/
inductive CordModel where
  | masslessLinearSpring
  | other
  deriving DecidableEq, Repr

/-- Motion regime assumed after the student is released. -/
inductive MotionRegime where
  | undampedVerticalSimpleHarmonic
  | other
  deriving DecidableEq, Repr

/-!
The physical quantities and response functions for the bungee experiment.

`unstretchedToReleaseExtension` is the full `5.0 m` cord extension visible in
the image.  It is deliberately distinct from `oscillationAmplitude`, which is
the release-to-equilibrium distance after the gravitational equilibrium shift.
The requested velocity is not stored as a special numerical field.
-/
structure BungeeOscillationSetup where
  studentMass : MassQuantity
  cordSpringStiffness : SpringStiffnessQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  unstretchedToReleaseExtension : LengthQuantity
  equilibriumExtension : LengthQuantity
  oscillationAmplitude : LengthQuantity
  observationDelay : TimeQuantity
  oscillator : ClassicalMechanics.HarmonicOscillator
  initialConditions :
    ClassicalMechanics.HarmonicOscillator.InitialConditions
  verticalDisplacementFromEquilibrium :
    TimeQuantity → SignedLengthQuantity
  verticalVelocity : TimeQuantity → SignedVelocityQuantity
  coordinateConvention : VerticalCoordinateConvention
  cordModel : CordModel
  motionRegime : MotionRegime
  figure : BungeeFigureReadout

/-!
Numerical values given in the prose, together with the standard near-Earth
gravity calibration used by the recorded multiple-choice calculation.  No
velocity value or answer-choice assertion occurs here.
-/
structure MatchesProblemData (setup : BungeeOscillationSetup) : Prop where
  studentMassIs83Kilograms :
    massInKilograms setup.studentMass = 83
  springStiffnessIs270NewtonsPerMeter :
    stiffnessInNewtonsPerMeter setup.cordSpringStiffness = 270
  releaseExtensionIsFiveMeters :
    lengthInMeters setup.unstretchedToReleaseExtension = 5
  observationDelayIsTwoSeconds :
    timeInSeconds setup.observationDelay = 2
  standardNearEarthGravity :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5

/-!
Transcription of the source image and coherence of its three numerical labels
with the corresponding dimensionful quantities.  The top endpoint of the
`5.0 m` arrow is the unstretched-cord level, not the equilibrium line.
-/
structure MatchesSourceFigure (setup : BungeeOscillationSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.objectShown object
  everyTextLabelShown : ∀ label, setup.figure.textLabelShown label
  extensionArrowStartsAtUnstretchedLevel :
    setup.figure.extensionArrowUpperEndpoint = .unstretchedCordEnd
  extensionArrowEndsAtReleaseLevel :
    setup.figure.extensionArrowLowerEndpoint = .release
  cordAttachedAtCeiling :
    setup.figure.cordUpperAttachmentLevel = .ceiling
  stretchedCordEndsAtRelease :
    setup.figure.cordLowerEndLevel = .release
  studentShownAtRelease : setup.figure.studentLevel = .release
  ceilingAboveUnstretchedEnd :
    setup.figure.verticalCoordinate .ceiling >
      setup.figure.verticalCoordinate .unstretchedCordEnd
  unstretchedEndAboveEquilibrium :
    setup.figure.verticalCoordinate .unstretchedCordEnd >
      setup.figure.verticalCoordinate .equilibrium
  equilibriumAboveRelease :
    setup.figure.verticalCoordinate .equilibrium >
      setup.figure.verticalCoordinate .release
  equilibriumAlignsWithZeroMarker :
    setup.figure.verticalCoordinate .equilibrium =
      setup.figure.verticalCoordinate .zeroMarker
  releaseAlignsWithNegativeAmplitudeMarker :
    setup.figure.verticalCoordinate .release =
      setup.figure.verticalCoordinate .negativeAmplitudeMarker
  positiveAmplitudeMarkerAboveZero :
    setup.figure.verticalCoordinate .positiveAmplitudeMarker >
      setup.figure.verticalCoordinate .zeroMarker
  figureSpringStiffnessIs270 :
    setup.figure.springConstantLabelNewtonsPerMeter = 270
  figureExtensionIsFiveMeters :
    setup.figure.extensionLabelMeters = 5
  figureStudentMassIs83Kilograms :
    setup.figure.studentMassLabelKilograms = 83
  figureSpringStiffnessMatchesSetup :
    stiffnessInNewtonsPerMeter setup.cordSpringStiffness =
      setup.figure.springConstantLabelNewtonsPerMeter
  figureExtensionMatchesSetup :
    lengthInMeters setup.unstretchedToReleaseExtension =
      setup.figure.extensionLabelMeters
  figureMassMatchesSetup :
    massInKilograms setup.studentMass =
      setup.figure.studentMassLabelKilograms

/-! ## Governing equilibrium and harmonic-motion laws -/

/-!
The ideal vertical spring model consists of:

* static force balance `k x_eq = m g`;
* amplitude equal to the excess of the release extension over the equilibrium
  extension;
* release from rest at the displayed point `y = -A`;
* Physlib's harmonic oscillator with SI-calibrated mass and stiffness;
* displacement and velocity given, for every elapsed duration, by Physlib's
  harmonic-oscillator trajectory and its time derivative.

These are generic physical/modeling relations.  They do not mention the
two-second numerical velocity or any displayed answer choice.
-/
structure SatisfiesIdealBungeePhysics
    (setup : BungeeOscillationSetup) : Prop where
  upwardPositiveCoordinate :
    setup.coordinateConvention =
      .upwardPositiveWithOriginAtEquilibrium
  cordIsLinearSpring : setup.cordModel = .masslessLinearSpring
  motionIsUndampedSHM :
    setup.motionRegime = .undampedVerticalSimpleHarmonic
  oscillatorUsesStudentMass :
    setup.oscillator.m = massInKilograms setup.studentMass
  oscillatorUsesCordStiffness :
    setup.oscillator.k =
      stiffnessInNewtonsPerMeter setup.cordSpringStiffness
  staticEquilibriumForceBalance :
    stiffnessInNewtonsPerMeter setup.cordSpringStiffness *
        lengthInMeters setup.equilibriumExtension =
      massInKilograms setup.studentMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  amplitudeIsReleaseOffsetFromEquilibrium :
    lengthInMeters setup.oscillationAmplitude =
      lengthInMeters setup.unstretchedToReleaseExtension -
        lengthInMeters setup.equilibriumExtension
  releasedAtNegativeAmplitude :
    setup.initialConditions.x₀ 0 =
      -lengthInMeters setup.oscillationAmplitude
  releasedFromRest : setup.initialConditions.v₀ 0 = 0
  displacementMatchesOscillatorTrajectory :
    ∀ duration,
      signedLengthInMeters
          (setup.verticalDisplacementFromEquilibrium duration) =
        (setup.initialConditions.trajectory setup.oscillator
            (timeInSeconds duration : Time)) 0
  velocityMatchesOscillatorTrajectory :
    ∀ duration,
      velocityInMetersPerSecond (setup.verticalVelocity duration) =
        (Time.deriv
            (setup.initialConditions.trajectory setup.oscillator)
            (timeInSeconds duration : Time)) 0

/-! ## Displayed answer choices and target -/

/-- Letter labels of the four velocities printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre-per-second value printed beside each displayed answer label. -/
def AnswerChoice.velocityMetersPerSecond : AnswerChoice → ℝ
  | .A => -2
  | .B => -9 / 5
  | .C => -8 / 5
  | .D => -7 / 5

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
For the stated mass, spring stiffness, release extension, gravity calibration,
and two-second delay, the upward-positive velocity is within `0.05 m/s` of
`-1.6 m/s`; option C is uniquely closest among the displayed choices.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0718:target`.
-/
theorem bungee_velocity_after_two_seconds_matches_answer_C
    (setup : BungeeOscillationSetup)
    (hData : MatchesProblemData setup)
    (hFigure : MatchesSourceFigure setup)
    (hPhysics : SatisfiesIdealBungeePhysics setup) :
    abs (velocityInMetersPerSecond
          (setup.verticalVelocity setup.observationDelay) -
        AnswerChoice.velocityMetersPerSecond .C) < 1 / 20 ∧
      ∀ choice, choice ≠ .C →
        abs (velocityInMetersPerSecond
              (setup.verticalVelocity setup.observationDelay) -
            AnswerChoice.velocityMetersPerSecond .C) <
        abs (velocityInMetersPerSecond
              (setup.verticalVelocity setup.observationDelay) -
            AnswerChoice.velocityMetersPerSecond choice) := by
    have hMassFromFigure :
        massInKilograms setup.studentMass = 83 :=
      hFigure.figureMassMatchesSetup.trans hFigure.figureStudentMassIs83Kilograms
    have hωsq : setup.oscillator.ω ^ 2 = 270 / 83 := by
      rw [ClassicalMechanics.HarmonicOscillator.ω_sq,
        hPhysics.oscillatorUsesCordStiffness,
        hPhysics.oscillatorUsesStudentMass,
        hData.springStiffnessIs270NewtonsPerMeter,
        hMassFromFigure]
    clear hFigure hMassFromFigure
    have hωpos : 0 < setup.oscillator.ω :=
      setup.oscillator.ω_pos
    have hωLower : (1803 : ℝ) / 1000 < setup.oscillator.ω := by
      nlinarith [hωsq]
    have hωUpper : setup.oscillator.ω < (1804 : ℝ) / 1000 := by
      nlinarith [hωsq]
    have hAmplitude :
        lengthInMeters setup.oscillationAmplitude = (2683 : ℝ) / 1350 := by
      have hBalance := hPhysics.staticEquilibriumForceBalance
      rw [hData.springStiffnessIs270NewtonsPerMeter,
        hData.studentMassIs83Kilograms,
        hData.standardNearEarthGravity] at hBalance
      rw [hPhysics.amplitudeIsReleaseOffsetFromEquilibrium,
        hData.releaseExtensionIsFiveMeters]
      norm_num at hBalance ⊢
      linarith
    have hInitialPosition :
        setup.initialConditions.x₀ 0 = -(2683 : ℝ) / 1350 := by
      rw [hPhysics.releasedAtNegativeAmplitude, hAmplitude]
      ring
    have hVelocity :
        velocityInMetersPerSecond
            (setup.verticalVelocity setup.observationDelay) =
          setup.oscillator.ω * ((2683 : ℝ) / 1350) *
            Real.sin (setup.oscillator.ω * 2) := by
      rw [hPhysics.velocityMatchesOscillatorTrajectory,
        ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_velocity,
        hData.observationDelayIsTwoSeconds]
      simp [hInitialPosition, hPhysics.releasedFromRest]
      ring
    clear hAmplitude hInitialPosition hωsq
    have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = 2 := by
      norm_num
    have hsqrtTwoUpper : Real.sqrt 2 < (70711 : ℝ) / 50000 := by
      nlinarith [Real.sqrt_nonneg 2]
    have hsqrtTwoLower : (141421 : ℝ) / 100000 < Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2]
    have hsqrtTwoPlusSq :
        (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrtTwoPlusUpper :
        Real.sqrt (2 + Real.sqrt 2) < (184777 : ℝ) / 100000 := by
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 2)]
    have hsqrtTwoPlusLower :
        (923879 : ℝ) / 500000 < Real.sqrt (2 + Real.sqrt 2) := by
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 2)]
    have hsqrtThreeLevelSq :
        (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
          2 + Real.sqrt (2 + Real.sqrt 2) := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrtThreeLevelUpper :
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
          (98079 : ℝ) / 50000 := by
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt (2 + Real.sqrt 2))]
    have hsqrtThreeLevelLower :
        (4903921 : ℝ) / 2500000 <
          Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt (2 + Real.sqrt 2))]
    have hFinalRadicand :
        0 ≤ 2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
      linarith
    have hsqrtFinalSq :
        (Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))) ^ 2 =
          2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
      rw [Real.sq_sqrt hFinalRadicand]
    have hsinePiOver32Lower :
        (98 : ℝ) / 1000 <
          Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) / 2 := by
      nlinarith [Real.sqrt_nonneg
        (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))]
    have hsinePiOver32Upper :
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) / 2 <
          (9802 : ℝ) / 100000 := by
      nlinarith [Real.sqrt_nonneg
        (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))]
    have hPiLower : (392 : ℝ) / 125 < Real.pi := by
      have hSinLe := Real.sin_le (show 0 ≤ Real.pi / 32 by positivity)
      rw [Real.sin_pi_div_thirty_two] at hSinLe
      nlinarith
    have hPiUpper : Real.pi < (1966 : ℝ) / 625 := by
      let x : ℝ := Real.pi / 32
      have hxPos : 0 < x := by
        dsimp [x]
        positivity
      have hxUpper : x ≤ 1 / 8 := by
        dsimp [x]
        nlinarith [Real.pi_le_four]
      have hSinCube := Real.sin_gt_sub_cube hxPos (by linarith : x ≤ 1)
      rw [show Real.sin x =
          Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) / 2 by
            dsimp [x]
            exact Real.sin_pi_div_thirty_two] at hSinCube
      by_contra h
      have hxLower : (983 : ℝ) / 10000 ≤ x := by
        dsimp [x] at h ⊢
        push Not at h
        linarith
      have hxSqUpper : x ^ 2 ≤ ((1 : ℝ) / 8) ^ 2 := by
        have hProduct :
            0 ≤ ((1 : ℝ) / 8 - x) * ((1 : ℝ) / 8 + x) :=
          mul_nonneg (sub_nonneg.mpr hxUpper) (by linarith)
        nlinarith only [hProduct]
      have hxMulUpper :
          x * ((983 : ℝ) / 10000) ≤
            ((1 : ℝ) / 8) * ((983 : ℝ) / 10000) :=
        mul_le_mul_of_nonneg_right hxUpper (by norm_num)
      have hFactorPos :
          0 < 1 -
            (x ^ 2 + x * ((983 : ℝ) / 10000) +
              ((983 : ℝ) / 10000) ^ 2) / 4 := by
        nlinarith only [hxSqUpper, hxMulUpper]
      have hPolynomialMono :
          (983 : ℝ) / 10000 - ((983 : ℝ) / 10000) ^ 3 / 4 ≤
            x - x ^ 3 / 4 := by
        have hProduct :
            0 ≤ (x - (983 : ℝ) / 10000) *
              (1 -
                (x ^ 2 + x * ((983 : ℝ) / 10000) +
                  ((983 : ℝ) / 10000) ^ 2) / 4) :=
          mul_nonneg (sub_nonneg.mpr hxLower) hFactorPos.le
        nlinarith only [hProduct]
      nlinarith only [hSinCube, hsinePiOver32Upper, hPolynomialMono]
    clear hsqrtTwoSq hsqrtTwoUpper hsqrtTwoLower
      hsqrtTwoPlusSq hsqrtTwoPlusUpper hsqrtTwoPlusLower
      hsqrtThreeLevelSq hsqrtThreeLevelUpper hsqrtThreeLevelLower
      hFinalRadicand hsqrtFinalSq hsinePiOver32Lower hsinePiOver32Upper
    let y : ℝ := 2 * setup.oscillator.ω - Real.pi
    have hyLower : (23 : ℝ) / 50 < y := by
      dsimp [y]
      linarith only [hωLower, hPiUpper]
    have hyUpper : y < (59 : ℝ) / 125 := by
      dsimp [y]
      linarith only [hωUpper, hPiLower]
    have hyPos : 0 < y := by linarith only [hyLower]
    have hyCubeUpper : y ^ 3 < ((59 : ℝ) / 125) ^ 3 := by
      have hSumPos :
          0 < y ^ 2 + y * ((59 : ℝ) / 125) +
            ((59 : ℝ) / 125) ^ 2 := by
        nlinarith only [sq_nonneg y, hyPos]
      have hProduct :
          0 < ((59 : ℝ) / 125 - y) *
            (y ^ 2 + y * ((59 : ℝ) / 125) +
              ((59 : ℝ) / 125) ^ 2) :=
        mul_pos (sub_pos.mpr hyUpper) hSumPos
      nlinarith only [hProduct]
    have hSinYLower : (433 : ℝ) / 1000 < Real.sin y := by
      have h := Real.sin_gt_sub_cube hyPos (by linarith only [hyUpper] : y ≤ 1)
      nlinarith only [h, hyLower, hyCubeUpper]
    let z : ℝ := y / 2
    have hzLower : (23 : ℝ) / 100 < z := by
      dsimp [z]
      linarith only [hyLower]
    have hzUpper : z < (59 : ℝ) / 250 := by
      dsimp [z]
      linarith only [hyUpper]
    have hzPos : 0 < z := by linarith only [hzLower]
    have hzCubeUpper : z ^ 3 < ((59 : ℝ) / 250) ^ 3 := by
      have hSumPos :
          0 < z ^ 2 + z * ((59 : ℝ) / 250) +
            ((59 : ℝ) / 250) ^ 2 := by
        nlinarith only [sq_nonneg z, hzPos]
      have hProduct :
          0 < ((59 : ℝ) / 250 - z) *
            (z ^ 2 + z * ((59 : ℝ) / 250) +
              ((59 : ℝ) / 250) ^ 2) :=
        mul_pos (sub_pos.mpr hzUpper) hSumPos
      nlinarith only [hProduct]
    have hSinZLower : (113 : ℝ) / 500 < Real.sin z := by
      have h := Real.sin_gt_sub_cube hzPos (by linarith only [hzUpper] : z ≤ 1)
      nlinarith only [h, hzLower, hzCubeUpper]
    have hSinZNonneg : 0 ≤ Real.sin z := by
      linarith only [hSinZLower]
    have hCosZNonneg : 0 ≤ Real.cos z := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith only [hzPos, hzUpper, Real.one_le_pi_div_two]
    have hSinZSq :
        ((113 : ℝ) / 500) ^ 2 < (Real.sin z) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hSinZNonneg).mpr hSinZLower
    have hCosZSq :
        (Real.cos z) ^ 2 < ((975 : ℝ) / 1000) ^ 2 := by
      nlinarith only [hSinZSq, Real.sin_sq_add_cos_sq z]
    have hCosZUpper : Real.cos z < (975 : ℝ) / 1000 :=
      (sq_lt_sq₀ hCosZNonneg (by norm_num)).mp hCosZSq
    have hSinZUpper : Real.sin z ≤ z :=
      Real.sin_le hzPos.le
    have hZCosUpper :
        z * Real.cos z <
          ((59 : ℝ) / 250) * ((975 : ℝ) / 1000) := by
      calc
        z * Real.cos z < z * ((975 : ℝ) / 1000) :=
          mul_lt_mul_of_pos_left hCosZUpper hzPos
        _ < ((59 : ℝ) / 250) * ((975 : ℝ) / 1000) :=
          mul_lt_mul_of_pos_right hzUpper (by norm_num)
    have hSinYUpper :
        Real.sin y < ((975 : ℝ) / 1000) * ((59 : ℝ) / 125) := by
      rw [show y = 2 * z by dsimp [z]; ring, Real.sin_two_mul]
      have hProduct :
          Real.sin z * Real.cos z ≤ z * Real.cos z :=
        mul_le_mul_of_nonneg_right hSinZUpper hCosZNonneg
      nlinarith only [hProduct, hZCosUpper]
    have hSinShift :
        Real.sin (setup.oscillator.ω * 2) = -Real.sin y := by
      rw [show setup.oscillator.ω * 2 = y + Real.pi by
        dsimp [y]
        ring, Real.sin_add_pi]
    have hVelocityFormula :
        velocityInMetersPerSecond
            (setup.verticalVelocity setup.observationDelay) =
          -(setup.oscillator.ω * ((2683 : ℝ) / 1350) * Real.sin y) := by
      rw [hVelocity, hSinShift]
      ring
    have hCoefficientLower :
        ((1803 : ℝ) / 1000) * ((2683 : ℝ) / 1350) <
          setup.oscillator.ω * ((2683 : ℝ) / 1350) :=
      mul_lt_mul_of_pos_right hωLower (by norm_num)
    have hCoefficientUpper :
        setup.oscillator.ω * ((2683 : ℝ) / 1350) <
          ((1804 : ℝ) / 1000) * ((2683 : ℝ) / 1350) :=
      mul_lt_mul_of_pos_right hωUpper (by norm_num)
    have hCoefficientPos :
        0 < setup.oscillator.ω * ((2683 : ℝ) / 1350) :=
      mul_pos hωpos (by norm_num)
    have hMagnitudeLower :
        (31 : ℝ) / 20 <
          setup.oscillator.ω * ((2683 : ℝ) / 1350) * Real.sin y := by
      have hSinYPos : 0 < Real.sin y := by linarith only [hSinYLower]
      calc
        (31 : ℝ) / 20 <
            (((1803 : ℝ) / 1000) * ((2683 : ℝ) / 1350)) *
              ((433 : ℝ) / 1000) := by norm_num
        _ < setup.oscillator.ω * ((2683 : ℝ) / 1350) *
            Real.sin y := by
          have h₁ :
              (((1803 : ℝ) / 1000) * ((2683 : ℝ) / 1350)) *
                  ((433 : ℝ) / 1000) <
                (setup.oscillator.ω * ((2683 : ℝ) / 1350)) *
                  ((433 : ℝ) / 1000) :=
            mul_lt_mul_of_pos_right hCoefficientLower (by norm_num)
          have h₂ :
              (setup.oscillator.ω * ((2683 : ℝ) / 1350)) *
                  ((433 : ℝ) / 1000) <
                (setup.oscillator.ω * ((2683 : ℝ) / 1350)) *
                  Real.sin y :=
            mul_lt_mul_of_pos_left hSinYLower hCoefficientPos
          linarith only [h₁, h₂]
    have hMagnitudeUpper :
        setup.oscillator.ω * ((2683 : ℝ) / 1350) * Real.sin y <
          (33 : ℝ) / 20 := by
      have hSinYPos : 0 < Real.sin y := by linarith only [hSinYLower]
      calc
        setup.oscillator.ω * ((2683 : ℝ) / 1350) * Real.sin y <
            (((1804 : ℝ) / 1000) * ((2683 : ℝ) / 1350)) *
              (((975 : ℝ) / 1000) * ((59 : ℝ) / 125)) := by
          have h₁ :
              (setup.oscillator.ω * ((2683 : ℝ) / 1350)) *
                  Real.sin y <
                (((1804 : ℝ) / 1000) * ((2683 : ℝ) / 1350)) *
                  Real.sin y :=
            mul_lt_mul_of_pos_right hCoefficientUpper hSinYPos
          have h₂ :
              (((1804 : ℝ) / 1000) * ((2683 : ℝ) / 1350)) *
                  Real.sin y <
                (((1804 : ℝ) / 1000) * ((2683 : ℝ) / 1350)) *
                  (((975 : ℝ) / 1000) * ((59 : ℝ) / 125)) :=
            mul_lt_mul_of_pos_left hSinYUpper (by norm_num)
          linarith only [h₁, h₂]
        _ < (33 : ℝ) / 20 := by norm_num
    have hVelocityLower :
        -(33 : ℝ) / 20 <
          velocityInMetersPerSecond
            (setup.verticalVelocity setup.observationDelay) := by
      rw [hVelocityFormula]
      linarith only [hMagnitudeUpper]
    have hVelocityUpper :
        velocityInMetersPerSecond
            (setup.verticalVelocity setup.observationDelay) <
          -(31 : ℝ) / 20 := by
      rw [hVelocityFormula]
      linarith only [hMagnitudeLower]
    have hClose :
        abs (velocityInMetersPerSecond
              (setup.verticalVelocity setup.observationDelay) -
            AnswerChoice.velocityMetersPerSecond .C) < 1 / 20 := by
      rw [AnswerChoice.velocityMetersPerSecond, abs_lt]
      constructor
      · linarith only [hVelocityLower]
      · linarith only [hVelocityUpper]
    refine ⟨hClose, ?_⟩
    intro choice hChoice
    cases choice with
    | A =>
        simp only [AnswerChoice.velocityMetersPerSecond]
        calc
          abs (velocityInMetersPerSecond
                (setup.verticalVelocity setup.observationDelay) - -8 / 5) <
              (1 : ℝ) / 20 := by
            simpa only [AnswerChoice.velocityMetersPerSecond] using hClose
          _ < abs (velocityInMetersPerSecond
                (setup.verticalVelocity setup.observationDelay) - -2) := by
            rw [abs_of_pos (by linarith only [hVelocityLower])]
            linarith only [hVelocityLower]
    | B =>
        simp only [AnswerChoice.velocityMetersPerSecond]
        calc
          abs (velocityInMetersPerSecond
                (setup.verticalVelocity setup.observationDelay) - -8 / 5) <
              (1 : ℝ) / 20 := by
            simpa only [AnswerChoice.velocityMetersPerSecond] using hClose
          _ < abs (velocityInMetersPerSecond
                (setup.verticalVelocity setup.observationDelay) - (-9 / 5)) := by
            rw [abs_of_pos (by linarith only [hVelocityLower])]
            linarith only [hVelocityLower]
    | C =>
        exact (hChoice rfl).elim
    | D =>
        simp only [AnswerChoice.velocityMetersPerSecond]
        calc
          abs (velocityInMetersPerSecond
                (setup.verticalVelocity setup.observationDelay) - -8 / 5) <
              (1 : ℝ) / 20 := by
            simpa only [AnswerChoice.velocityMetersPerSecond] using hClose
          _ < abs (velocityInMetersPerSecond
                (setup.verticalVelocity setup.observationDelay) - (-7 / 5)) := by
            rw [abs_of_neg (by linarith only [hVelocityUpper])]
            linarith only [hVelocityUpper]

end PhyXMiniProblems.ProblemPhyXMini0718
