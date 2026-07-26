import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Two blocks released from a compressed spring

Block `m₁` is attached to a light spring on a frictionless horizontal surface.
Block `m₂` is pushed against it while the spring is compressed by `A`, and the
two blocks are released from rest.  They move together until the spring first
reaches its equilibrium length.  Afterwards `m₂` moves freely while `m₁`
executes simple harmonic motion.

Masses, lengths, durations, speeds, and spring stiffness are represented by
unit-independent Physlib quantities.  Real numbers occur only as coherent
unit readouts, dimensionless trigonometric arguments, and answer-choice data.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0236

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical length or signed one-dimensional displacement. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical duration. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A one-dimensional speed magnitude, with dimension length per time. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-!
A spring constant has dimension force per length, equivalently mass per time
squared.  Its SI readout is measured in newtons per metre.
-/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  (mass {UnitChoices.SI with mass := unit}).val

/-- Read a length or displacement in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  (duration {UnitChoices.SI with time := unit}).val

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a spring constant in coherent selected mass and time units. -/
def springConstantReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (springConstant : SpringConstantQuantity) : ℝ :=
  (springConstant {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val

/-- Kilogram readout used for the two stated masses. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout used for the compression and the governing laws. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the displayed answers. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Second readout used for elapsed time after the blocks cease touching. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Metres-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Newton-per-metre readout of the spring constant. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  springConstantReadout MassUnit.kilograms TimeUnit.seconds springConstant

/-! ## Objects and primary-figure labels -/

/-- The two blocks labeled in panels (a)--(d). -/
inductive Block where
  | m1
  | m2
  deriving DecidableEq, Repr

/-- The four panels in the supplied image. -/
inductive FigurePanel where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

/-- Horizontal arrow directions in the figure. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Qualitative state of the spring relative to its equilibrium length. -/
inductive SpringState where
  | compressed
  | atEquilibrium
  | stretched
  deriving DecidableEq, Repr

/-- Distance labels printed under panels (b) and (d). -/
inductive FigureDistanceMark where
  | A
  | D
  deriving DecidableEq, Repr

/-- Surface idealizations relevant to the horizontal motion. -/
inductive SurfaceCondition where
  | frictionless
  | resistive
  deriving DecidableEq, Repr

/-- Idealization of the spring stated in the problem. -/
inductive SpringIdealization where
  | lightLinear
  | massiveOrNonlinear
  deriving DecidableEq, Repr

/-!
Qualitative evidence transcribed from the four-panel primary image.  The
boolean distance marks record only the appearances of `A` and `D`; their
physical values live in the setup and are not inferred from pixels.
-/
structure TwoBlockSpringFigure where
  showsBlock : FigurePanel → Block → Bool
  showsWallMountedSpring : FigurePanel → Bool
  springState : FigurePanel → SpringState
  springAttachedTo : FigurePanel → Block → Bool
  blocksTouch : FigurePanel → Bool
  velocityArrowDirection : FigurePanel → Block → Option HorizontalDirection
  showsDistanceMark : FigurePanel → FigureDistanceMark → Bool
  isLeftOf : FigurePanel → Block → Block → Bool

/-! ## Physical setup, supplied data, and governing model -/

/-!
Independent physical quantities for the two stages of the motion.

The displacement functions use the spring equilibrium position as origin.
After contact ends, `m1DisplacementAfterContactEnd t` is the rightward signed
displacement of `m₁`, while `m2DisplacementAfterContactEnd t` is the distance
traveled freely by `m₂`.  The separation is stored independently and is
related to those displacements only by the geometry law below.
-/
structure TwoBlockSpringSetup where
  mass : Block → MassQuantity
  springConstant_k : SpringConstantQuantity
  initialCompression_A : LengthQuantity
  commonReleaseSpeed : SpeedQuantity
  commonSpeedAtContactEnd : SpeedQuantity
  firstMaximumStretchTime : DurationQuantity
  m1DisplacementAfterContactEnd : DurationQuantity → LengthQuantity
  m2DisplacementAfterContactEnd : DurationQuantity → LengthQuantity
  separationAfterContactEnd : DurationQuantity → LengthQuantity
  m1OscillatorSIReadout : ClassicalMechanics.HarmonicOscillator
  surfaceCondition : SurfaceCondition
  springIdealization : SpringIdealization
  releaseDirection : HorizontalDirection
  springAttachedBlock : Block
  figure : TwoBlockSpringFigure

/-!
Numerical data from the prose and qualitative facts from the primary image.
Panel (a) supplies the equilibrium reference; (b) shows compression `A` and
touching blocks; (c) shows their common rightward motion at equilibrium; and
(d) shows stretched `m₁`, freely moving `m₂`, and the unknown distance `D`.
No numerical value for `D` occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TwoBlockSpringSetup) : Prop where
  mass1Kilograms : massInKilograms (setup.mass .m1) = 9
  mass2Kilograms : massInKilograms (setup.mass .m2) = 7
  springConstantNewtonsPerMeter :
    springConstantInNewtonsPerMeter setup.springConstant_k = 100
  compressionMeters : lengthInMeters setup.initialCompression_A = 1 / 5
  releasedFromRest : speedInMetersPerSecond setup.commonReleaseSpeed = 0
  frictionlessSurface : setup.surfaceCondition = .frictionless
  lightLinearSpring : setup.springIdealization = .lightLinear
  releasedTowardRight : setup.releaseDirection = .right
  springAttachedOnlyToM1 : setup.springAttachedBlock = .m1
  wallSpringShown : ∀ panel, setup.figure.showsWallMountedSpring panel = true
  springAttachedToM1InEveryPanel :
    ∀ panel, setup.figure.springAttachedTo panel .m1 = true
  springNotAttachedToM2 :
    ∀ panel, setup.figure.springAttachedTo panel .m2 = false
  panelAOnlyShowsM1 :
    setup.figure.showsBlock .a .m1 = true ∧
      setup.figure.showsBlock .a .m2 = false
  panelAEquilibrium : setup.figure.springState .a = .atEquilibrium
  panelBShowsBothBlocks :
    setup.figure.showsBlock .b .m1 = true ∧
      setup.figure.showsBlock .b .m2 = true
  panelBCompressedAndTouching :
    setup.figure.springState .b = .compressed ∧
      setup.figure.blocksTouch .b = true
  panelBCompressionMark : setup.figure.showsDistanceMark .b .A = true
  panelCShowsBothBlocks :
    setup.figure.showsBlock .c .m1 = true ∧
      setup.figure.showsBlock .c .m2 = true
  panelCAtEquilibriumAndTouching :
    setup.figure.springState .c = .atEquilibrium ∧
      setup.figure.blocksTouch .c = true
  panelCCommonRightwardMotion :
    setup.figure.velocityArrowDirection .c .m1 = some .right ∧
      setup.figure.velocityArrowDirection .c .m2 = some .right
  panelDShowsSeparatedBlocks :
    setup.figure.showsBlock .d .m1 = true ∧
      setup.figure.showsBlock .d .m2 = true ∧
      setup.figure.blocksTouch .d = false
  panelDStretchedSpring : setup.figure.springState .d = .stretched
  panelDM2MovesRightAlone :
    setup.figure.velocityArrowDirection .d .m1 = none ∧
      setup.figure.velocityArrowDirection .d .m2 = some .right
  panelDM1LeftOfM2 : setup.figure.isLeftOf .d .m1 .m2 = true
  panelDSeparationMark : setup.figure.showsDistanceMark .d .D = true

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalParameters (setup : TwoBlockSpringSetup) : Prop where
  mass1Positive : 0 < massInKilograms (setup.mass .m1)
  mass2Positive : 0 < massInKilograms (setup.mass .m2)
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant_k
  compressionPositive : 0 < lengthInMeters setup.initialCompression_A
  contactEndSpeedPositive :
    0 < speedInMetersPerSecond setup.commonSpeedAtContactEnd
  firstMaximumTimePositive :
    0 < durationInSeconds setup.firstMaximumStretchTime

/-!
The selected time is the first time at which `m₁` reaches a global maximum
rightward extension after the blocks cease touching.  Global maximality says
the spring is fully stretched; strict inequality at every earlier nonnegative
time selects its first occurrence.
-/
def IsFirstMaximumSpringExtension
    (setup : TwoBlockSpringSetup) (eventTime : DurationQuantity) : Prop :=
  0 < durationInSeconds eventTime ∧
    (∀ otherTime : DurationQuantity,
      0 ≤ durationInSeconds otherTime →
      lengthInMeters (setup.m1DisplacementAfterContactEnd otherTime) ≤
        lengthInMeters (setup.m1DisplacementAfterContactEnd eventTime)) ∧
    (∀ earlierTime : DurationQuantity,
      0 ≤ durationInSeconds earlierTime →
      durationInSeconds earlierTime < durationInSeconds eventTime →
      lengthInMeters (setup.m1DisplacementAfterContactEnd earlierTime) <
        lengthInMeters (setup.m1DisplacementAfterContactEnd eventTime))

/-!
Governing laws for the two motion stages.

* Mechanical energy is conserved while the touching blocks move together
  from the compressed release state to the equilibrium/contact-end state.
* Physlib's harmonic oscillator is tied to the SI readouts of `m₁` and `k`.
* After contact ends, `m₁` follows the SHO solution with initial velocity
  `v`, while `m₂` moves uniformly at the same speed.
* Their separation is the free-block displacement minus the spring-block
  displacement.

These laws do not mention the requested numerical separation or any answer
choice.
-/
structure SatisfiesTwoStageSpringDynamics
    (setup : TwoBlockSpringSetup) : Prop where
  oscillatorMassIsM1Readout :
    setup.m1OscillatorSIReadout.m = massInKilograms (setup.mass .m1)
  oscillatorSpringConstantIsReadout :
    setup.m1OscillatorSIReadout.k =
      springConstantInNewtonsPerMeter setup.springConstant_k
  jointMotionEnergyConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      (massReadout massUnit (setup.mass .m1) +
          massReadout massUnit (setup.mass .m2)) *
            speedReadout lengthUnit timeUnit setup.commonReleaseSpeed ^ 2 +
        springConstantReadout massUnit timeUnit setup.springConstant_k *
            lengthReadout lengthUnit setup.initialCompression_A ^ 2 =
      (massReadout massUnit (setup.mass .m1) +
          massReadout massUnit (setup.mass .m2)) *
            speedReadout lengthUnit timeUnit setup.commonSpeedAtContactEnd ^ 2
  m1SimpleHarmonicMotion :
    ∀ elapsedTime : DurationQuantity,
      0 ≤ durationInSeconds elapsedTime →
      lengthInMeters (setup.m1DisplacementAfterContactEnd elapsedTime) =
        speedInMetersPerSecond setup.commonSpeedAtContactEnd /
            setup.m1OscillatorSIReadout.ω *
          Real.sin
            (setup.m1OscillatorSIReadout.ω *
              durationInSeconds elapsedTime)
  m2UniformMotion :
    ∀ elapsedTime : DurationQuantity,
      0 ≤ durationInSeconds elapsedTime →
      lengthInMeters (setup.m2DisplacementAfterContactEnd elapsedTime) =
        speedInMetersPerSecond setup.commonSpeedAtContactEnd *
          durationInSeconds elapsedTime
  separationGeometry :
    ∀ elapsedTime : DurationQuantity,
      0 ≤ durationInSeconds elapsedTime →
      lengthInMeters (setup.separationAfterContactEnd elapsedTime) =
        lengthInMeters (setup.m2DisplacementAfterContactEnd elapsedTime) -
          lengthInMeters (setup.m1DisplacementAfterContactEnd elapsedTime)

/-! ## Derived stage relations -/

/-!
Energy conservation during the common-motion stage gives the speed at the
instant contact ends and the spring reaches equilibrium.
-/
lemma contactEndSpeed_eq_compression_mul_sqrt_stiffness_div_totalMass
    (setup : TwoBlockSpringSetup)
    (hProblem : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hDynamics : SatisfiesTwoStageSpringDynamics setup) :
    speedInMetersPerSecond setup.commonSpeedAtContactEnd =
      lengthInMeters setup.initialCompression_A *
        Real.sqrt
          (springConstantInNewtonsPerMeter setup.springConstant_k /
            (massInKilograms (setup.mass .m1) +
              massInKilograms (setup.mass .m2))) := by
  have hEnergy :=
    hDynamics.jointMotionEnergyConservation
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    (massInKilograms (setup.mass .m1) +
        massInKilograms (setup.mass .m2)) *
          speedInMetersPerSecond setup.commonReleaseSpeed ^ 2 +
      springConstantInNewtonsPerMeter setup.springConstant_k *
          lengthInMeters setup.initialCompression_A ^ 2 =
    (massInKilograms (setup.mass .m1) +
        massInKilograms (setup.mass .m2)) *
          speedInMetersPerSecond setup.commonSpeedAtContactEnd ^ 2 at hEnergy
  rw [hProblem.mass1Kilograms, hProblem.mass2Kilograms,
    hProblem.springConstantNewtonsPerMeter, hProblem.compressionMeters,
    hProblem.releasedFromRest] at hEnergy
  rw [hProblem.mass1Kilograms, hProblem.mass2Kilograms,
    hProblem.springConstantNewtonsPerMeter, hProblem.compressionMeters]
  have hSpeed :
      speedInMetersPerSecond setup.commonSpeedAtContactEnd = 1 / 2 := by
    nlinarith [hPhysical.contactEndSpeedPositive]
  rw [hSpeed]
  have hSquareRoot :
      Real.sqrt (100 / (9 + 7) : ℝ) = 5 / 2 := by
    rw [show (100 / (9 + 7) : ℝ) = (5 / 2) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  rw [hSquareRoot]
  norm_num

/-!
The first global maximum of the post-contact sine trajectory occurs one
quarter of an `m₁` oscillator period after contact ends.
-/
lemma firstMaximumStretchTime_eq_quarterPeriod
    (setup : TwoBlockSpringSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hDynamics : SatisfiesTwoStageSpringDynamics setup)
    (hFirstMaximum :
      IsFirstMaximumSpringExtension setup setup.firstMaximumStretchTime) :
    durationInSeconds setup.firstMaximumStretchTime =
      Real.pi / (2 * setup.m1OscillatorSIReadout.ω) := by
  let quarterTime : DurationQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨Real.pi / (2 * setup.m1OscillatorSIReadout.ω)⟩ :
        WithDim T𝓭 ℝ)
  have hQuarterReadout :
      durationInSeconds quarterTime =
        Real.pi / (2 * setup.m1OscillatorSIReadout.ω) := by
    simp [quarterTime, durationInSeconds, durationReadout,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale]
  have hOmegaPositive : 0 < setup.m1OscillatorSIReadout.ω :=
    setup.m1OscillatorSIReadout.ω_pos
  have hQuarterPositive :
      0 < Real.pi / (2 * setup.m1OscillatorSIReadout.ω) :=
    div_pos Real.pi_pos (mul_pos (by norm_num) hOmegaPositive)
  have hQuarterNonnegative : 0 ≤ durationInSeconds quarterTime := by
    rw [hQuarterReadout]
    exact hQuarterPositive.le
  have hCoefficientPositive :
      0 <
        speedInMetersPerSecond setup.commonSpeedAtContactEnd /
          setup.m1OscillatorSIReadout.ω :=
    div_pos hPhysical.contactEndSpeedPositive hOmegaPositive
  have hQuarterPhase :
      setup.m1OscillatorSIReadout.ω *
          durationInSeconds quarterTime =
        Real.pi / 2 := by
    rw [hQuarterReadout]
    field_simp [ne_of_gt hOmegaPositive]
  have hQuarterDisplacement :
      lengthInMeters
          (setup.m1DisplacementAfterContactEnd quarterTime) =
        speedInMetersPerSecond setup.commonSpeedAtContactEnd /
          setup.m1OscillatorSIReadout.ω := by
    rw [hDynamics.m1SimpleHarmonicMotion quarterTime hQuarterNonnegative,
      hQuarterPhase, Real.sin_pi_div_two, mul_one]
  have hEventNonnegative :
      0 ≤ durationInSeconds setup.firstMaximumStretchTime :=
    hFirstMaximum.1.le
  have hEventDisplacement :=
    hDynamics.m1SimpleHarmonicMotion
      setup.firstMaximumStretchTime hEventNonnegative
  apply le_antisymm
  · by_contra hNotLe
    have hQuarterEarlier :
        durationInSeconds quarterTime <
          durationInSeconds setup.firstMaximumStretchTime := by
      rw [hQuarterReadout]
      exact lt_of_not_ge hNotLe
    have hStrict :=
      hFirstMaximum.2.2 quarterTime hQuarterNonnegative hQuarterEarlier
    rw [hQuarterDisplacement, hEventDisplacement] at hStrict
    nlinarith [Real.sin_le_one
      (setup.m1OscillatorSIReadout.ω *
        durationInSeconds setup.firstMaximumStretchTime)]
  · by_contra hNotLe
    have hEventEarlierThanQuarter :
        durationInSeconds setup.firstMaximumStretchTime <
          durationInSeconds quarterTime :=
      by
        rw [hQuarterReadout]
        exact lt_of_not_ge hNotLe
    have hPhaseLower :
        -(Real.pi / 2) ≤
          setup.m1OscillatorSIReadout.ω *
            durationInSeconds setup.firstMaximumStretchTime := by
      have hPhaseNonnegative :
          0 ≤
            setup.m1OscillatorSIReadout.ω *
              durationInSeconds setup.firstMaximumStretchTime :=
        mul_nonneg hOmegaPositive.le hEventNonnegative
      linarith [Real.pi_pos]
    have hPhaseUpper :
        setup.m1OscillatorSIReadout.ω *
            durationInSeconds setup.firstMaximumStretchTime <
          Real.pi / 2 := by
      rw [← hQuarterPhase]
      exact mul_lt_mul_of_pos_left hEventEarlierThanQuarter hOmegaPositive
    have hSinStrict :
        Real.sin
            (setup.m1OscillatorSIReadout.ω *
              durationInSeconds setup.firstMaximumStretchTime) <
          1 := by
      rw [← Real.sin_pi_div_two]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        hPhaseLower le_rfl hPhaseUpper
    have hGlobal :=
      hFirstMaximum.2.1 quarterTime hQuarterNonnegative
    rw [hQuarterDisplacement, hEventDisplacement] at hGlobal
    nlinarith

/-!
Combining the common contact-end speed, the quarter-period SHO motion, free
motion of `m₂`, and one-dimensional separation geometry eliminates `k` and
gives the exact general separation formula.
-/
lemma firstMaximumSeparation_formula
    (setup : TwoBlockSpringSetup)
    (hProblem : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hDynamics : SatisfiesTwoStageSpringDynamics setup)
    (hFirstMaximum :
      IsFirstMaximumSpringExtension setup setup.firstMaximumStretchTime) :
    lengthInMeters
        (setup.separationAfterContactEnd setup.firstMaximumStretchTime) =
      lengthInMeters setup.initialCompression_A *
        Real.sqrt
          (massInKilograms (setup.mass .m1) /
            (massInKilograms (setup.mass .m1) +
              massInKilograms (setup.mass .m2))) *
        (Real.pi / 2 - 1) := by
  have hSpeed :=
    contactEndSpeed_eq_compression_mul_sqrt_stiffness_div_totalMass
      setup hProblem hPhysical hDynamics
  rw [hProblem.mass1Kilograms, hProblem.mass2Kilograms,
    hProblem.springConstantNewtonsPerMeter, hProblem.compressionMeters] at hSpeed
  have hSpeedSquareRoot :
      Real.sqrt (100 / (9 + 7) : ℝ) = 5 / 2 := by
    rw [show (100 / (9 + 7) : ℝ) = (5 / 2) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  rw [hSpeedSquareRoot] at hSpeed
  norm_num at hSpeed
  have hOscillatorMass :
      setup.m1OscillatorSIReadout.m = 9 := by
    rw [hDynamics.oscillatorMassIsM1Readout,
      hProblem.mass1Kilograms]
  have hOscillatorSpringConstant :
      setup.m1OscillatorSIReadout.k = 100 := by
    rw [hDynamics.oscillatorSpringConstantIsReadout,
      hProblem.springConstantNewtonsPerMeter]
  have hOmega :
      setup.m1OscillatorSIReadout.ω = 10 / 3 := by
    rw [ClassicalMechanics.HarmonicOscillator.ω,
      hOscillatorMass, hOscillatorSpringConstant]
    rw [show (100 / 9 : ℝ) = (10 / 3) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  have hTime :=
    firstMaximumStretchTime_eq_quarterPeriod
      setup hPhysical hDynamics hFirstMaximum
  rw [hOmega] at hTime
  have hTimeValue :
      durationInSeconds setup.firstMaximumStretchTime =
        3 * Real.pi / 20 := by
    rw [hTime]
    ring
  have hEventNonnegative :
      0 ≤ durationInSeconds setup.firstMaximumStretchTime :=
    hFirstMaximum.1.le
  have hM1Displacement :=
    hDynamics.m1SimpleHarmonicMotion
      setup.firstMaximumStretchTime hEventNonnegative
  rw [hSpeed, hOmega, hTimeValue] at hM1Displacement
  have hPhase :
      (10 / 3 : ℝ) * (3 * Real.pi / 20) = Real.pi / 2 := by
    ring
  rw [hPhase, Real.sin_pi_div_two] at hM1Displacement
  norm_num at hM1Displacement
  have hM2Displacement :=
    hDynamics.m2UniformMotion
      setup.firstMaximumStretchTime hEventNonnegative
  rw [hSpeed, hTimeValue] at hM2Displacement
  have hSeparation :=
    hDynamics.separationGeometry
      setup.firstMaximumStretchTime hEventNonnegative
  rw [hM1Displacement, hM2Displacement] at hSeparation
  rw [hSeparation, hProblem.mass1Kilograms, hProblem.mass2Kilograms,
    hProblem.compressionMeters]
  have hMassSquareRoot :
      Real.sqrt (9 / (9 + 7) : ℝ) = 3 / 4 := by
    rw [show (9 / (9 + 7) : ℝ) = (3 / 4) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  rw [hMassSquareRoot]
  ring

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Separation in centimetres printed beside each answer label. -/
def AnswerChoice.displayedCentimeters : AnswerChoice → ℝ
  | .A => 443 / 50
  | .B => 219 / 25
  | .C => 433 / 50
  | .D => 214 / 25

/-!
Agreement with a separation displayed to the nearest hundredth of a
centimetre.  This rounding predicate is answer-list metadata, not a premise.
-/
def MatchesAnswerChoice
    (separation : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters separation - choice.displayedCentimeters| ≤ 1 / 200

/-!
For `m₁ = 9 kg`, `m₂ = 7 kg`, and `A = 0.200 m`, the exact ideal-model
separation is

`(3/20) * (π/2 - 1) m = 15 * (π/2 - 1) cm`,

which rounds to `8.56 cm`, displayed as answer D.

This formalizes `thm:physics:phyx_mini_0236:target`.  The exact separation,
`8.56 cm`, and answer D do not occur in any hypothesis or governing-law field.
-/
theorem firstFullyStretchedSeparation_matches_answerD
    (setup : TwoBlockSpringSetup)
    (hProblem : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hDynamics : SatisfiesTwoStageSpringDynamics setup)
    (hFirstMaximum :
      IsFirstMaximumSpringExtension setup setup.firstMaximumStretchTime) :
    lengthInMeters
        (setup.separationAfterContactEnd setup.firstMaximumStretchTime) =
        (3 / 20 : ℝ) * (Real.pi / 2 - 1) ∧
      MatchesAnswerChoice
        (setup.separationAfterContactEnd setup.firstMaximumStretchTime) .D := by
  have hMassSquareRoot :
      Real.sqrt (9 / (9 + 7) : ℝ) = 3 / 4 := by
    rw [show (9 / (9 + 7) : ℝ) = (3 / 4) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  have hExact :
      lengthInMeters
          (setup.separationAfterContactEnd setup.firstMaximumStretchTime) =
        (3 / 20 : ℝ) * (Real.pi / 2 - 1) := by
    rw [firstMaximumSeparation_formula
      setup hProblem hPhysical hDynamics hFirstMaximum]
    rw [hProblem.mass1Kilograms, hProblem.mass2Kilograms,
      hProblem.compressionMeters, hMassSquareRoot]
    ring
  constructor
  · exact hExact
  · have hCentimetersToMeters (length : LengthQuantity) :
        lengthInCentimeters length = 100 * lengthInMeters length := by
      have hUnits := length.2 UnitChoices.SI
        ({UnitChoices.SI with
          length := LengthUnit.centimeters} : UnitChoices)
      have hUnitsReal := congrArg
        (fun reading : WithDim L𝓭 ℝ => reading.val) hUnits
      norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
        UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
        LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
        smul_eq_mul] at hUnitsReal ⊢
      exact hUnitsReal
    rw [MatchesAnswerChoice, hCentimetersToMeters, hExact,
      AnswerChoice.displayedCentimeters]
    have pi_gt_sqrtTwoAddSeries (n : ℕ) :
        2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) <
          Real.pi := by
      have h :
          √(2 - Real.sqrtTwoAddSeries 0 n) / 2 *
              2 ^ (n + 2) <
            Real.pi := by
        rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
        focus
          apply Real.sin_lt
          apply div_pos Real.pi_pos
        all_goals apply pow_pos
        all_goals norm_num
      refine lt_of_le_of_lt (le_of_eq ?_) h
      rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀,
        mul_comm]
      simp
    have pi_lower_bound_start (n : ℕ) {a : ℝ}
        (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
          (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
        a < Real.pi := by
      refine lt_of_le_of_lt ?_ (pi_gt_sqrtTwoAddSeries n)
      rw [mul_comm]
      refine (div_le_iff₀ (pow_pos (by simp) _)).mp
        (Real.le_sqrt_of_sq_le ?_)
      rwa [le_sub_comm,
        show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
          rw [Nat.cast_zero, zero_div]]
    have sqrtTwoAddSeries_step_up
        (c d : ℕ) {a b n : ℕ} {z : ℝ}
        (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
        (hb : 0 < b) (hd : 0 < d)
        (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
        Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
      refine le_trans ?_ hz
      rw [Real.sqrtTwoAddSeries_succ]
      apply Real.sqrtTwoAddSeries_monotone_left
      have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
      have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
      rw [Real.sqrt_le_left
          (div_nonneg c.cast_nonneg d.cast_nonneg),
        div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
        div_le_div_iff₀ hb' (pow_pos hd' _)]
      exact_mod_cast h
    have hPiLower : (31415 / 10000 : ℝ) < Real.pi := by
      apply pi_lower_bound_start 6
      apply sqrtTwoAddSeries_step_up 1970 1393
      case hb => norm_num
      case hd => norm_num
      case h => norm_num
      case hz =>
        apply sqrtTwoAddSeries_step_up 3010 1629
        case hb => norm_num
        case hd => norm_num
        case h => norm_num
        case hz =>
          apply sqrtTwoAddSeries_step_up 11689 5959
          case hb => norm_num
          case hd => norm_num
          case h => norm_num
          case hz =>
            apply sqrtTwoAddSeries_step_up 10127 5088
            case hb => norm_num
            case hd => norm_num
            case h => norm_num
            case hz =>
              apply sqrtTwoAddSeries_step_up 33997 17019
              case hb => norm_num
              case hd => norm_num
              case h => norm_num
              case hz =>
                apply sqrtTwoAddSeries_step_up 23235 11621
                case hb => norm_num
                case hd => norm_num
                case h => norm_num
                case hz => norm_num [Real.sqrtTwoAddSeries]
    have pi_lt_sqrtTwoAddSeries (n : ℕ) :
        Real.pi <
          2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) +
            1 / 4 ^ n := by
      have h :
          Real.pi <
            (√(2 - Real.sqrtTwoAddSeries 0 n) / 2 +
                1 / (2 ^ n) ^ 3 / 4) *
              (2 : ℝ) ^ (n + 2) := by
        rw [← div_lt_iff₀ (by simp),
          ← Real.sin_pi_over_two_pow_succ,
          ← sub_lt_iff_lt_add']
        calc
          Real.pi / 2 ^ (n + 2) -
                Real.sin (Real.pi / 2 ^ (n + 2)) <
              (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
            sub_lt_comm.1 <| Real.sin_gt_sub_cube (by positivity) <|
              div_le_one_of_le₀ ?_ (by positivity)
          _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
            gcongr
            exact Real.pi_le_four
          _ = 1 / (2 ^ n) ^ 3 / 4 := by
            simp [add_comm n, pow_add, div_mul_eq_div_div]
            norm_num
        calc
          Real.pi ≤ 4 := Real.pi_le_four
          _ = 2 ^ (0 + 2) := by norm_num
          _ ≤ 2 ^ (n + 2) := by
            gcongr <;> norm_num
      refine lt_of_lt_of_le h (le_of_eq ?_)
      rw [add_mul]
      congr 1
      · ring
      simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
        div_div, ← pow_add]
      rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
        mul_inv_eq_iff_eq_mul₀, ← pow_add]
      · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n,
          add_assoc, mul_comm n]
      all_goals norm_num
    have pi_upper_bound_start (n : ℕ) {a : ℝ}
        (h : (2 : ℝ) -
            ((a - 1 / (4 : ℝ) ^ n) /
              (2 : ℝ) ^ (n + 1)) ^ 2 ≤
          Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
        (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
        Real.pi < a := by
      refine lt_of_lt_of_le (pi_lt_sqrtTwoAddSeries n) ?_
      rw [← le_sub_iff_add_le, ← le_div_iff₀',
        Real.sqrt_le_left, sub_le_comm]
      · rwa [Nat.cast_zero, zero_div] at h
      · exact div_nonneg (sub_nonneg.2 h₂)
          (pow_nonneg (le_of_lt zero_lt_two) _)
      · exact pow_pos zero_lt_two _
    have sqrtTwoAddSeries_step_down
        (a b : ℕ) {c d n : ℕ} {z : ℝ}
        (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
        (hb : 0 < b) (hd : 0 < d)
        (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
        z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
      apply le_trans hz
      rw [Real.sqrtTwoAddSeries_succ]
      apply Real.sqrtTwoAddSeries_monotone_left
      apply Real.le_sqrt_of_sq_le
      have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
      have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
      rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
        div_le_div_iff₀ (pow_pos hb' _) hd']
      exact_mod_cast h
    have hPiUpper : Real.pi < (1571 / 500 : ℝ) := by
      apply pi_upper_bound_start 6
      · apply sqrtTwoAddSeries_step_down 4756 3363
        case hb => norm_num
        case hd => norm_num
        case h => norm_num
        case hz =>
          apply sqrtTwoAddSeries_step_down 14965 8099
          case hb => norm_num
          case hd => norm_num
          case h => norm_num
          case hz =>
            apply sqrtTwoAddSeries_step_down 21183 10799
            case hb => norm_num
            case hd => norm_num
            case h => norm_num
            case hz =>
              apply sqrtTwoAddSeries_step_down 49188 24713
              case hb => norm_num
              case hd => norm_num
              case h => norm_num
              case hz =>
                apply sqrtTwoAddSeries_step_down 43947 22000
                case hb => norm_num
                case hd => norm_num
                case h => norm_num
                case hz =>
                  apply sqrtTwoAddSeries_step_down 235667 117869
                  case hb => norm_num
                  case hd => norm_num
                  case h => norm_num
                  case hz => norm_num [Real.sqrtTwoAddSeries]
      · norm_num
    rw [abs_le]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0236
