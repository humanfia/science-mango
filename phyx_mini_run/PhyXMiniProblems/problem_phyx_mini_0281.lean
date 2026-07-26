import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/-!
# Pendulum with the frequency of a vertically suspended spring--block system

A block hung from the spring labeled `k` produces the equilibrium extension
`h = 2.0 cm`.  After a small downward pull and release, the block oscillates
vertically.  The question asks for the length of a simple pendulum having the
same frequency.

Masses, lengths, velocities, accelerations, spring stiffnesses, and
frequencies are represented by Physlib `Dimensionful` quantities.  Real
numbers occur only as coherent unit readouts and as displayed answer values.

Assumption/target boundary:

* the problem and image supply the spring label `k`, the extension label `h`,
  the fixed supports, the block and pendulum geometry, and the `2.0 cm`
  extension readout;
* governing laws supply static weight balance and the two small-oscillation
  frequency formulas, using Physlib's harmonic-oscillator API;
* the pendulum is required to match the spring's frequency;
* `pendulumLength = h`, its `2.0 cm` readout, and answer `D` are conclusions
  only.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0281

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical speed or one-dimensional velocity magnitude. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Spring stiffness, equivalently force per length, with dimension `M T⁻²`. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Cyclic frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a velocity magnitude. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  ((velocity UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Newton-per-metre readout of a spring stiffness. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Hertz readout of a cyclic frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of an angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-! ## Primary-image panels, labels, and geometry -/

/-- The three side-by-side configurations shown in the supplied image. -/
inductive FigurePanel where
  | unloadedSpring
  | loadedSpring
  | simplePendulum
  deriving DecidableEq, Repr

/-- The two mathematical labels printed in the image. -/
inductive FigureLabel where
  | springConstant_k
  | equilibriumExtension_h
  deriving DecidableEq, Repr

/-- The physical role of a printed figure label. -/
inductive FigureQuantityRole where
  | springStiffness
  | equilibriumExtensionBetweenUnloadedAndLoadedPositions
  deriving DecidableEq, Repr

/-- Qualitative evidence visible directly in the supplied three-panel image. -/
structure SpringPendulumFigure where
  showsPanel : FigurePanel → Bool
  springShown : FigurePanel → Bool
  springTopFixedToSupport : FigurePanel → Bool
  blockShown : FigurePanel → Bool
  sameSpringInFirstTwoPanels : Bool
  pendulumFixedPivotShown : Bool
  pendulumStringShown : Bool
  pendulumBobShown : Bool
  labelShown : FigureLabel → Bool
  labelRole : FigureLabel → FigureQuantityRole
  extensionMarkerRunsFromUnloadedEndToLoadedPosition : Bool

/--
Image readouts: the first two panels compare the same fixed spring before and
after attaching the block, `h` marks their endpoint separation, and the third
panel is a fixed-pivot string pendulum with a bob.
-/
def MatchesPrimaryFigure (figure : SpringPendulumFigure) : Prop :=
  (∀ panel, figure.showsPanel panel = true) ∧
    figure.springShown .unloadedSpring = true ∧
    figure.springShown .loadedSpring = true ∧
    figure.springTopFixedToSupport .unloadedSpring = true ∧
    figure.springTopFixedToSupport .loadedSpring = true ∧
    figure.blockShown .unloadedSpring = false ∧
    figure.blockShown .loadedSpring = true ∧
    figure.sameSpringInFirstTwoPanels = true ∧
    figure.pendulumFixedPivotShown = true ∧
    figure.pendulumStringShown = true ∧
    figure.pendulumBobShown = true ∧
    figure.labelShown .springConstant_k = true ∧
    figure.labelShown .equilibriumExtension_h = true ∧
    figure.labelRole .springConstant_k = .springStiffness ∧
    figure.labelRole .equilibriumExtension_h =
      .equilibriumExtensionBetweenUnloadedAndLoadedPositions ∧
    figure.extensionMarkerRunsFromUnloadedEndToLoadedPosition = true

/-! ## Apparatus, problem data, and approximation regimes -/

/-- Orientation of the block's oscillatory motion. -/
inductive MotionOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Linearization regime used for either oscillator. -/
inductive OscillationRegime where
  | smallVerticalAboutStaticEquilibrium
  | smallAngleAboutDownwardEquilibrium
  | finiteAmplitude
  deriving DecidableEq, Repr

/-- The ideal mechanical model requested for the pendulum. -/
inductive PendulumModel where
  | simplePointBobMasslessString
  | extendedPhysicalPendulum
  deriving DecidableEq, Repr

/--
All independent physical quantities used by the spring and pendulum models.

The pendulum length and both frequencies are unconstrained outputs here.  In
particular, neither the extension `h` nor its `2 cm` readout is assigned to the
pendulum length by this structure.
-/
structure SpringPendulumSetup where
  figure : SpringPendulumFigure
  blockMass : MassQuantity
  pendulumBobMass : MassQuantity
  springConstant_k : SpringStiffnessQuantity
  equilibriumExtension_h : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  initialDownwardPullFromEquilibrium : LengthQuantity
  blockVelocityAtRelease : VelocityQuantity
  springAngularFrequency : AngularFrequencyQuantity
  springFrequency : FrequencyQuantity
  pendulumLength : LengthQuantity
  pendulumAngularFrequency : AngularFrequencyQuantity
  pendulumFrequency : FrequencyQuantity
  blockMotionOrientation : MotionOrientation
  springOscillationRegime : OscillationRegime
  pendulumOscillationRegime : OscillationRegime
  pendulumModel : PendulumModel

/--
Numerical and qualitative data stated in the prose.  “A short distance” is
recorded as a positive pull in the small-vertical-oscillation regime; release
means zero initial velocity.  The standard small-angle regime is made explicit
for the simple-pendulum formula.  No requested pendulum length occurs here.
-/
structure MatchesProblemDescription (setup : SpringPendulumSetup) : Prop where
  extension_h_is_two_centimeters :
    lengthInCentimeters setup.equilibriumExtension_h = 2
  pull_is_nonzero :
    0 < lengthInMeters setup.initialDownwardPullFromEquilibrium
  released_from_rest :
    velocityInMetersPerSecond setup.blockVelocityAtRelease = 0
  block_motion_is_vertical : setup.blockMotionOrientation = .vertical
  spring_motion_is_small :
    setup.springOscillationRegime = .smallVerticalAboutStaticEquilibrium
  requested_pendulum_is_simple :
    setup.pendulumModel = .simplePointBobMasslessString
  pendulum_motion_is_small_angle :
    setup.pendulumOscillationRegime = .smallAngleAboutDownwardEquilibrium

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalParameters (setup : SpringPendulumSetup) : Prop where
  blockMassPositive : 0 < massInKilograms setup.blockMass
  pendulumBobMassPositive : 0 < massInKilograms setup.pendulumBobMass
  springStiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springConstant_k
  equilibriumExtensionPositive :
    0 < lengthInMeters setup.equilibriumExtension_h
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  pendulumLengthPositive : 0 < lengthInMeters setup.pendulumLength
  springAngularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.springAngularFrequency
  pendulumAngularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.pendulumAngularFrequency
  springFrequencyPositive : 0 < frequencyInHertz setup.springFrequency
  pendulumFrequencyPositive : 0 < frequencyInHertz setup.pendulumFrequency

/-! ## Governing spring and simple-pendulum laws -/

/--
The loaded spring viewed in coherent SI readouts as Physlib's classical
harmonic oscillator, whose angular frequency is `sqrt (k / m)`.
-/
def springOscillatorSI
    (setup : SpringPendulumSetup)
    (hPhysical : HasPhysicalParameters setup) :
    ClassicalMechanics.HarmonicOscillator where
  m := massInKilograms setup.blockMass
  k := springStiffnessInNewtonsPerMeter setup.springConstant_k
  m_pos := hPhysical.blockMassPositive
  k_pos := hPhysical.springStiffnessPositive

/--
The small-angle simple pendulum viewed as a generalized harmonic oscillator.
For angular displacement, generalized inertia is `m L²` and the gravitational
restoring coefficient is `m g L`, so their ratio is `g / L`.
-/
def pendulumOscillatorSI
    (setup : SpringPendulumSetup)
    (hPhysical : HasPhysicalParameters setup) :
    ClassicalMechanics.HarmonicOscillator where
  m := massInKilograms setup.pendulumBobMass *
    lengthInMeters setup.pendulumLength ^ 2
  k := massInKilograms setup.pendulumBobMass *
    accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude *
    lengthInMeters setup.pendulumLength
  m_pos := mul_pos hPhysical.pendulumBobMassPositive
    (pow_pos hPhysical.pendulumLengthPositive 2)
  k_pos := mul_pos
    (mul_pos hPhysical.pendulumBobMassPositive
      hPhysical.gravitationalAccelerationPositive)
    hPhysical.pendulumLengthPositive

/--
Static balance and the two general small-oscillation laws.

The static law is `k h = m g`.  Physlib supplies `ω = sqrt (k / m)` for the
spring and for the generalized pendulum oscillator, and the last two fields
state `ω = 2πf`.  None of these fields gives a numerical pendulum length or
asserts that the pendulum length equals `h`.
-/
structure SatisfiesSpringAndPendulumLaws
    (setup : SpringPendulumSetup)
    (hPhysical : HasPhysicalParameters setup) : Prop where
  staticWeightBalance :
    springStiffnessInNewtonsPerMeter setup.springConstant_k *
        lengthInMeters setup.equilibriumExtension_h =
      massInKilograms setup.blockMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude
  springHarmonicFrequencyLaw :
    angularFrequencyInRadiansPerSecond setup.springAngularFrequency =
      (springOscillatorSI setup hPhysical).ω
  pendulumSmallAngleFrequencyLaw :
    angularFrequencyInRadiansPerSecond setup.pendulumAngularFrequency =
      (pendulumOscillatorSI setup hPhysical).ω
  springAngularToCyclicFrequency :
    angularFrequencyInRadiansPerSecond setup.springAngularFrequency =
      2 * Real.pi * frequencyInHertz setup.springFrequency
  pendulumAngularToCyclicFrequency :
    angularFrequencyInRadiansPerSecond setup.pendulumAngularFrequency =
      2 * Real.pi * frequencyInHertz setup.pendulumFrequency

/--
The design condition posed by the question: the simple pendulum swings with
the same cyclic frequency as the spring--block oscillator.  This constrains a
frequency, not the requested length.
-/
def PendulumMatchesSpringFrequency (setup : SpringPendulumSetup) : Prop :=
  frequencyInHertz setup.pendulumFrequency =
    frequencyInHertz setup.springFrequency

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answer choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Pendulum length in centimetres printed beside an answer label. -/
def AnswerChoice.lengthInCentimeters : AnswerChoice → ℝ
  | .A => 8 / 5
  | .B => 9 / 5
  | .C => 11 / 5
  | .D => 2

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A displayed choice reports the physical pendulum length exactly. -/
def MatchesAnswerChoice
    (setup : SpringPendulumSetup) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters setup.pendulumLength = choice.lengthInCentimeters

/--
Any positive simple pendulum satisfying the stated laws and frequency-match
condition has physical length equal to the spring's equilibrium extension.

This is an intermediate conclusion, not an assumption.
-/
lemma matchingFrequency_pendulumLength_eq_equilibriumExtension
    (setup : SpringPendulumSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesSpringAndPendulumLaws setup hPhysical)
    (hFrequencyMatch : PendulumMatchesSpringFrequency setup) :
    setup.pendulumLength = setup.equilibriumExtension_h := by
  have hAngular :
      angularFrequencyInRadiansPerSecond setup.springAngularFrequency =
        angularFrequencyInRadiansPerSecond setup.pendulumAngularFrequency := by
    calc
      _ = 2 * Real.pi * frequencyInHertz setup.springFrequency :=
        hLaws.springAngularToCyclicFrequency
      _ = 2 * Real.pi * frequencyInHertz setup.pendulumFrequency := by
        rw [← hFrequencyMatch]
      _ = _ := hLaws.pendulumAngularToCyclicFrequency.symm
  have hOmega :
      (springOscillatorSI setup hPhysical).ω =
        (pendulumOscillatorSI setup hPhysical).ω := by
    calc
      _ = angularFrequencyInRadiansPerSecond setup.springAngularFrequency :=
        hLaws.springHarmonicFrequencyLaw.symm
      _ = angularFrequencyInRadiansPerSecond setup.pendulumAngularFrequency :=
        hAngular
      _ = _ := hLaws.pendulumSmallAngleFrequencyLaw
  have hRatio :
      (springOscillatorSI setup hPhysical).k /
          (springOscillatorSI setup hPhysical).m =
        (pendulumOscillatorSI setup hPhysical).k /
          (pendulumOscillatorSI setup hPhysical).m := by
    rw [← (springOscillatorSI setup hPhysical).ω_sq,
      ← (pendulumOscillatorSI setup hPhysical).ω_sq, hOmega]
  change
    springStiffnessInNewtonsPerMeter setup.springConstant_k /
        massInKilograms setup.blockMass =
      (massInKilograms setup.pendulumBobMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.pendulumLength) /
        (massInKilograms setup.pendulumBobMass *
          lengthInMeters setup.pendulumLength ^ 2) at hRatio
  have hFrequencyRatio :
      springStiffnessInNewtonsPerMeter setup.springConstant_k /
          massInKilograms setup.blockMass =
        accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude /
          lengthInMeters setup.pendulumLength := by
    calc
      _ = _ := hRatio
      _ = _ := by
        field_simp [hPhysical.pendulumBobMassPositive.ne',
          hPhysical.pendulumLengthPositive.ne']
  have hCross := (div_eq_div_iff hPhysical.blockMassPositive.ne'
    hPhysical.pendulumLengthPositive.ne').mp hFrequencyRatio
  have hMeters :
      lengthInMeters setup.pendulumLength =
        lengthInMeters setup.equilibriumExtension_h := by
    apply mul_left_cancel₀ hPhysical.springStiffnessPositive.ne'
    calc
      springStiffnessInNewtonsPerMeter setup.springConstant_k *
          lengthInMeters setup.pendulumLength =
        accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          massInKilograms setup.blockMass := hCross
      _ = massInKilograms setup.blockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude :=
        mul_comm _ _
      _ = springStiffnessInNewtonsPerMeter setup.springConstant_k *
          lengthInMeters setup.equilibriumExtension_h :=
        hLaws.staticWeightBalance.symm
  let meterUnits : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.meters }
  have hAtMeters :
      setup.pendulumLength meterUnits =
        setup.equilibriumExtension_h meterUnits := by
    apply WithDim.ext
    apply NNReal.coe_injective
    simpa only [lengthInMeters, lengthReadout, meterUnits] using hMeters
  apply Dimensionful.ext
  funext units
  rw [setup.pendulumLength.2 meterUnits units,
    setup.equilibriumExtension_h.2 meterUnits units, hAtMeters]

/--
The frequency-matched simple pendulum has length `h = 2.0 cm`, so it agrees
with recorded answer `D`.

This formalizes blueprint label `thm:physics:phyx_mini_0281:target`.
-/
theorem problem_phyx_mini_0281
    (setup : SpringPendulumSetup)
    (hFigure : MatchesPrimaryFigure setup.figure)
    (hProblem : MatchesProblemDescription setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesSpringAndPendulumLaws setup hPhysical)
    (hFrequencyMatch : PendulumMatchesSpringFrequency setup) :
    setup.pendulumLength = setup.equilibriumExtension_h ∧
      lengthInCentimeters setup.pendulumLength = 2 ∧
      MatchesAnswerChoice setup recordedAnswerChoice := by
  have hLength :=
    matchingFrequency_pendulumLength_eq_equilibriumExtension
      setup hPhysical hLaws hFrequencyMatch
  refine ⟨hLength, ?_, ?_⟩
  · rw [hLength]
    exact hProblem.extension_h_is_two_centimeters
  · change lengthInCentimeters setup.pendulumLength = 2
    rw [hLength]
    exact hProblem.extension_h_is_two_centimeters

end PhyXMiniProblems.ProblemPhyXMini0281
