import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0704

open Dimension

/-!
# Startup time of a small-airplane propeller

The engine applies a `60 N m` torque to a propeller whose primary figure labels
its total tip-to-tip length as `2.0 m` and its mass as `40 kg`.  The rotation
axis passes through the central hub.  The propeller is idealized as a uniform
slender rod about its midpoint, starts from rest, and is driven by a constant
torque without an opposing torque until it reaches `200 rpm`.

Physical magnitudes are represented by Physlib `Dimensionful` quantities.
Real numbers below are coherent SI readouts, dimensionless angular readouts,
figure-label values, or the numerical values printed in the answer choices.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative torque magnitude, with dimension `M L² T⁻²`. -/
abbrev TorqueMagnitudeQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A moment of inertia about the displayed axis, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative angular speed; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative angular acceleration; radians are dimensionless. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of the total tip-to-tip propeller length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Kilogram readout of the propeller mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  nonnegativeSIReadout duration

/-- Newton-metre readout of a torque magnitude. -/
def torqueInNewtonMeters (torque : TorqueMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout torque

/-- Kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Radian-per-second readout of an angular speed. -/
def angularSpeedInRadiansPerSecond (speed : AngularSpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Radian-per-second-squared readout of an angular acceleration. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Revolutions-per-minute readout, using one revolution as `2 * π` radians. -/
def angularSpeedInRevolutionsPerMinute (speed : AngularSpeedQuantity) : ℝ :=
  60 * angularSpeedInRadiansPerSecond speed / (2 * Real.pi)

/-! ## Primary-figure vocabulary and readout -/

/-- Objects and graphical annotations visibly present in the supplied image. -/
inductive FigureObject where
  | propeller
  | centralHub
  | axisLeader
  | engineTorqueLeader
  | rotationDirectionArrow
  | tipToTipLengthArrow
  deriving DecidableEq, Repr

/-- Text labels printed in the supplied image. -/
inductive FigureTextLabel where
  | axis
  | engineTorqueDescription
  | massM
  | lengthL
  deriving DecidableEq, Repr

/-- Distinguished locations in the supplied propeller drawing. -/
inductive FigurePoint where
  | upperBladeTip
  | centralHub
  | lowerBladeTip
  deriving DecidableEq, Repr

/-- Scalar labels and incidence information read directly from the image. -/
structure PropellerFigureReadout where
  objectShown : FigureObject → Prop
  textLabelShown : FigureTextLabel → Prop
  lengthLabelMeters : ℝ
  massLabelKilograms : ℝ
  lengthArrowStart : FigurePoint
  lengthArrowEnd : FigurePoint
  axisLeaderEndpoint : FigurePoint
  engineTorqueLeaderEndpoint : FigurePoint

/-! ## Physical setup and modeling choices -/

/-- Placement of the fixed rotation axis relative to the propeller. -/
inductive RotationAxisPlacement where
  | throughCentralHubAndMidpoint
  | other
  deriving DecidableEq, Repr

/-- Mass-distribution idealization used to compute the axial inertia. -/
inductive PropellerMassModel where
  | uniformSlenderRod
  | other
  deriving DecidableEq, Repr

/-- Torque regime during the modeled startup interval. -/
inductive StartupTorqueRegime where
  | constantEngineTorqueNoOpposingTorque
  | other
  deriving DecidableEq, Repr

/-- The physical quantities and figure attached to the startup experiment. -/
structure PropellerStartupSetup where
  propellerMass : MassQuantity
  propellerLength : LengthQuantity
  engineTorque : TorqueMagnitudeQuantity
  momentOfInertiaAboutAxis : MomentOfInertiaQuantity
  initialAngularSpeed : AngularSpeedQuantity
  targetAngularSpeed : AngularSpeedQuantity
  angularAcceleration : AngularAccelerationQuantity
  startupDuration : TimeQuantity
  rotationAxisPlacement : RotationAxisPlacement
  massModel : PropellerMassModel
  torqueRegime : StartupTorqueRegime
  figure : PropellerFigureReadout

/-- The values stated in the text for the driving torque and target speed. -/
structure MatchesProblemData (setup : PropellerStartupSetup) : Prop where
  engineTorqueIsSixtyNewtonMeters :
    torqueInNewtonMeters setup.engineTorque = 60
  targetSpeedIsTwoHundredRpm :
    angularSpeedInRevolutionsPerMinute setup.targetAngularSpeed = 200

/-- The labels and geometry read from the supplied image, including the
coherence of its scalar labels with the dimensionful setup quantities. -/
structure MatchesSourceFigure (setup : PropellerStartupSetup) : Prop where
  propellerShown : setup.figure.objectShown .propeller
  centralHubShown : setup.figure.objectShown .centralHub
  axisLeaderShown : setup.figure.objectShown .axisLeader
  engineTorqueLeaderShown : setup.figure.objectShown .engineTorqueLeader
  rotationDirectionShown : setup.figure.objectShown .rotationDirectionArrow
  tipToTipLengthArrowShown : setup.figure.objectShown .tipToTipLengthArrow
  axisLabelShown : setup.figure.textLabelShown .axis
  engineTorqueDescriptionShown :
    setup.figure.textLabelShown .engineTorqueDescription
  massLabelShown : setup.figure.textLabelShown .massM
  lengthLabelShown : setup.figure.textLabelShown .lengthL
  lengthArrowStartsAtUpperTip :
    setup.figure.lengthArrowStart = .upperBladeTip
  lengthArrowEndsAtLowerTip :
    setup.figure.lengthArrowEnd = .lowerBladeTip
  axisLeaderPointsToHub :
    setup.figure.axisLeaderEndpoint = .centralHub
  engineTorqueLeaderPointsToHub :
    setup.figure.engineTorqueLeaderEndpoint = .centralHub
  figureLengthIsTwoMeters : setup.figure.lengthLabelMeters = 2
  figureMassIsFortyKilograms : setup.figure.massLabelKilograms = 40
  figureLengthMatchesSetup :
    lengthInMeters setup.propellerLength = setup.figure.lengthLabelMeters
  figureMassMatchesSetup :
    massInKilograms setup.propellerMass = setup.figure.massLabelKilograms

/-- Governing fixed-axis dynamics and the uniform-rod idealization.

The final startup duration is deliberately absent.  The last field is the
constant-angular-acceleration kinematic law relating the still-unknown duration
to the initial and target angular speeds. -/
structure ValidPropellerStartupPhysics (setup : PropellerStartupSetup) : Prop where
  axisThroughMidpoint :
    setup.rotationAxisPlacement = .throughCentralHubAndMidpoint
  uniformRodModel : setup.massModel = .uniformSlenderRod
  constantUnopposedEngineTorque :
    setup.torqueRegime = .constantEngineTorqueNoOpposingTorque
  uniformRodMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAxis =
      massInKilograms setup.propellerMass *
        (lengthInMeters setup.propellerLength) ^ 2 / 12
  rotationalSecondLaw :
    torqueInNewtonMeters setup.engineTorque =
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAxis *
        angularAccelerationInRadiansPerSecondSquared
          setup.angularAcceleration
  startsFromRest :
    angularSpeedInRadiansPerSecond setup.initialAngularSpeed = 0
  constantAngularAccelerationKinematics :
    angularSpeedInRadiansPerSecond setup.targetAngularSpeed =
      angularSpeedInRadiansPerSecond setup.initialAngularSpeed +
        angularAccelerationInRadiansPerSecondSquared
            setup.angularAcceleration *
          timeInSeconds setup.startupDuration

/-! ## Displayed answer choices and target -/

/-- Letter labels used by the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The duration in seconds printed beside each answer-choice letter. -/
def AnswerChoice.durationSeconds : AnswerChoice → ℝ
  | .A => 5
  | .B => 24 / 5
  | .C => 23 / 5
  | .D => 22 / 5

/-- Under the stated data, primary-figure readouts, uniform-rod inertia law,
fixed-axis torque law, and constant-acceleration kinematics, the startup lasts
exactly `40π/27` seconds.  Option C (`4.6 s`) is the uniquely closest displayed
answer and is within one tenth of a second of that exact value.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0704:target`. -/
theorem propeller_startup_duration_and_answer_choice
    (setup : PropellerStartupSetup)
    (hData : MatchesProblemData setup)
    (hFigure : MatchesSourceFigure setup)
    (hPhysics : ValidPropellerStartupPhysics setup) :
    timeInSeconds setup.startupDuration = 40 * Real.pi / 27 ∧
      abs (timeInSeconds setup.startupDuration -
          AnswerChoice.durationSeconds .C) < 1 / 10 ∧
      ∀ choice, choice ≠ .C →
        abs (timeInSeconds setup.startupDuration -
            AnswerChoice.durationSeconds .C) <
          abs (timeInSeconds setup.startupDuration -
            AnswerChoice.durationSeconds choice) := by
  have hMass :
      massInKilograms setup.propellerMass = 40 :=
    hFigure.figureMassMatchesSetup.trans hFigure.figureMassIsFortyKilograms
  have hLength :
      lengthInMeters setup.propellerLength = 2 :=
    hFigure.figureLengthMatchesSetup.trans hFigure.figureLengthIsTwoMeters
  have hInertia := hPhysics.uniformRodMomentOfInertia
  rw [hMass, hLength] at hInertia
  norm_num at hInertia
  have hAcceleration := hPhysics.rotationalSecondLaw
  rw [hData.engineTorqueIsSixtyNewtonMeters, hInertia] at hAcceleration
  have hAccelerationValue :
      angularAccelerationInRadiansPerSecondSquared
          setup.angularAcceleration = 9 / 2 := by
    nlinarith
  have hTargetSpeed := hData.targetSpeedIsTwoHundredRpm
  unfold angularSpeedInRevolutionsPerMinute at hTargetSpeed
  field_simp [Real.pi_ne_zero] at hTargetSpeed
  have hTargetSpeedValue :
      angularSpeedInRadiansPerSecond setup.targetAngularSpeed =
        20 * Real.pi / 3 := by
    linarith
  have hKinematics := hPhysics.constantAngularAccelerationKinematics
  rw [hTargetSpeedValue, hPhysics.startsFromRest, hAccelerationValue] at hKinematics
  have hDuration :
      timeInSeconds setup.startupDuration = 40 * Real.pi / 27 := by
    linarith
  have hPiLower : (621 : ℝ) / 200 < Real.pi := by
    have hSinBound :=
      Real.sin_bound (x := (621 : ℝ) / 1600) (by norm_num)
    have hSinUpper := (abs_le.mp hSinBound).2
    norm_num [abs_of_nonneg] at hSinUpper
    have hCosBound :=
      Real.cos_bound (x := (621 : ℝ) / 1600) (by norm_num)
    have hCosUpper := (abs_le.mp hCosBound).2
    norm_num [abs_of_nonneg] at hCosUpper
    have hSinPos : 0 < Real.sin ((621 : ℝ) / 1600) :=
      Real.sin_pos_of_pos_of_le_one (by norm_num) (by norm_num)
    have hCosPos : 0 < Real.cos ((621 : ℝ) / 1600) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hSinLt : Real.sin ((621 : ℝ) / 1600) < 381 / 1000 := by
      nlinarith
    have hCosLt : Real.cos ((621 : ℝ) / 1600) < 927 / 1000 := by
      nlinarith
    have hSinDoubleLt : Real.sin ((621 : ℝ) / 800) < 707 / 1000 := by
      rw [show (621 : ℝ) / 800 = 2 * (621 / 1600) by ring,
        Real.sin_two_mul]
      calc
        2 * Real.sin (621 / 1600) * Real.cos (621 / 1600) <
            2 * Real.sin (621 / 1600) * (927 / 1000) := by
              gcongr
        _ < 2 * (381 / 1000) * (927 / 1000) := by
              gcongr
        _ < 707 / 1000 := by norm_num
    have hSinDoublePos : 0 < Real.sin ((621 : ℝ) / 800) :=
      Real.sin_pos_of_pos_of_le_one (by norm_num) (by norm_num)
    have hSinDoubleSq :
        (Real.sin ((621 : ℝ) / 800)) ^ 2 < 1 / 2 := by
      nlinarith
    have hCosPos' : 0 < Real.cos ((621 : ℝ) / 400) := by
      rw [show (621 : ℝ) / 400 = 2 * (621 / 800) by ring,
        Real.cos_two_mul_eq_one_sub]
      nlinarith
    have hHalf : (621 : ℝ) / 400 < Real.pi / 2 := by
      by_contra h
      have hNonpos : Real.cos ((621 : ℝ) / 400) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le
          (le_of_not_gt h) (by nlinarith [Real.two_le_pi])
      linarith
    linarith
  have hPiUpper : Real.pi < (1269 : ℝ) / 400 := by
    have hCosBound :=
      Real.cos_bound (x := (1269 : ℝ) / 1600) (by norm_num)
    have hCosUpper := (abs_le.mp hCosBound).2
    norm_num [abs_of_nonneg] at hCosUpper
    have hCosPos : 0 < Real.cos ((1269 : ℝ) / 1600) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hCosLt : Real.cos ((1269 : ℝ) / 1600) < 707 / 1000 := by
      nlinarith
    have hCosSq :
        (Real.cos ((1269 : ℝ) / 1600)) ^ 2 < 1 / 2 := by
      nlinarith
    have hCosNeg : Real.cos ((1269 : ℝ) / 800) < 0 := by
      rw [show (1269 : ℝ) / 800 = 2 * (1269 / 1600) by ring,
        Real.cos_two_mul]
      nlinarith
    have hHalf : Real.pi / 2 < (1269 : ℝ) / 800 := by
      by_contra h
      have hNonneg : 0 ≤ Real.cos ((1269 : ℝ) / 800) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by nlinarith [Real.pi_pos]) (le_of_not_gt h)
      linarith
    linarith
  refine ⟨hDuration, ?_, ?_⟩
  · rw [hDuration]
    rw [abs_lt]
    constructor <;> norm_num [AnswerChoice.durationSeconds] <;> nlinarith
  · intro choice hChoice
    rw [hDuration]
    cases choice
    · norm_num [AnswerChoice.durationSeconds]
      rw [abs_of_nonneg (by nlinarith), abs_of_neg (by nlinarith)]
      nlinarith
    · norm_num [AnswerChoice.durationSeconds]
      rw [abs_of_nonneg (by nlinarith), abs_of_neg (by nlinarith)]
      nlinarith
    · contradiction
    · norm_num [AnswerChoice.durationSeconds]
      rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0704
