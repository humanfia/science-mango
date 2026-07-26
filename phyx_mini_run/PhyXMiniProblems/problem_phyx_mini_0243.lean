import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0243

open Dimension

/-!
# Angle swept while a transverse wave crosses a rotating cord

A block labelled `M` moves in a circle on a frictionless horizontal table.
One end of a uniform cord is fixed at the center of the circle and the other
is attached to the block.  The cord length is therefore the orbit radius.

The recorded numerical answer uses the standard light-cord tension model:
the block supplies the centripetal-force relation `T = M * omega^2 * R`, and
the small but nonzero cord mass is used to determine the linear density
`mu = m / R`.  Thus the tension is treated as uniform when applying the
transverse-wave law.  All dimensional quantities below are represented by
Physlib's unit-independent `Dimensionful` type.  Real numbers occur only as
explicit SI readouts, dimensionless ratios, or unwrapped radian readouts.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative angular speed; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative force, used for the tension in the cord. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative mass per unit length of cord. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A nonnegative propagation speed along the cord. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- Kilogram readout of a mass in coherent SI units. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Meter readout of a length in coherent SI units. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Second readout of a duration in coherent SI units. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of an angular speed. -/
def angularSpeedInRadiansPerSecond (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Newton readout of a cord tension. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  ((tension UnitChoices.SI).val : ℝ)

/-- Kilogram-per-meter readout of a linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Meter-per-second readout of a wave speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Primary-figure labels and experimental quantities -/

/-- The two physically distinct ends of the cord. -/
inductive CordEnd where
  | centerEnd
  | blockEnd
  deriving DecidableEq, Repr

/-- Object labels visible or implied in the primary figure. -/
inductive FigureObject where
  | fixedCenter
  | blockM
  deriving DecidableEq, Repr

/-- The dashed trajectory drawn on the tabletop. -/
inductive OrbitShape where
  | circle
  deriving DecidableEq, Repr

/-- Orientation of the surface supporting the block. -/
inductive TableOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Contact model for the table surface. -/
inductive SurfaceCondition where
  | frictionless
  deriving DecidableEq, Repr

/-!
The independent physical quantities and figure-derived roles in the setup.

`angularDisplacementRadians duration` is an unwrapped scalar radian readout,
appropriate for the short time intervals in this problem.  It is not defined
to be the requested answer; its relation to the angular speed is stated later
as a governing kinematic law.
-/
structure RotatingBlockCordExperiment where
  blockMass : MassQuantity
  cordMass : MassQuantity
  cordLength : LengthQuantity
  orbitRadius : LengthQuantity
  angularSpeed : AngularSpeedQuantity
  linearMassDensity : LinearMassDensityQuantity
  cordTension : TensionQuantity
  transverseWaveSpeed : SpeedQuantity
  waveTravelTime : TimeQuantity
  angularDisplacementRadians : TimeQuantity → ℝ
  cordEndAttachment : CordEnd → FigureObject
  orbitCenter : FigureObject
  orbitShape : OrbitShape
  tableOrientation : TableOrientation
  surfaceCondition : SurfaceCondition

/-- The angle swept by the block during the center-to-block wave transit. -/
def angleDuringWaveTravelRadians
    (experiment : RotatingBlockCordExperiment) : ℝ :=
  experiment.angularDisplacementRadians experiment.waveTravelTime

/-!
Numerical data and geometry stated by the problem or read from the primary
figure.  The source's `0.003,20 kg` typography is normalized to `0.00320 kg`.
-/
structure MatchesProblemAndPrimaryFigure
    (experiment : RotatingBlockCordExperiment) : Prop where
  blockMassKilograms :
    massInKilograms experiment.blockMass = (450 : ℝ) / 1000
  cordMassKilograms :
    massInKilograms experiment.cordMass = (320 : ℝ) / 100000
  fixedEndAtCenter :
    experiment.cordEndAttachment .centerEnd = .fixedCenter
  otherEndAtBlock :
    experiment.cordEndAttachment .blockEnd = .blockM
  orbitCenteredAtFixedPoint : experiment.orbitCenter = .fixedCenter
  circularOrbit : experiment.orbitShape = .circle
  cordSetsOrbitRadius : experiment.orbitRadius = experiment.cordLength
  horizontalTable : experiment.tableOrientation = .horizontal
  frictionlessTable : experiment.surfaceCondition = .frictionless

/-- Positivity and nondegeneracy conditions for the physical setup. -/
structure HasPhysicalParameters
    (experiment : RotatingBlockCordExperiment) : Prop where
  blockMassPositive : 0 < massInKilograms experiment.blockMass
  cordMassPositive : 0 < massInKilograms experiment.cordMass
  cordLengthPositive : 0 < lengthInMeters experiment.cordLength
  angularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond experiment.angularSpeed
  linearMassDensityPositive :
    0 < linearMassDensityInKilogramsPerMeter experiment.linearMassDensity
  cordTensionPositive : 0 < tensionInNewtons experiment.cordTension
  transverseWaveSpeedPositive :
    0 < speedInMetersPerSecond experiment.transverseWaveSpeed
  waveTravelTimePositive : 0 < timeInSeconds experiment.waveTravelTime

/-!
The governing textbook laws used for this question:

* uniform linear density `mu = m / R`;
* the light-cord, uniform-tension centripetal relation `T = M * omega^2 * R`;
* transverse wave speed `v = sqrt (T / mu)`;
* center-to-block transit time `t = R / v`;
* constant-angular-speed kinematics `theta = omega * t`.

These laws relate independently stored physical quantities.  In particular,
they do not contain either `sqrt (m / M)` or the displayed answer `0.0843`.
-/
structure SatisfiesRotatingCordWaveLaws
    (experiment : RotatingBlockCordExperiment) : Prop where
  uniformLinearDensity :
    linearMassDensityInKilogramsPerMeter experiment.linearMassDensity =
      massInKilograms experiment.cordMass /
        lengthInMeters experiment.cordLength
  lightCordUniformTension :
    tensionInNewtons experiment.cordTension =
      massInKilograms experiment.blockMass *
        angularSpeedInRadiansPerSecond experiment.angularSpeed ^ 2 *
          lengthInMeters experiment.orbitRadius
  transverseWaveLaw :
    speedInMetersPerSecond experiment.transverseWaveSpeed =
      Real.sqrt
        (tensionInNewtons experiment.cordTension /
          linearMassDensityInKilogramsPerMeter experiment.linearMassDensity)
  centerToBlockTravelTime :
    timeInSeconds experiment.waveTravelTime =
      lengthInMeters experiment.cordLength /
        speedInMetersPerSecond experiment.transverseWaveSpeed
  constantAngularSpeedKinematics :
    ∀ duration : TimeQuantity,
      experiment.angularDisplacementRadians duration =
        angularSpeedInRadiansPerSecond experiment.angularSpeed *
          timeInSeconds duration

/-!
The governing laws imply that the cord length and angular speed cancel, so
the swept angle is the square root of the cord-to-block mass ratio.  This is a
derived conclusion, not a law or data field.
-/
lemma angleDuringWaveTravel_massRatio
    (experiment : RotatingBlockCordExperiment)
    (_figure : MatchesProblemAndPrimaryFigure experiment)
    (_physical : HasPhysicalParameters experiment)
    (_laws : SatisfiesRotatingCordWaveLaws experiment) :
    angleDuringWaveTravelRadians experiment =
      Real.sqrt
        (massInKilograms experiment.cordMass /
          massInKilograms experiment.blockMass) := by
  let M : ℝ := massInKilograms experiment.blockMass
  let m : ℝ := massInKilograms experiment.cordMass
  let L : ℝ := lengthInMeters experiment.cordLength
  let ω : ℝ :=
    angularSpeedInRadiansPerSecond experiment.angularSpeed
  let μ : ℝ :=
    linearMassDensityInKilogramsPerMeter experiment.linearMassDensity
  let T : ℝ := tensionInNewtons experiment.cordTension
  let v : ℝ := speedInMetersPerSecond experiment.transverseWaveSpeed
  have hM : 0 < M := by
    simpa [M] using _physical.blockMassPositive
  have hm : 0 < m := by
    simpa [m] using _physical.cordMassPositive
  have hL : 0 < L := by
    simpa [L] using _physical.cordLengthPositive
  have hω : 0 < ω := by
    simpa [ω] using _physical.angularSpeedPositive
  have hμ : 0 < μ := by
    simpa [μ] using _physical.linearMassDensityPositive
  have hT : 0 < T := by
    simpa [T] using _physical.cordTensionPositive
  have hv : 0 < v := by
    simpa [v] using _physical.transverseWaveSpeedPositive
  have hR :
      lengthInMeters experiment.orbitRadius =
        lengthInMeters experiment.cordLength :=
    congrArg lengthInMeters _figure.cordSetsOrbitRadius
  have hμeq : μ = m / L := by
    simpa [μ, m, L] using _laws.uniformLinearDensity
  have hTeq : T = M * ω ^ 2 * L := by
    simpa [T, M, ω, L, hR] using _laws.lightCordUniformTension
  have hveq : v = Real.sqrt (T / μ) := by
    simpa [v, T, μ] using _laws.transverseWaveLaw
  have hθ :
      angleDuringWaveTravelRadians experiment = ω * (L / v) := by
    rw [angleDuringWaveTravelRadians,
      _laws.constantAngularSpeedKinematics,
      _laws.centerToBlockTravelTime]
  have hradicand : 0 ≤ T / μ := (div_pos hT hμ).le
  have hvsq : v ^ 2 = T / μ := by
    rw [hveq, Real.sq_sqrt hradicand]
  rw [hμeq, hTeq] at hvsq
  have hanglesq : (ω * (L / v)) ^ 2 = m / M := by
    field_simp [ne_of_gt hM, ne_of_gt hm, ne_of_gt hL, ne_of_gt hv] at hvsq ⊢
    nlinarith [hvsq]
  have hratio : 0 ≤ m / M := (div_pos hm hM).le
  have hsqrtsq : (Real.sqrt (m / M)) ^ 2 = m / M :=
    Real.sq_sqrt hratio
  have hanglepos : 0 < ω * (L / v) :=
    mul_pos hω (div_pos hL hv)
  rw [hθ]
  change ω * (L / v) = Real.sqrt (m / M)
  nlinarith [hanglesq, hsqrtsq, Real.sqrt_nonneg (m / M)]

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate angles. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Unwrapped radian value printed beside each answer label. -/
def AnswerChoice.radians : AnswerChoice → ℝ
  | .A => 833 / 10000
  | .B => 863 / 10000
  | .C => 853 / 10000
  | .D => 843 / 10000

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a four-decimal-place displayed angle: the exact radian value
is within half a unit in the last displayed decimal place.
-/
def MatchesDisplayedAnswer (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |angleRadians - choice.radians| ≤ 1 / 20000

/-!
For the stated masses, the angle is `sqrt (0.00320 / 0.450)` radians and
agrees, to the displayed precision, with `0.0843 rad`, recorded answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0243:target`.
-/
theorem angleDuringWaveTravel_matches_recordedAnswerD
    (experiment : RotatingBlockCordExperiment)
    (_figure : MatchesProblemAndPrimaryFigure experiment)
    (_physical : HasPhysicalParameters experiment)
    (_laws : SatisfiesRotatingCordWaveLaws experiment) :
    angleDuringWaveTravelRadians experiment =
        Real.sqrt
          (((320 : ℝ) / 100000) / ((450 : ℝ) / 1000)) ∧
      MatchesDisplayedAnswer
        (angleDuringWaveTravelRadians experiment) recordedAnswerChoice := by
  have hangle :
      angleDuringWaveTravelRadians experiment =
        Real.sqrt
          (((320 : ℝ) / 100000) / ((450 : ℝ) / 1000)) := by
    calc
      angleDuringWaveTravelRadians experiment =
          Real.sqrt
            (massInKilograms experiment.cordMass /
              massInKilograms experiment.blockMass) :=
        angleDuringWaveTravel_massRatio experiment _figure _physical _laws
      _ = Real.sqrt
            (((320 : ℝ) / 100000) / ((450 : ℝ) / 1000)) := by
        rw [_figure.cordMassKilograms, _figure.blockMassKilograms]
  constructor
  · exact hangle
  · rw [hangle]
    change
      |Real.sqrt
          (((320 : ℝ) / 100000) / ((450 : ℝ) / 1000)) -
            843 / 10000| ≤
        1 / 20000
    let x : ℝ :=
      Real.sqrt
        (((320 : ℝ) / 100000) / ((450 : ℝ) / 1000))
    have hradicand :
        0 ≤ (((320 : ℝ) / 100000) / ((450 : ℝ) / 1000)) := by
      norm_num
    have hsquare : x ^ 2 = (8 : ℝ) / 1125 := by
      dsimp [x]
      rw [Real.sq_sqrt hradicand]
      norm_num
    have hnonnegative : 0 ≤ x := by
      dsimp [x]
      exact Real.sqrt_nonneg _
    change |x - 843 / 10000| ≤ 1 / 20000
    rw [abs_le]
    constructor <;> norm_num at hsquare ⊢ <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0243
