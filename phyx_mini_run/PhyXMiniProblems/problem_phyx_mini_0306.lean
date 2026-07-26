import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0306

open Dimension

/-!
# Transverse-wave speed on a spinning circular string loop

A circular loop of string of radius `4.00 cm` rotates clockwise with tangential
speed `5.00 cm/s` in negligible gravity.  Plucking the string launches a
transverse wave.  The local radial force balance of the rotating loop gives
`T = μ v²`, while the transverse-string wave law gives `T = μ c²`; positivity
therefore selects `c = v`.

The physical quantities below use Physlib's unit-independent `Dimensionful`
wrapper.  Real scalars occur only as readouts in explicitly selected units and
as the dimensionless numerical data printed by the problem.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- Mass per unit length of the uniform string. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A nonnegative physical acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A tensile or resultant force, with dimension `mass * length / time²`. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass { UnitChoices.SI with mass := unit }).val : ℝ)

/-- Read a linear mass density in selected mass and length units. -/
def linearMassDensityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : LinearMassDensityQuantity) : ℝ :=
  ((density { UnitChoices.SI with
    mass := massUnit, length := lengthUnit }).val : ℝ)

/-- Read an acceleration in selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration { UnitChoices.SI with
    length := lengthUnit, time := timeUnit }).val : ℝ)

/-- Read tension in the force unit induced by selected base units. -/
def tensionReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (tension : TensionQuantity) : ℝ :=
  ((tension { UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit }).val : ℝ)

/-- Read a speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed { UnitChoices.SI with
    length := lengthUnit, time := timeUnit }).val : ℝ)

/-- Centimeter readout used for the stated radius. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Centimeters-per-second readout used for the given and requested speeds. -/
def speedInCentimetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.centimeters TimeUnit.seconds speed

/-! ## Scenario and primary-figure labels -/

/-- Sense of rotation in the plane of the supplied figure. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Location of the rotation axis relative to the loop. -/
inductive RotationAxisLocation where
  | centerOfLoop
  | other
  deriving DecidableEq, Repr

/-- Whether gravity contributes appreciably to the string tension. -/
inductive GravityRegime where
  | negligible
  | appreciable
  deriving DecidableEq, Repr

/-- How the string is excited in the scenario. -/
inductive StringExcitation where
  | plucked
  | other
  deriving DecidableEq, Repr

/-- The kind of disturbance whose propagation speed is requested. -/
inductive WaveMotionKind where
  | transverse
  | longitudinal
  | other
  deriving DecidableEq, Repr

/-!
The primary image contains one unlabelled circular outline and a curved
clockwise arrow.  It does not visibly mark the center point; rotation about
the center comes from the prose rather than from an invented figure label.
-/
structure CircularLoopFigure where
  showsSingleCircularOutline : Bool
  showsCurvedRotationArrow : Bool
  showsMarkedCenterPoint : Bool
  arrowSense : RotationSense

/-!
Physical quantities of the ideal rotating loop.  `arcMassPerRadian` is the
mass of an infinitesimal arc divided by its dimensionless central angle.
`inwardTensionResultantPerRadian` is the corresponding limiting inward force
from the endpoint tensions.  Keeping these quantities explicit separates the
local circular dynamics from the target wave speed.
-/
structure RotatingCircularStringSetup where
  loopRadius : LengthQuantity
  linearMassDensity : LinearMassDensityQuantity
  tangentialSpeed : SpeedQuantity
  stringTension : TensionQuantity
  arcMassPerRadian : MassQuantity
  centripetalAcceleration : AccelerationQuantity
  inwardTensionResultantPerRadian : TensionQuantity
  transverseWaveSpeed : SpeedQuantity
  rotationSense : RotationSense
  rotationAxis : RotationAxisLocation
  gravityRegime : GravityRegime
  excitation : StringExcitation
  waveMotionKind : WaveMotionKind
  figure : CircularLoopFigure

/-- Qualitative physical information stated in the prose. -/
def MatchesProblemScenario (setup : RotatingCircularStringSetup) : Prop :=
  setup.rotationAxis = .centerOfLoop ∧
    setup.gravityRegime = .negligible ∧
    setup.excitation = .plucked ∧
    setup.waveMotionKind = .transverse

/-!
Primary-image evidence: a single circular outline and a curved clockwise
arrow are visible, with no marked or text-labelled center.  This predicate
contains no wave-speed value.
-/
def MatchesSuppliedFigure (setup : RotatingCircularStringSetup) : Prop :=
  setup.figure.showsSingleCircularOutline = true ∧
    setup.figure.showsCurvedRotationArrow = true ∧
    setup.figure.showsMarkedCenterPoint = false ∧
    setup.figure.arrowSense = .clockwise ∧
    setup.rotationSense = setup.figure.arrowSense

/-- The two numerical readouts supplied by the problem statement. -/
structure MatchesProblemReadouts (setup : RotatingCircularStringSetup) : Prop where
  radiusCentimeters : lengthInCentimeters setup.loopRadius = 4
  tangentialSpeedCentimetersPerSecond :
    speedInCentimetersPerSecond setup.tangentialSpeed = 5

/-!
Strict positivity conditions needed for the nondegenerate circular motion and
for cancellation in the wave-speed comparison.  The remaining quantities are
already nonnegative because their underlying scalar type is `NNReal`.
-/
def HasPhysicalParameters (setup : RotatingCircularStringSetup) : Prop :=
  0 < lengthReadout LengthUnit.meters setup.loopRadius ∧
    0 < linearMassDensityReadout MassUnit.kilograms LengthUnit.meters
      setup.linearMassDensity ∧
    0 < speedReadout LengthUnit.meters TimeUnit.seconds
      setup.tangentialSpeed

/-! ## Governing circular-motion and transverse-wave laws -/

/-!
Local dynamics of a uniform string element in steady circular motion:

* arc mass per radian is `μ r`;
* centripetal acceleration is `v² / r`;
* the limiting inward resultant of the two endpoint tensions, per radian, is
  the tension magnitude `T`;
* Newton's second law equates that resultant with mass times acceleration.

These laws imply `T = μ v²`; they do not mention the requested wave speed.
-/
structure SatisfiesRotatingLoopDynamics
    (setup : RotatingCircularStringSetup) : Prop where
  arcMassPerRadianLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      massReadout massUnit setup.arcMassPerRadian =
        linearMassDensityReadout massUnit lengthUnit
            setup.linearMassDensity *
          lengthReadout lengthUnit setup.loopRadius
  centripetalAccelerationLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationReadout lengthUnit timeUnit
          setup.centripetalAcceleration =
        speedReadout lengthUnit timeUnit setup.tangentialSpeed ^ 2 /
          lengthReadout lengthUnit setup.loopRadius
  circularTensionGeometry :
    setup.inwardTensionResultantPerRadian = setup.stringTension
  newtonsSecondLawForArcPerRadian :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      tensionReadout massUnit lengthUnit timeUnit
          setup.inwardTensionResultantPerRadian =
        massReadout massUnit setup.arcMassPerRadian *
          accelerationReadout lengthUnit timeUnit
            setup.centripetalAcceleration

/-!
The standard constitutive law for transverse waves on an ideal uniform
string, `T = μ c²`, expressed in every compatible system of base units.  This
is a governing law, not the conclusion `c = v` and not a numerical answer.
-/
structure SatisfiesTransverseStringWaveLaw
    (setup : RotatingCircularStringSetup) : Prop where
  tensionEqualsLinearDensityTimesWaveSpeedSquared :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      tensionReadout massUnit lengthUnit timeUnit setup.stringTension =
        linearMassDensityReadout massUnit lengthUnit
            setup.linearMassDensity *
          speedReadout lengthUnit timeUnit setup.transverseWaveSpeed ^ 2

/-!
The rotating-loop laws imply the intermediate tension relation
`T = μ v²`.  It is derived rather than included as a premise.
-/
lemma tension_eq_linearDensity_mul_tangentialSpeed_sq
    (setup : RotatingCircularStringSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_dynamics : SatisfiesRotatingLoopDynamics setup) :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      tensionReadout massUnit lengthUnit timeUnit setup.stringTension =
        linearMassDensityReadout massUnit lengthUnit
            setup.linearMassDensity *
          speedReadout lengthUnit timeUnit setup.tangentialSpeed ^ 2 := by
  intro massUnit lengthUnit timeUnit
  have h_radius_pos :
      0 < lengthReadout lengthUnit setup.loopRadius := by
    have h_scale := setup.loopRadius.2
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
      ({UnitChoices.SI with length := lengthUnit} : UnitChoices)
    unfold lengthReadout at h_scale ⊢
    rw [h_scale]
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul]
    exact mul_pos
      (NNReal.coe_pos.mpr (UnitChoices.dimScale_pos _ _ _))
      h_physical.1
  calc
    tensionReadout massUnit lengthUnit timeUnit setup.stringTension =
        tensionReadout massUnit lengthUnit timeUnit
          setup.inwardTensionResultantPerRadian := by
      rw [h_dynamics.circularTensionGeometry]
    _ = massReadout massUnit setup.arcMassPerRadian *
          accelerationReadout lengthUnit timeUnit
            setup.centripetalAcceleration :=
      h_dynamics.newtonsSecondLawForArcPerRadian
        massUnit lengthUnit timeUnit
    _ = (linearMassDensityReadout massUnit lengthUnit
            setup.linearMassDensity *
          lengthReadout lengthUnit setup.loopRadius) *
        (speedReadout lengthUnit timeUnit setup.tangentialSpeed ^ 2 /
          lengthReadout lengthUnit setup.loopRadius) := by
      rw [h_dynamics.arcMassPerRadianLaw,
        h_dynamics.centripetalAccelerationLaw]
    _ = linearMassDensityReadout massUnit lengthUnit
          setup.linearMassDensity *
        speedReadout lengthUnit timeUnit setup.tangentialSpeed ^ 2 := by
      field_simp [ne_of_gt h_radius_pos]

/-! ## Displayed choices and formalization target -/

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Speed in centimeters per second printed beside each answer label. -/
def AnswerChoice.speedCentimetersPerSecond : AnswerChoice → ℝ
  | .A => 4.4
  | .B => 4.6
  | .C => 4.8
  | .D => 5.0

/-- Answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The circular-motion force balance and transverse-string wave law give equal
nonnegative squared speeds.  Hence the physical wave speed equals the loop's
tangential speed, whose supplied readout is `5.00 cm/s`, answer choice D.

This formalizes `thm:physics:phyx_mini_0306:target`.
-/
theorem problem_phyx_mini_0306
    (setup : RotatingCircularStringSetup)
    (h_scenario : MatchesProblemScenario setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_dynamics : SatisfiesRotatingLoopDynamics setup)
    (h_wave_law : SatisfiesTransverseStringWaveLaw setup) :
    setup.transverseWaveSpeed = setup.tangentialSpeed ∧
      speedInCentimetersPerSecond setup.transverseWaveSpeed =
        AnswerChoice.speedCentimetersPerSecond recordedDatasetAnswer := by
  clear h_scenario h_figure
  let baseUnits : UnitChoices :=
    {UnitChoices.SI with
      length := LengthUnit.meters, time := TimeUnit.seconds}
  have h_density_pos :
      0 < linearMassDensityReadout MassUnit.kilograms LengthUnit.meters
        setup.linearMassDensity :=
    h_physical.2.1
  have h_tangential_tension :=
    tension_eq_linearDensity_mul_tangentialSpeed_sq
      setup h_physical h_dynamics MassUnit.kilograms
        LengthUnit.meters TimeUnit.seconds
  have h_wave_tension :=
    h_wave_law.tensionEqualsLinearDensityTimesWaveSpeedSquared
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have h_speed_squares :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.transverseWaveSpeed ^ 2 =
        speedReadout LengthUnit.meters TimeUnit.seconds
          setup.tangentialSpeed ^ 2 := by
    apply mul_left_cancel₀ (ne_of_gt h_density_pos)
    exact h_wave_tension.symm.trans h_tangential_tension
  have h_wave_speed_nonneg :
      0 ≤ speedReadout LengthUnit.meters TimeUnit.seconds
        setup.transverseWaveSpeed := by
    exact NNReal.zero_le_coe
  have h_tangential_speed_nonneg :
      0 ≤ speedReadout LengthUnit.meters TimeUnit.seconds
        setup.tangentialSpeed := by
    exact NNReal.zero_le_coe
  have h_base_speed_readouts :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.transverseWaveSpeed =
        speedReadout LengthUnit.meters TimeUnit.seconds
          setup.tangentialSpeed := by
    nlinarith
  have h_base_speeds :
      setup.transverseWaveSpeed baseUnits =
        setup.tangentialSpeed baseUnits := by
    apply WithDim.ext
    apply NNReal.eq
    exact h_base_speed_readouts
  have h_speeds :
      setup.transverseWaveSpeed = setup.tangentialSpeed := by
    apply Dimensionful.ext
    funext units
    rw [setup.transverseWaveSpeed.2 baseUnits units,
      setup.tangentialSpeed.2 baseUnits units, h_base_speeds]
  constructor
  · exact h_speeds
  · rw [h_speeds, h_readouts.tangentialSpeedCentimetersPerSecond]
    norm_num [recordedDatasetAnswer,
      AnswerChoice.speedCentimetersPerSecond]

end PhyXMiniProblems.ProblemPhyXMini0306
