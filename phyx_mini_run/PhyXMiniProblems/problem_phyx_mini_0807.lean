import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/-!
# Period of a conical pendulum

A bob of mass `m` is attached to a fixed support by a thin wire of length
`L`.  It moves at constant tangential speed `v` around a horizontal circle,
while the wire makes a fixed angle `beta` with the vertical.  The requested
quantity is the duration `T` of one revolution.

Physlib's unit-independent `Dimensionful` quantities represent mass, length,
time, speed, acceleration, and force.  Real numbers are used only for coherent
SI readouts and for the dimensionless angle in radians.

Assumption/target split:

* governing laws: the horizontal-radius projection, vertical force balance,
  horizontal centripetal-force balance, and distance travelled in one uniform
  circular revolution;
* previous-part results: none;
* data and figure readouts: a thin wire from a fixed support to the bob, the
  horizontal dashed circular path, the vertical dashed reference, and the
  labels `L`, `beta`, and tangential `v` shown in the primary bitmap;
* current target: `T = 2 * pi * sqrt (L * cos beta / g)`, corresponding to
  displayed answer choice B.  This relation occurs only as a conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0807

open Dimension

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical mass, independent of a choice of units. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for the wire and orbit radius. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, used for the revolution period. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude, of dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude, used for the wire tension. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical duration in SI seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a nonnegative physical speed in SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in SI newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-image vocabulary -/

/-- The plane containing the bob's circular orbit. -/
inductive OrbitPlane where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Whether the magnitude of the tangential speed changes during the orbit. -/
inductive SpeedRegime where
  | constant
  | varying
  deriving DecidableEq, Repr

/-- The reference direction from which the displayed wire angle is measured. -/
inductive AngleReference where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Distinct physical or graphical objects visible in image `807.png`. -/
inductive FigureObject where
  | fixedSupport
  | suspensionWire
  | pendulumBob
  | verticalDashedReference
  | horizontalDashedCircularPath
  | tangentialVelocityArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels visible in the primary image. -/
inductive FigureLabel where
  | wireLengthL
  | angleBeta
  | speedV
  deriving DecidableEq, Fintype, Repr

/-!
Typed and qualitative evidence transcribed from the primary bitmap.  The
dimensionful fields record what the three displayed labels denote; they are
not definitions of the requested period.
-/
structure ConicalPendulumFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  depictedWireLength : LengthQuantity
  depictedAngleRadians : ℝ
  depictedTangentialSpeed : DimSpeed
  wireStartsAtSupport : Bool
  wireEndsAtBob : Bool
  verticalReferenceIsDashed : Bool
  circularPathIsDashed : Bool
  circularPathAppearsHorizontal : Bool
  betaArcLiesBetweenWireAndVertical : Bool
  lengthArrowFollowsWire : Bool
  velocityArrowIsTangentToCircle : Bool

/-!
Independent physical quantities of the conical pendulum.  In particular,
`revolutionPeriod` is stored independently and is related to the other fields
only by the governing laws below.
-/
structure ConicalPendulumSetup where
  bobMass : MassQuantity
  wireLength : LengthQuantity
  orbitRadius : LengthQuantity
  tangentialSpeed : DimSpeed
  revolutionPeriod : TimeQuantity
  gravitationalAcceleration : AccelerationQuantity
  wireTension : ForceQuantity
  wireAngleFromVerticalRadians : ℝ
  orbitPlane : OrbitPlane
  speedRegime : SpeedRegime
  angleReference : AngleReference
  wireIsThin : Bool
  supportIsFixed : Bool
  bobAttachedToWireEnd : Bool
  figure : ConicalPendulumFigure

/-! ## Scenario, figure evidence, and physical branch -/

/-- Qualitative apparatus and motion stated in the problem prose. -/
structure MatchesConicalPendulumScenario
    (setup : ConicalPendulumSetup) : Prop where
  thinWire : setup.wireIsThin = true
  fixedSupport : setup.supportIsFixed = true
  bobAtWireEnd : setup.bobAttachedToWireEnd = true
  horizontalOrbit : setup.orbitPlane = .horizontal
  constantTangentialSpeed : setup.speedRegime = .constant
  betaMeasuredFromVertical : setup.angleReference = .vertical

/-- Direct readouts and spatial relations from the supplied primary image. -/
structure MatchesPrimaryConicalPendulumFigure
    (setup : ConicalPendulumSetup) : Prop where
  everyDepictedObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everySymbolicLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  labelLDenotesWireLength :
    setup.figure.depictedWireLength = setup.wireLength
  labelBetaDenotesWireAngle :
    setup.figure.depictedAngleRadians =
      setup.wireAngleFromVerticalRadians
  labelVDenotesTangentialSpeed :
    setup.figure.depictedTangentialSpeed = setup.tangentialSpeed
  wireBeginsAtFixedSupport : setup.figure.wireStartsAtSupport = true
  wireTerminatesAtBob : setup.figure.wireEndsAtBob = true
  verticalLineDashed : setup.figure.verticalReferenceIsDashed = true
  circularPathDashed : setup.figure.circularPathIsDashed = true
  circularPathShownHorizontal :
    setup.figure.circularPathAppearsHorizontal = true
  betaArcBetweenWireAndVertical :
    setup.figure.betaArcLiesBetweenWireAndVertical = true
  lengthArrowAlongWire : setup.figure.lengthArrowFollowsWire = true
  speedArrowTangentToOrbit :
    setup.figure.velocityArrowIsTangentToCircle = true

/-!
Positivity and angle bounds selecting a genuine, nondegenerate conical
pendulum rather than a stationary vertical wire or a horizontal wire.
-/
structure HasPhysicalConicalPendulumParameters
    (setup : ConicalPendulumSetup) : Prop where
  positiveBobMass : 0 < massInKilograms setup.bobMass
  positiveWireLength : 0 < lengthInMeters setup.wireLength
  positiveOrbitRadius : 0 < lengthInMeters setup.orbitRadius
  positiveTangentialSpeed :
    0 < speedInMetersPerSecond setup.tangentialSpeed
  positiveRevolutionPeriod : 0 < timeInSeconds setup.revolutionPeriod
  positiveGravity :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  positiveWireTension : 0 < forceInNewtons setup.wireTension
  anglePositive : 0 < setup.wireAngleFromVerticalRadians
  angleLessThanRightAngle :
    setup.wireAngleFromVerticalRadians < Real.pi / 2

/-! ## Governing geometry, dynamics, and kinematics -/

/-!
The horizontal orbit radius is the horizontal projection of the wire,
`r = L sin beta`.  This geometric relation does not mention the period.
-/
structure SatisfiesConicalPendulumGeometry
    (setup : ConicalPendulumSetup) : Prop where
  horizontalRadiusProjection :
    lengthInMeters setup.orbitRadius =
      lengthInMeters setup.wireLength *
        Real.sin setup.wireAngleFromVerticalRadians

/-!
Newton's second law resolved vertically and horizontally.  The vertical
component of tension balances weight, while the horizontal component supplies
the centripetal force.  Neither field states the requested period formula.
-/
structure SatisfiesConicalPendulumDynamics
    (setup : ConicalPendulumSetup) : Prop where
  verticalForceBalance :
    forceInNewtons setup.wireTension *
        Real.cos setup.wireAngleFromVerticalRadians =
      massInKilograms setup.bobMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  horizontalCentripetalForceBalance :
    forceInNewtons setup.wireTension *
        Real.sin setup.wireAngleFromVerticalRadians =
      massInKilograms setup.bobMass *
        speedInMetersPerSecond setup.tangentialSpeed ^ 2 /
          lengthInMeters setup.orbitRadius

/-!
At constant speed, the distance travelled in one period is one circumference,
`v T = 2 pi r`.  This is the general one-revolution kinematic law.
-/
structure SatisfiesUniformCircularKinematics
    (setup : ConicalPendulumSetup) : Prop where
  distanceTravelledInOneRevolution :
    speedInMetersPerSecond setup.tangentialSpeed *
        timeInSeconds setup.revolutionPeriod =
      2 * Real.pi * lengthInMeters setup.orbitRadius

/-!
The component balances and radius projection imply the speed-squared relation
used in the period calculation.  This is a derived intermediate conclusion,
not a premise of the final theorem.
-/
lemma tangentialSpeed_sq_from_force_balance
    (setup : ConicalPendulumSetup)
    (_physical : HasPhysicalConicalPendulumParameters setup)
    (_geometry : SatisfiesConicalPendulumGeometry setup)
    (_dynamics : SatisfiesConicalPendulumDynamics setup) :
    speedInMetersPerSecond setup.tangentialSpeed ^ 2 =
      accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters setup.wireLength *
        Real.sin setup.wireAngleFromVerticalRadians ^ 2 /
        Real.cos setup.wireAngleFromVerticalRadians := by
  let m := massInKilograms setup.bobMass
  let L := lengthInMeters setup.wireLength
  let r := lengthInMeters setup.orbitRadius
  let v := speedInMetersPerSecond setup.tangentialSpeed
  let g :=
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  let F := forceInNewtons setup.wireTension
  let beta := setup.wireAngleFromVerticalRadians
  let s := Real.sin beta
  let c := Real.cos beta
  have hm : 0 < m := _physical.positiveBobMass
  have hr : 0 < r := _physical.positiveOrbitRadius
  have hc : 0 < c := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, _physical.anglePositive]
    · exact _physical.angleLessThanRightAngle
  have hgeometry : r = L * s :=
    _geometry.horizontalRadiusProjection
  have hvertical : F * c = m * g :=
    _dynamics.verticalForceBalance
  have hhorizontal : F * s = m * v ^ 2 / r :=
    _dynamics.horizontalCentripetalForceBalance
  have hhorizontal' : F * s * r = m * v ^ 2 :=
    (eq_div_iff hr.ne').mp hhorizontal
  have hhorizontalCos :
      F * s * r * c = m * v ^ 2 * c :=
    congrArg (fun x : ℝ => x * c) hhorizontal'
  have hverticalScaled :
      F * c * (L * s ^ 2) = m * g * (L * s ^ 2) :=
    congrArg (fun x : ℝ => x * (L * s ^ 2)) hvertical
  have hmassScaled :
      m * (v ^ 2 * c) = m * (g * L * s ^ 2) := by
    calc
      m * (v ^ 2 * c) = m * v ^ 2 * c := by ring
      _ = F * s * r * c := hhorizontalCos.symm
      _ = F * c * (L * s ^ 2) := by rw [hgeometry]; ring
      _ = m * g * (L * s ^ 2) := hverticalScaled
      _ = m * (g * L * s ^ 2) := by ring
  have hcross : v ^ 2 * c = g * L * s ^ 2 :=
    mul_left_cancel₀ hm.ne' hmassScaled
  exact (eq_div_iff hc.ne').mpr hcross

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate period formulas. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/--
The period formula printed beside each answer label, evaluated using coherent
SI readouts.  These definitions record the multiple-choice text; they do not
constrain `setup.revolutionPeriod`.
-/
def AnswerChoice.periodFormulaSeconds
    (choice : AnswerChoice) (setup : ConicalPendulumSetup) : ℝ :=
  let L := lengthInMeters setup.wireLength
  let beta := setup.wireAngleFromVerticalRadians
  let g := accelerationInMetersPerSecondSquared
    setup.gravitationalAcceleration
  match choice with
  | .A => Real.pi * Real.sqrt (L * Real.cos beta / g)
  | .B => 2 * Real.pi * Real.sqrt (L * Real.cos beta / g)
  | .C => 2 * Real.pi * Real.sqrt (L * Real.sin beta / g)
  | .D => Real.pi * Real.sqrt (L * Real.sin beta / g)

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The conical-pendulum force balances and circular kinematics give

`T = 2 pi sqrt (L cos beta / g)`,

which is displayed answer choice B.  This formalizes
`thm:physics:phyx_mini_0807:target`.
-/
theorem conicalPendulum_period_is_choice_B
    (setup : ConicalPendulumSetup)
    (_scenario : MatchesConicalPendulumScenario setup)
    (_figure : MatchesPrimaryConicalPendulumFigure setup)
    (_physical : HasPhysicalConicalPendulumParameters setup)
    (_geometry : SatisfiesConicalPendulumGeometry setup)
    (_dynamics : SatisfiesConicalPendulumDynamics setup)
    (_kinematics : SatisfiesUniformCircularKinematics setup) :
    timeInSeconds setup.revolutionPeriod =
      2 * Real.pi *
        Real.sqrt
          (lengthInMeters setup.wireLength *
              Real.cos setup.wireAngleFromVerticalRadians /
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration) := by
  let L := lengthInMeters setup.wireLength
  let r := lengthInMeters setup.orbitRadius
  let v := speedInMetersPerSecond setup.tangentialSpeed
  let T := timeInSeconds setup.revolutionPeriod
  let g :=
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  let beta := setup.wireAngleFromVerticalRadians
  let s := Real.sin beta
  let c := Real.cos beta
  let p : ℝ := 2 * Real.pi
  have hL : 0 < L := _physical.positiveWireLength
  have hv : 0 < v := _physical.positiveTangentialSpeed
  have hT : 0 < T := _physical.positiveRevolutionPeriod
  have hg : 0 < g := _physical.positiveGravity
  have hc : 0 < c := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, _physical.anglePositive]
    · exact _physical.angleLessThanRightAngle
  have hs : 0 < s := by
    apply Real.sin_pos_of_pos_of_lt_pi _physical.anglePositive
    linarith [Real.pi_pos, _physical.angleLessThanRightAngle]
  have hgeometry : r = L * s :=
    _geometry.horizontalRadiusProjection
  have hspeed :
      v ^ 2 = g * L * s ^ 2 / c :=
    tangentialSpeed_sq_from_force_balance
      setup _physical _geometry _dynamics
  have hspeedCross : v ^ 2 * c = g * L * s ^ 2 :=
    (eq_div_iff hc.ne').mp hspeed
  have hkinematics : v * T = p * r :=
    _kinematics.distanceTravelledInOneRevolution
  have hkinematics' : v * T = p * L * s := by
    rw [hgeometry] at hkinematics
    simpa [mul_assoc] using hkinematics
  have hkinematicsSq :
      v ^ 2 * T ^ 2 = p ^ 2 * L ^ 2 * s ^ 2 := by
    calc
      v ^ 2 * T ^ 2 = (v * T) ^ 2 := by ring
      _ = (p * L * s) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hkinematics'
      _ = p ^ 2 * L ^ 2 * s ^ 2 := by ring
  have hcombined :
      (g * L * s ^ 2) * T ^ 2 =
        (p ^ 2 * L ^ 2 * s ^ 2) * c := by
    calc
      (g * L * s ^ 2) * T ^ 2 =
          (v ^ 2 * c) * T ^ 2 := by rw [hspeedCross]
      _ = (v ^ 2 * T ^ 2) * c := by ring
      _ = (p ^ 2 * L ^ 2 * s ^ 2) * c := by
        rw [hkinematicsSq]
  have hfactorNe : L * s ^ 2 ≠ 0 :=
    mul_ne_zero hL.ne' (pow_ne_zero 2 hs.ne')
  have hcancelEquation :
      (L * s ^ 2) * (g * T ^ 2) =
        (L * s ^ 2) * (p ^ 2 * L * c) := by
    calc
      (L * s ^ 2) * (g * T ^ 2) =
          (g * L * s ^ 2) * T ^ 2 := by ring
      _ = (p ^ 2 * L ^ 2 * s ^ 2) * c := hcombined
      _ = (L * s ^ 2) * (p ^ 2 * L * c) := by ring
  have hperiodCross : g * T ^ 2 = p ^ 2 * L * c :=
    mul_left_cancel₀ hfactorNe hcancelEquation
  have hperiodSq : T ^ 2 = p ^ 2 * (L * c / g) := by
    calc
      T ^ 2 = (p ^ 2 * L * c) / g := by
        apply (eq_div_iff hg.ne').mpr
        simpa [mul_comm] using hperiodCross
      _ = p ^ 2 * (L * c / g) := by ring
  have hradicand : 0 ≤ L * c / g :=
    (div_pos (mul_pos hL hc) hg).le
  have hsquares :
      T ^ 2 = (p * Real.sqrt (L * c / g)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hradicand]
    exact hperiodSq
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquares) with h | h
  · exact h
  · have hrhsNonnegative :
        0 ≤ p * Real.sqrt (L * c / g) := by
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0807
