import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0267

open Dimension

/-!
# Period of a cube coupled to a horizontal spring

A homogeneous cube is mounted on an axle through its center, perpendicular to
the face shown in the primary figure.  A horizontal spring joins a rigid wall
to the upper corner of the cube.  The spring is initially at its natural
length.  The cube is turned through three degrees and released from rest.

Dimensionful physical quantities use Physlib's `Dimensionful` type.  Scalar
real numbers below are only coherent-SI readouts, dimensionless radian
readouts, or signed scalar components such as the spring torque about the
axle.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/--
A nonnegative linear spring stiffness.  Its SI unit is newtons per metre and
its dimension is mass per time squared.
-/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A central moment of inertia, with dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
A torsional stiffness.  Radians are dimensionless, so its dimension is that
of torque, mass times length squared per time squared.
-/
abbrev TorsionalStiffnessQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative angular frequency, with radians treated as dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical mass in coherent SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in coherent SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical duration in coherent SI seconds. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a linear spring stiffness in SI newtons per metre. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in SI kilogram metre squared. -/
def inertiaInKilogramMetersSquared (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a torsional stiffness in SI newton metres per radian. -/
def torsionalStiffnessInNewtonMetersPerRadian
    (stiffness : TorsionalStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Read an angular frequency in radians per SI second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Convert the degree readout printed in the problem to radians. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Apparatus and primary-figure labels -/

/-- The two physical ends of the spring. -/
inductive SpringEnd where
  | wallEnd
  | cubeEnd
  deriving DecidableEq, Repr

/-- Objects distinguished by the problem statement and primary image. -/
inductive FigureObject where
  | rigidWall
  | cube
  deriving DecidableEq, Repr

/-- Vertices of the diamond-shaped cube projection in the primary image. -/
inductive CubeCorner where
  | upper
  | right
  | lower
  | left
  deriving DecidableEq, Repr

/-- The two right-hand edges on which the source image prints `d`. -/
inductive ShownCubeEdge where
  | upperRight
  | lowerRight
  deriving DecidableEq, Repr

/-- The sole dimension label printed on the cube. -/
inductive FigureLabel where
  | edgeLength_d
  deriving DecidableEq, Repr

/-- Location of the rotation axle indicated by the central black dot. -/
inductive AxleLocation where
  | throughCubeCenter
  deriving DecidableEq, Repr

/-- Direction of the axle relative to the square face visible in the figure. -/
inductive AxleDirection where
  | perpendicularToShownFace
  deriving DecidableEq, Repr

/-- Orientation of the spring in the unrotated configuration. -/
inductive SpringOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Qualitative information read from the primary figure. -/
structure CubeSpringFigure where
  springEndAttachment : SpringEnd → FigureObject
  attachedCubeCorner : CubeCorner
  labelOnShownEdge : ShownCubeEdge → FigureLabel
  axleLocation : AxleLocation
  axleDirection : AxleDirection
  springOrientation : SpringOrientation

/-!
The independent physical quantities of the apparatus.

The angle-indexed extension and torque fields are coherent-SI scalar readouts.
The oscillation period and angular frequency are stored independently; neither
is defined to equal the requested numerical answer.
-/
structure CubeSpringSetup where
  cubeMass : MassQuantity
  cubeEdgeLength : LengthQuantity
  axleToUpperCornerRadius : LengthQuantity
  springStiffness : SpringStiffnessQuantity
  springNaturalLength : LengthQuantity
  initialSpringLength : LengthQuantity
  centralAxisMomentOfInertia : MomentOfInertiaQuantity
  effectiveTorsionalStiffness : TorsionalStiffnessQuantity
  angularFrequency : AngularFrequencyQuantity
  oscillationPeriod : TimeQuantity
  releaseAngleRadians : ℝ
  releaseAngularVelocityRadiansPerSecond : ℝ
  springLengthMetersAtAngle : ℝ → ℝ
  springExtensionMeters : ℝ → ℝ
  springElasticEnergyJoules : ℝ → ℝ
  springTorqueNewtonMeters : ℝ → ℝ
  figure : CubeSpringFigure

/-!
Numerical data, release conditions, and geometry stated by the text or read
from the primary image.  The spring's initial length equals its natural length;
no period or answer-choice assertion occurs here.
-/
structure MatchesProblemAndPrimaryFigure (setup : CubeSpringSetup) : Prop where
  cubeMassKilograms : massInKilograms setup.cubeMass = 3
  cubeEdgeLengthMeters : lengthInMeters setup.cubeEdgeLength = 6 / 100
  springStiffnessNewtonsPerMeter :
    stiffnessInNewtonsPerMeter setup.springStiffness = 1200
  springInitiallyAtNaturalLength :
    setup.initialSpringLength = setup.springNaturalLength
  releaseAngleIsThreeDegrees :
    setup.releaseAngleRadians = degreesToRadians 3
  releasedFromRest : setup.releaseAngularVelocityRadiansPerSecond = 0
  wallEndAttachedToRigidWall :
    setup.figure.springEndAttachment .wallEnd = .rigidWall
  cubeEndAttachedToCube :
    setup.figure.springEndAttachment .cubeEnd = .cube
  springAttachedAtUpperCorner : setup.figure.attachedCubeCorner = .upper
  upperRightEdgeLabelledD :
    setup.figure.labelOnShownEdge .upperRight = .edgeLength_d
  lowerRightEdgeLabelledD :
    setup.figure.labelOnShownEdge .lowerRight = .edgeLength_d
  axlePassesThroughCenter : setup.figure.axleLocation = .throughCubeCenter
  axlePerpendicularToShownFace :
    setup.figure.axleDirection = .perpendicularToShownFace
  springInitiallyHorizontal : setup.figure.springOrientation = .horizontal

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalParameters (setup : CubeSpringSetup) : Prop where
  cubeMassPositive : 0 < massInKilograms setup.cubeMass
  cubeEdgeLengthPositive : 0 < lengthInMeters setup.cubeEdgeLength
  cornerRadiusPositive : 0 < lengthInMeters setup.axleToUpperCornerRadius
  springStiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.springStiffness
  springNaturalLengthPositive : 0 < lengthInMeters setup.springNaturalLength
  centralMomentOfInertiaPositive :
    0 < inertiaInKilogramMetersSquared setup.centralAxisMomentOfInertia
  effectiveTorsionalStiffnessPositive :
    0 < torsionalStiffnessInNewtonMetersPerRadian
      setup.effectiveTorsionalStiffness
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  periodPositive : 0 < timeInSeconds setup.oscillationPeriod

/-!
The governing geometry, Hooke elastic energy, conservative spring torque,
rigid-body inertia, and linearized rotational-SHM relations.

Write `L0` for the natural spring length and `r` for the center-to-corner
distance.  Relative to the fixed wall endpoint, the rotated corner has
components `L0 + r sin theta` and `r (cos theta - 1)`, so the square-root
formula below is the actual spring length rather than a finite-angle
horizontal-spring shortcut.  Hooke energy is `k extension^2 / 2`, and torque
is its negative angular derivative.  Linearization at zero therefore has
torsional stiffness `k * r^2`.  A homogeneous cube about an axis through its
center perpendicular to a face has `I = m d^2 / 6`.  Finally, rotational
Newton dynamics gives `omega^2 = kappa / I`, and an SHM cycle has period
`2 pi / omega`.

These general laws contain neither `0.18 s` nor an answer label.
-/
structure SatisfiesSmallAngleCubeSpringModel
    (setup : CubeSpringSetup) : Prop where
  cornerRadiusGeometry :
    lengthInMeters setup.axleToUpperCornerRadius ^ 2 =
      lengthInMeters setup.cubeEdgeLength ^ 2 / 2
  fixedWallToRotatedCornerGeometry :
    ∀ theta : ℝ,
      setup.springLengthMetersAtAngle theta =
        Real.sqrt
          ((lengthInMeters setup.springNaturalLength +
                lengthInMeters setup.axleToUpperCornerRadius *
                  Real.sin theta) ^ 2 +
            (lengthInMeters setup.axleToUpperCornerRadius *
                (Real.cos theta - 1)) ^ 2)
  initialLengthIsZeroAngleLength :
    lengthInMeters setup.initialSpringLength =
      setup.springLengthMetersAtAngle 0
  extensionFromNaturalLength :
    ∀ theta : ℝ,
      setup.springExtensionMeters theta =
        setup.springLengthMetersAtAngle theta -
          lengthInMeters setup.springNaturalLength
  hookeElasticEnergy :
    ∀ theta : ℝ,
      setup.springElasticEnergyJoules theta =
        stiffnessInNewtonsPerMeter setup.springStiffness *
          setup.springExtensionMeters theta ^ 2 / 2
  conservativeSpringTorque :
    ∀ theta : ℝ,
      HasDerivAt setup.springElasticEnergyJoules
        (-setup.springTorqueNewtonMeters theta) theta
  homogeneousCubeCentralAxisInertia :
    inertiaInKilogramMetersSquared setup.centralAxisMomentOfInertia =
      massInKilograms setup.cubeMass *
        lengthInMeters setup.cubeEdgeLength ^ 2 / 6
  linearizedTorsionalStiffness :
    torsionalStiffnessInNewtonMetersPerRadian
        setup.effectiveTorsionalStiffness =
      stiffnessInNewtonsPerMeter setup.springStiffness *
        lengthInMeters setup.axleToUpperCornerRadius ^ 2
  smallOscillationAngularFrequency :
    angularFrequencyInRadiansPerSecond setup.angularFrequency ^ 2 =
      torsionalStiffnessInNewtonMetersPerRadian
          setup.effectiveTorsionalStiffness /
        inertiaInKilogramMetersSquared setup.centralAxisMomentOfInertia
  periodFromAngularFrequency :
    timeInSeconds setup.oscillationPeriod =
      2 * Real.pi /
        angularFrequencyInRadiansPerSecond setup.angularFrequency

/-!
The exact torque law has derivative `-kappa` at the equilibrium angle.  This
derived statement makes precise the local restoring-torque linearization used
by the small-angle SHM model.
-/
lemma springTorque_hasDerivAt_equilibrium
    (setup : CubeSpringSetup)
    (_model : SatisfiesSmallAngleCubeSpringModel setup) :
    HasDerivAt setup.springTorqueNewtonMeters
      (-torsionalStiffnessInNewtonMetersPerRadian
        setup.effectiveTorsionalStiffness) 0 := by
  let L := lengthInMeters setup.springNaturalLength
  let r := lengthInMeters setup.axleToUpperCornerRadius
  let k := stiffnessInNewtonsPerMeter setup.springStiffness
  let p : ℝ → ℝ := fun theta =>
    L ^ 2 + 2 * L * r * Real.sin theta +
      2 * r ^ 2 * (1 - Real.cos theta)
  let e : ℝ → ℝ := fun theta => Real.sqrt (p theta) - L
  let E : ℝ → ℝ := fun theta => k * e theta ^ 2 / 2
  have hp_geometry (theta : ℝ) :
      (L + r * Real.sin theta) ^ 2 +
          (r * (Real.cos theta - 1)) ^ 2 = p theta := by
    dsimp [p]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hp_nonneg (theta : ℝ) : 0 ≤ p theta := by
    rw [← hp_geometry theta]
    positivity
  have henergy : setup.springElasticEnergyJoules = E := by
    funext theta
    rw [_model.hookeElasticEnergy theta,
      _model.extensionFromNaturalLength theta,
      _model.fixedWallToRotatedCornerGeometry theta]
    dsimp [E, e, k, r, L]
    rw [hp_geometry theta]
  have htorque :
      setup.springTorqueNewtonMeters = fun theta => -deriv E theta := by
    funext theta
    have h := (_model.conservativeSpringTorque theta).deriv
    rw [henergy] at h
    linarith
  rw [htorque, _model.linearizedTorsionalStiffness]
  have hL : 0 ≤ L := by
    dsimp [L, lengthInMeters]
    positivity
  rcases hL.eq_or_lt with hLzero | hLpos
  · have hEzero :
        E = fun theta => k * r ^ 2 * (1 - Real.cos theta) := by
      funext theta
      dsimp [E, e]
      rw [← hLzero, sub_zero, Real.sq_sqrt (hp_nonneg theta)]
      dsimp [p]
      rw [← hLzero]
      ring
    have hderivE :
        (fun theta => deriv E theta) =
          fun theta => k * r ^ 2 * Real.sin theta := by
      rw [hEzero]
      funext theta
      have h :=
        (((hasDerivAt_const theta (1 : ℝ)).sub
          (Real.hasDerivAt_cos theta)).const_mul (k * r ^ 2)).deriv
      simpa only [Pi.sub_apply, zero_sub, neg_neg] using h
    have hsin :
        HasDerivAt (fun theta => k * r ^ 2 * Real.sin theta)
          (k * r ^ 2) 0 := by
      simpa only [Real.cos_zero, mul_one] using
        (Real.hasDerivAt_sin 0).const_mul (k * r ^ 2)
    have hderiv :
        HasDerivAt (fun theta => deriv E theta) (k * r ^ 2) 0 :=
      hsin.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun theta => congrFun hderivE theta)
    convert hderiv.neg using 1 <;> rfl
  · let a : ℝ → ℝ := fun theta =>
      L * r * Real.cos theta + r ^ 2 * Real.sin theta
    let D : ℝ → ℝ := fun theta =>
      k * e theta * a theta / Real.sqrt (p theta)
    have hp_deriv (theta : ℝ) :
        HasDerivAt p (2 * a theta) theta := by
      have hraw :=
        ((hasDerivAt_const theta (L ^ 2)).add
          ((Real.hasDerivAt_sin theta).const_mul (2 * L * r))).add
            (((hasDerivAt_const theta (1 : ℝ)).sub
              (Real.hasDerivAt_cos theta)).const_mul (2 * r ^ 2))
      have hfun :
          p =ᶠ[nhds theta]
            (fun y => L ^ 2) +
              (fun y => 2 * L * r * Real.sin y) +
                (fun y => 2 * r ^ 2 * (1 - Real.cos y)) :=
        Filter.Eventually.of_forall fun y => by
          dsimp [p]
      apply (hraw.congr_of_eventuallyEq hfun).congr_deriv
      dsimp [a]
      ring
    have sqrt_chain {f : ℝ → ℝ} {f' x : ℝ}
        (hf : HasDerivAt f f' x) (hfx : 0 < f x) :
        HasDerivAt (fun y => Real.sqrt (f y))
          (f' / (2 * Real.sqrt (f x))) x := by
      rw [hasDerivAt_iff_tendsto_slope_zero]
      have hbase :
          Filter.Tendsto (fun t : ℝ => x + t) (nhds 0) (nhds x) := by
        convert (tendsto_const_nhds.add Filter.tendsto_id :
          Filter.Tendsto (fun t : ℝ => x + t) (nhds 0) (nhds (x + 0))) using 1
        norm_num
      have harg :
          Filter.Tendsto (fun t : ℝ => x + t)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds x) :=
        hbase.mono_left inf_le_left
      have hfsqrt :
          Filter.Tendsto (fun t : ℝ => Real.sqrt (f (x + t)))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sqrt (f x))) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp
          (hf.continuousAt.tendsto.comp harg)
      have hden :
          Filter.Tendsto
            (fun t : ℝ => Real.sqrt (f (x + t)) + Real.sqrt (f x))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
            (nhds (2 * Real.sqrt (f x))) := by
        simpa only [two_mul] using hfsqrt.add tendsto_const_nhds
      have hquot :
          Filter.Tendsto
            ((fun t : ℝ => t⁻¹ • (f (x + t) - f x)) /
              fun t => Real.sqrt (f (x + t)) + Real.sqrt (f x))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
            (nhds (f' / (2 * Real.sqrt (f x)))) :=
        hf.tendsto_slope_zero.div hden (by positivity)
      refine hquot.congr' ?_
      have hfpos : ∀ᶠ y in nhds x, 0 < f y :=
        hf.continuousAt.tendsto.eventually (eventually_gt_nhds hfx)
      filter_upwards [harg.eventually hfpos, self_mem_nhdsWithin] with t hft ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      simp only [Pi.div_apply, smul_eq_mul]
      field_simp [ht]
      nlinarith [Real.sq_sqrt hft.le, Real.sq_sqrt hfx.le]
    have hsqrt {theta : ℝ} (hp : 0 < p theta) :
        HasDerivAt (fun y => Real.sqrt (p y))
          (a theta / Real.sqrt (p theta)) theta := by
      apply (sqrt_chain (hp_deriv theta) hp).congr_deriv
      field_simp [ne_of_gt (Real.sqrt_pos.2 hp)]
    have he_deriv {theta : ℝ} (hp : 0 < p theta) :
        HasDerivAt e (a theta / Real.sqrt (p theta)) theta := by
      simpa only [e] using (hsqrt hp).sub_const L
    have hE_deriv {theta : ℝ} (hp : 0 < p theta) :
        HasDerivAt E (D theta) theta := by
      have hraw := (((he_deriv hp).pow 2).const_mul k).div_const 2
      have hfun :
          E =ᶠ[nhds theta] fun y => k * e y ^ 2 / 2 :=
        Filter.Eventually.of_forall fun y => by rfl
      apply (hraw.congr_of_eventuallyEq hfun).congr_deriv
      dsimp [D]
      ring
    have hp0 : 0 < p 0 := by
      dsimp [p]
      simp only [Real.sin_zero, Real.cos_zero, mul_zero, sub_self,
        add_zero]
      positivity
    have hp_eventually : ∀ᶠ theta in nhds 0, 0 < p theta :=
      (hp_deriv 0).continuousAt.tendsto.eventually (eventually_gt_nhds hp0)
    have hderiv_eventually :
        (fun theta => deriv E theta) =ᶠ[nhds 0] D := by
      filter_upwards [hp_eventually] with theta hp
      exact (hE_deriv hp).deriv
    have ha0 : HasDerivAt a (r ^ 2) 0 := by
      have hraw :=
        ((Real.hasDerivAt_cos 0).const_mul (L * r)).add
          ((Real.hasDerivAt_sin 0).const_mul (r ^ 2))
      have hfun :
          a =ᶠ[nhds 0]
            (fun y => L * r * Real.cos y) +
              fun y => r ^ 2 * Real.sin y :=
        Filter.Eventually.of_forall fun y => by rfl
      apply (hraw.congr_of_eventuallyEq hfun).congr_deriv
      norm_num
    have hD : HasDerivAt D (k * r ^ 2) 0 := by
      have hsqrt0 := hsqrt hp0
      have he0 := he_deriv hp0
      have hraw := (((he0.const_mul k).mul ha0).div hsqrt0
        (by
          dsimp [p]
          simp only [Real.sin_zero, Real.cos_zero, mul_zero, sub_self,
            add_zero, Real.sqrt_sq_eq_abs, abs_of_pos hLpos]
          exact ne_of_gt hLpos))
      have hfun :
          D =ᶠ[nhds 0]
            ((fun y => k * e y) * a / fun y => Real.sqrt (p y)) :=
        Filter.Eventually.of_forall fun y => by rfl
      apply (hraw.congr_of_eventuallyEq hfun).congr_deriv
      have hp0sqrt : Real.sqrt (p 0) = L := by
        dsimp [p]
        simp only [Real.sin_zero, Real.cos_zero, mul_zero, sub_self,
          add_zero, Real.sqrt_sq_eq_abs, abs_of_pos hLpos]
      have he0val : e 0 = 0 := by
        dsimp [e]
        rw [hp0sqrt]
        ring
      have ha0val : a 0 = L * r := by
        dsimp [a]
        simp
      simp only [Pi.mul_apply, hp0sqrt, he0val, ha0val, mul_zero,
        zero_mul, add_zero, sub_zero]
      field_simp [ne_of_gt hLpos]
    convert (hD.congr_of_eventuallyEq hderiv_eventually).neg using 1 <;> rfl

/-!
The factors of the cube edge length cancel between the corner lever arm and
the cube's central-axis moment of inertia, leaving
`omega^2 = 3 k / m`.
-/
lemma angularFrequency_sq_eq_three_stiffness_div_mass
    (setup : CubeSpringSetup)
    (_physical : HasPhysicalParameters setup)
    (_model : SatisfiesSmallAngleCubeSpringModel setup) :
    angularFrequencyInRadiansPerSecond setup.angularFrequency ^ 2 =
      3 * stiffnessInNewtonsPerMeter setup.springStiffness /
        massInKilograms setup.cubeMass := by
  rw [_model.smallOscillationAngularFrequency,
    _model.linearizedTorsionalStiffness,
    _model.homogeneousCubeCentralAxisInertia,
    _model.cornerRadiusGeometry]
  field_simp [ne_of_gt _physical.cubeMassPositive,
    ne_of_gt _physical.cubeEdgeLengthPositive]
  ring

/-- The small-angle period formula after the cube geometry has cancelled. -/
lemma period_eq_cubeSpringFormula
    (setup : CubeSpringSetup)
    (_physical : HasPhysicalParameters setup)
    (_model : SatisfiesSmallAngleCubeSpringModel setup) :
    timeInSeconds setup.oscillationPeriod =
      2 * Real.pi /
        Real.sqrt
          (3 * stiffnessInNewtonsPerMeter setup.springStiffness /
            massInKilograms setup.cubeMass) := by
  rw [_model.periodFromAngularFrequency,
    ← angularFrequency_sq_eq_three_stiffness_div_mass setup _physical _model,
    Real.sqrt_sq_eq_abs,
    abs_of_pos _physical.angularFrequencyPositive]

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate periods. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Period in seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 12 / 100
  | .B => 15 / 100
  | .C => 18 / 100
  | .D => 21 / 100

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Agreement with a period displayed to two decimal places: the exact period is
within half of `0.01 s` of the displayed value.
-/
def MatchesDisplayedPeriod
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  |timeInSeconds period - choice.seconds| ≤ 1 / 200

/-!
For `m = 3.00 kg` and `k = 1200 N/m`, the small-angle period is
`2 pi / sqrt (3 k / m)`, approximately `0.181 s`.  It therefore agrees with
the displayed `0.18 s`, recorded answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0267:target`.
-/
theorem oscillationPeriod_exact_and_matches_recordedAnswerC
    (setup : CubeSpringSetup)
    (_problemAndFigure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_model : SatisfiesSmallAngleCubeSpringModel setup) :
    timeInSeconds setup.oscillationPeriod =
        2 * Real.pi / Real.sqrt (3 * (1200 : ℝ) / 3) ∧
      MatchesDisplayedPeriod setup.oscillationPeriod recordedAnswerChoice := by
  have hperiod := period_eq_cubeSpringFormula setup _physical _model
  rw [_problemAndFigure.springStiffnessNewtonsPerMeter,
    _problemAndFigure.cubeMassKilograms] at hperiod
  constructor
  · exact hperiod
  · rw [MatchesDisplayedPeriod, recordedAnswerChoice, AnswerChoice.seconds, hperiod]
    have hc := Real.cos_bound (x := (4 : ℝ) / 5)
      (by norm_num [abs_of_nonneg])
    have hcpos : 0 < Real.cos ((4 : ℝ) / 5) :=
      Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])
    have hcupper : Real.cos ((4 : ℝ) / 5) ≤ (263 : ℝ) / 375 := by
      rw [abs_le] at hc
      norm_num [abs_of_nonneg] at hc ⊢
      linarith
    have hcosneg : Real.cos ((8 : ℝ) / 5) < 0 := by
      rw [show (8 : ℝ) / 5 = 2 * (4 / 5) by norm_num,
        Real.cos_two_mul]
      nlinarith
    have hpiUpper : Real.pi < (16 : ℝ) / 5 := by
      by_contra h
      have hpi : (16 : ℝ) / 5 ≤ Real.pi := le_of_not_gt h
      have hcosnonneg : 0 ≤ Real.cos ((8 : ℝ) / 5) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by nlinarith [Real.pi_pos]) (by linarith)
      linarith
    have hs := Real.sin_bound (x := (19 : ℝ) / 25)
      (by norm_num [abs_of_nonneg])
    have hsupper : Real.sin ((19 : ℝ) / 25) ≤ (141 : ℝ) / 200 := by
      rw [abs_le] at hs
      norm_num [abs_of_nonneg] at hs ⊢
      linarith
    have hsinpos : 0 < Real.sin ((19 : ℝ) / 25) :=
      Real.sin_pos_of_pos_of_lt_pi (by norm_num)
        (by nlinarith [Real.two_le_pi])
    have hcospos : 0 < Real.cos ((38 : ℝ) / 25) := by
      rw [show (38 : ℝ) / 25 = 2 * (19 / 25) by norm_num,
        Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq ((19 : ℝ) / 25)]
    have hpiLower : (76 : ℝ) / 25 < Real.pi := by
      by_contra h
      have hpi : Real.pi ≤ (76 : ℝ) / 25 := le_of_not_gt h
      have hcosnonpos : Real.cos ((38 : ℝ) / 25) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith)
          (by nlinarith [Real.two_le_pi])
      linarith
    norm_num only [mul_div_cancel_left₀] at *
    have hsqrtPos : 0 < Real.sqrt (1200 : ℝ) :=
      Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : Real.sqrt (1200 : ℝ) ^ 2 = 1200 :=
      Real.sq_sqrt (by norm_num)
    have hsqrtLower : (866 : ℝ) / 25 < Real.sqrt 1200 := by
      nlinarith
    have hsqrtUpper : Real.sqrt 1200 < (1733 : ℝ) / 50 := by
      nlinarith
    have hperiodLower : (7 : ℝ) / 40 <
        2 * Real.pi / Real.sqrt 1200 := by
      rw [lt_div_iff₀ hsqrtPos]
      nlinarith
    have hperiodUpper : 2 * Real.pi / Real.sqrt 1200 <
        (37 : ℝ) / 200 := by
      rw [div_lt_iff₀ hsqrtPos]
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0267
