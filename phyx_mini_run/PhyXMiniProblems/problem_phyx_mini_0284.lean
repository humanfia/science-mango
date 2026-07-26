import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0284

open Dimension

/-!
# Swing period of a demolition ball

The primary image shows a demolition ball hanging from the end pulley of a
crane by one swinging cable segment, next to a brick wall.  The prose gives a
ball mass of `2500 kg` and a swinging length of `17 m`, and asks for the
period when the apparatus is idealized as a simple pendulum.

Physical mass, length, acceleration, and duration are represented by
Physlib's unit-independent `Dimensionful (WithDim ...)` types.  Real numbers
are used only for coherent SI readouts and for the numerical answer choices.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- Acceleration has physical dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def quantitySIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantitySIReadout mass

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantitySIReadout length

/-- Meter-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantitySIReadout acceleration

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  quantitySIReadout duration

/-! ## Primary-image geometry and the physical apparatus -/

/-- Objects visibly present in the supplied demolition-crane image. -/
inductive FigureObject where
  | trackedCraneVehicle
  | craneArm
  | pivotPulley
  | swingingCableSegment
  | demolitionBall
  | brickWall
  | cityscapeBackground
  deriving DecidableEq, Repr

/-- Distinguished attachment points of the pictured swinging cable. -/
inductive FigurePoint where
  | cranePivot
  | demolitionBallAttachment
  deriving DecidableEq, Repr

/-!
Qualitative incidence data from the primary image.  The bitmap contains no
printed scale or text, so all numerical measurements are kept in the prose
data predicate below rather than in this structure.
-/
structure DemolitionCraneFigure where
  shows : FigureObject → Bool
  swingingCableEndpoints : FigurePoint × FigurePoint
  demolitionBallAdjacentToBrickWall : Bool
  containsPrintedText : Bool

/-- Idealized model used for the suspended bob. -/
inductive BobModel where
  | pointMass
  | extendedRigidBody
  deriving DecidableEq, Repr

/-- Idealized mechanical behavior of the swinging cable segment. -/
inductive CableModel where
  | masslessInextensible
  | other
  deriving DecidableEq, Repr

/-- Oscillation regime in which the elementary pendulum period law applies. -/
inductive OscillationRegime where
  | smallAngle
  | finiteAmplitude
  deriving DecidableEq, Repr

/-!
Physical quantities and modeling choices for the demolition-ball pendulum.
The observed period is a field of the experiment; it is not defined to be the
requested answer.  The separate governing-law predicate constrains it.
-/
structure DemolitionBallPendulumSetup where
  figure : DemolitionCraneFigure
  ballMass : MassQuantity
  swingingCableLength : LengthQuantity
  localGravity : AccelerationQuantity
  swingPeriod : TimeQuantity
  bobModel : BobModel
  cableModel : CableModel
  oscillationRegime : OscillationRegime

/-! ## Figure/data readouts and physical assumptions -/

/-!
Readouts from the source prose and primary image.  The mass and cable length
are `2500 kg` and `17 m`; the picture fixes which endpoints the swinging cable
joins and confirms that the ball is beside the wall.  No period, gravity
value, or answer choice is asserted here.
-/
structure MatchesProblemAndFigureData
    (setup : DemolitionBallPendulumSetup) : Prop where
  ballMassKilograms : massInKilograms setup.ballMass = 2500
  swingingCableLengthMeters :
    lengthInMeters setup.swingingCableLength = 17
  allSourceObjectsShown : ∀ object, setup.figure.shows object = true
  swingingCableRunsFromPivotToBall :
    setup.figure.swingingCableEndpoints =
      (.cranePivot, .demolitionBallAttachment)
  ballShownAdjacentToWall :
    setup.figure.demolitionBallAdjacentToBrickWall = true
  imageHasNoPrintedText : setup.figure.containsPrintedText = false

/-!
The standard near-Earth textbook calibration implicit in the numerical
answer.  This is kept separate because the source does not print `g`.
-/
def UsesStandardEarthGravity
    (setup : DemolitionBallPendulumSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.localGravity = 9.8

/-- Positivity conditions for the physical magnitudes in the model. -/
structure HasPhysicalParameters
    (setup : DemolitionBallPendulumSetup) : Prop where
  ballMassPositive : 0 < massInKilograms setup.ballMass
  swingingCableLengthPositive :
    0 < lengthInMeters setup.swingingCableLength
  localGravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.localGravity
  swingPeriodPositive : 0 < timeInSeconds setup.swingPeriod

/-!
## Governing simple-pendulum law

The point-mass, massless-inextensible-cable, small-angle assumptions spell out
what it means here to treat the crane system as a simple pendulum.  The last
field is the standard symbolic law `T = 2π √(L/g)`.  It contains no substituted
`17 m` cable length and no `8.3 s` answer.
-/
structure SatisfiesSmallAngleSimplePendulumPhysics
    (setup : DemolitionBallPendulumSetup) : Prop where
  ballTreatedAsPointMass : setup.bobModel = .pointMass
  cableTreatedAsMasslessAndInextensible :
    setup.cableModel = .masslessInextensible
  usesSmallAngleRegime : setup.oscillationRegime = .smallAngle
  smallAnglePeriodLaw :
    timeInSeconds setup.swingPeriod =
      2 * Real.pi *
        Real.sqrt
          (lengthInMeters setup.swingingCableLength /
            accelerationInMetersPerSecondSquared setup.localGravity)

/-! ## Displayed choices and formalization target -/

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Period in seconds printed beside each source answer choice. -/
def answerPeriodSeconds : AnswerChoice → ℝ
  | .A => 7.6
  | .B => 8.0
  | .C => 8.7
  | .D => 8.3

/-- A computed duration agrees with a displayed one-decimal answer on rounding. -/
def RoundsToDisplayedTenth
    (computedSeconds displayedSeconds : ℝ) : Prop :=
  |computedSeconds - displayedSeconds| < 0.05

/-- A displayed answer is strictly closer than every other listed choice. -/
def IsUniqueClosestAnswerChoice
    (computedSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |computedSeconds - answerPeriodSeconds choice| <
      |computedSeconds - answerPeriodSeconds other|

/-!
For a `17 m` cable in standard gravity, the small-angle pendulum law gives a
period of approximately `8.3 s`; among the supplied values this uniquely
selects answer D.  The `2500 kg` mass is retained in the physical setup even
though it cancels from the simple-pendulum period law.

This is the declaration corresponding to
`thm:physics:phyx_mini_0284:target`.
-/
theorem demolitionBallSwingPeriod_is_answer_D
    (setup : DemolitionBallPendulumSetup)
    (h_data : MatchesProblemAndFigureData setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesSmallAngleSimplePendulumPhysics setup) :
    RoundsToDisplayedTenth
        (timeInSeconds setup.swingPeriod) (answerPeriodSeconds .D) ∧
      IsUniqueClosestAnswerChoice
        (timeInSeconds setup.swingPeriod) .D := by
  have double_cos_lower :
      ∀ x l m : ℝ, |x| ≤ 1 → 0 ≤ l → l < Real.cos x →
        m < 2 * l ^ 2 - 1 → m < Real.cos (2 * x) := by
    intro x l m hx hl hxl hm
    rw [Real.cos_two_mul]
    have hcx := Real.cos_pos_of_le_one hx
    have hp : 0 < (Real.cos x - l) * (Real.cos x + l) :=
      mul_pos (sub_pos.mpr hxl) (by positivity)
    nlinarith
  have double_cos_upper :
      ∀ x u v : ℝ, |x| ≤ 1 → 0 ≤ u → Real.cos x < u →
        2 * u ^ 2 - 1 < v → Real.cos (2 * x) < v := by
    intro x u v hx hu hxu hv
    rw [Real.cos_two_mul]
    have hcx := Real.cos_pos_of_le_one hx
    have hp : 0 < (u - Real.cos x) * (u + Real.cos x) :=
      mul_pos (sub_pos.mpr hxu) (by positivity)
    nlinarith
  have hcos_lower : 0 < Real.cos ((157 : ℝ) / 100) := by
    have hb := Real.cos_bound (x := (157 : ℝ) / 3200)
      (by norm_num [abs_of_nonneg])
    rw [abs_le] at hb
    have h0 : (998796 : ℝ) / 1000000 <
        Real.cos ((157 : ℝ) / 3200) := by
      norm_num [abs_of_nonneg] at hb ⊢
      linarith [hb.1]
    have h1 : (995186 : ℝ) / 1000000 <
        Real.cos ((157 : ℝ) / 1600) := by
      rw [show (157 : ℝ) / 1600 = 2 * (157 / 3200) by norm_num]
      exact double_cos_lower _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h0 (by norm_num)
    have h2 : (98079 : ℝ) / 100000 <
        Real.cos ((157 : ℝ) / 800) := by
      rw [show (157 : ℝ) / 800 = 2 * (157 / 1600) by norm_num]
      exact double_cos_lower _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h1 (by norm_num)
    have h3 : (923898 : ℝ) / 1000000 <
        Real.cos ((157 : ℝ) / 400) := by
      rw [show (157 : ℝ) / 400 = 2 * (157 / 800) by norm_num]
      exact double_cos_lower _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h2 (by norm_num)
    have h4 : (70717 : ℝ) / 100000 <
        Real.cos ((157 : ℝ) / 200) := by
      rw [show (157 : ℝ) / 200 = 2 * (157 / 400) by norm_num]
      exact double_cos_lower _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h3 (by norm_num)
    rw [show (157 : ℝ) / 100 = 2 * (157 / 200) by norm_num]
    exact double_cos_lower _ _ 0 (by norm_num [abs_of_nonneg])
      (by norm_num) h4 (by norm_num)
  have hcos_upper : Real.cos ((63 : ℝ) / 40) < 0 := by
    have hb := Real.cos_bound (x := (63 : ℝ) / 1280)
      (by norm_num [abs_of_nonneg])
    rw [abs_le] at hb
    have h0 : Real.cos ((63 : ℝ) / 1280) <
        (99879 : ℝ) / 100000 := by
      norm_num [abs_of_nonneg] at hb ⊢
      linarith [hb.2]
    have h1 : Real.cos ((63 : ℝ) / 640) <
        (995163 : ℝ) / 1000000 := by
      rw [show (63 : ℝ) / 640 = 2 * (63 / 1280) by norm_num]
      exact double_cos_upper _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h0 (by norm_num)
    have h2 : Real.cos ((63 : ℝ) / 320) <
        (9807 : ℝ) / 10000 := by
      rw [show (63 : ℝ) / 320 = 2 * (63 / 640) by norm_num]
      exact double_cos_upper _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h1 (by norm_num)
    have h3 : Real.cos ((63 : ℝ) / 160) <
        (92355 : ℝ) / 100000 := by
      rw [show (63 : ℝ) / 160 = 2 * (63 / 320) by norm_num]
      exact double_cos_upper _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h2 (by norm_num)
    have h4 : Real.cos ((63 : ℝ) / 80) <
        (7059 : ℝ) / 10000 := by
      rw [show (63 : ℝ) / 80 = 2 * (63 / 160) by norm_num]
      exact double_cos_upper _ _ _ (by norm_num [abs_of_nonneg])
        (by norm_num) h3 (by norm_num)
    rw [show (63 : ℝ) / 40 = 2 * (63 / 80) by norm_num]
    exact double_cos_upper _ _ 0 (by norm_num [abs_of_nonneg])
      (by norm_num) h4 (by norm_num)
  have hpi_lower : (157 : ℝ) / 50 < Real.pi := by
    by_contra h
    have hhalf : Real.pi / 2 ≤ (157 : ℝ) / 100 := by
      push Not at h
      linarith
    have hfar : (157 : ℝ) / 100 ≤ Real.pi + Real.pi / 2 := by
      nlinarith [Real.two_le_pi]
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hhalf hfar
    linarith
  have hpi_upper : Real.pi < (63 : ℝ) / 20 := by
    by_contra h
    have hhalf : (63 : ℝ) / 40 ≤ Real.pi / 2 := by
      push Not at h
      linarith
    have hnear : -(Real.pi / 2) ≤ (63 : ℝ) / 40 := by
      nlinarith [Real.two_le_pi]
    have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le hnear hhalf
    linarith
  have hsqrt_sq :
      Real.sqrt ((85 : ℝ) / 49) ^ 2 = (85 : ℝ) / 49 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((85 : ℝ) / 49) :=
    Real.sqrt_nonneg _
  have hsqrt_lower :
      (1317 : ℝ) / 1000 < Real.sqrt ((85 : ℝ) / 49) := by
    nlinarith
  have hsqrt_upper :
      Real.sqrt ((85 : ℝ) / 49) < (33 : ℝ) / 25 := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt ((85 : ℝ) / 49) := by
    positivity
  have hperiod :
      timeInSeconds setup.swingPeriod =
        2 * Real.pi * Real.sqrt ((85 : ℝ) / 49) := by
    rw [h_laws.smallAnglePeriodLaw, h_data.swingingCableLengthMeters]
    change accelerationInMetersPerSecondSquared setup.localGravity = 9.8 at h_gravity
    rw [h_gravity]
    norm_num
  have hpimul_lower :
      (157 / 50 : ℝ) * Real.sqrt ((85 : ℝ) / 49) <
        Real.pi * Real.sqrt ((85 : ℝ) / 49) :=
    mul_lt_mul_of_pos_right hpi_lower hsqrt_pos
  have hpimul_upper :
      Real.pi * Real.sqrt ((85 : ℝ) / 49) <
        (63 / 20 : ℝ) * Real.sqrt ((85 : ℝ) / 49) :=
    mul_lt_mul_of_pos_right hpi_upper hsqrt_pos
  have hperiod_lower :
      (33 : ℝ) / 4 < timeInSeconds setup.swingPeriod := by
    rw [hperiod]
    nlinarith
  have hperiod_upper :
      timeInSeconds setup.swingPeriod < (167 : ℝ) / 20 := by
    rw [hperiod]
    nlinarith
  have hround :
      RoundsToDisplayedTenth
        (timeInSeconds setup.swingPeriod) (answerPeriodSeconds .D) := by
    rw [RoundsToDisplayedTenth, answerPeriodSeconds, abs_lt]
    constructor <;> norm_num <;> linarith
  refine ⟨hround, ?_⟩
  intro other hother
  have hclose :
      |timeInSeconds setup.swingPeriod - (83 : ℝ) / 10| < (1 : ℝ) / 20 := by
    rw [abs_lt]
    constructor <;> norm_num <;> linarith
  cases other with
  | A =>
      simp only [answerPeriodSeconds]
      rw [show (8.3 : ℝ) = 83 / 10 by norm_num,
        show (7.6 : ℝ) = 38 / 5 by norm_num]
      have hAabs :
          |timeInSeconds setup.swingPeriod - (38 : ℝ) / 5| =
            timeInSeconds setup.swingPeriod - (38 : ℝ) / 5 :=
        abs_of_pos (by linarith [hperiod_lower])
      rw [hAabs]
      linarith
  | B =>
      simp only [answerPeriodSeconds]
      rw [show (8.3 : ℝ) = 83 / 10 by norm_num,
        show (8.0 : ℝ) = 8 by norm_num]
      have hBabs :
          |timeInSeconds setup.swingPeriod - (8 : ℝ)| =
            timeInSeconds setup.swingPeriod - (8 : ℝ) :=
        abs_of_pos (by linarith [hperiod_lower])
      rw [hBabs]
      linarith
  | C =>
      simp only [answerPeriodSeconds]
      rw [show (8.3 : ℝ) = 83 / 10 by norm_num,
        show (8.7 : ℝ) = 87 / 10 by norm_num]
      have hCabs :
          |timeInSeconds setup.swingPeriod - (87 : ℝ) / 10| =
            (87 : ℝ) / 10 - timeInSeconds setup.swingPeriod := by
        rw [abs_of_neg (by linarith [hperiod_upper])]
        ring
      rw [hCabs]
      linarith
  | D =>
      exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0284
