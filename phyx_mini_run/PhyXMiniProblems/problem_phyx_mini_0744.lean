import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0744

open Dimension

/-!
# A projectile landing on an inclined ramp

The primary figure shows a ball at the lower end of a straight incline.  The
incline rises through the horizontal distance `d₁ = 6.00 m` and vertical
distance `d₂ = 3.60 m`, after which the terrain is a horizontal plateau.  The
ball is launched at `10.0 m/s` and `50.0°` above the horizontal.

Lengths, elapsed time, speed, and acceleration are dimensionful Physlib
quantities.  Real numbers are used only for explicitly named coherent-SI
readouts, dimensionless ratios, and radian or degree readouts of angles.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative elapsed time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def quantityReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout length

/-- Second readout of a physical elapsed time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  quantityReadout time

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout speed

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantityReadout acceleration

/-- Convert a degree readout to Mathlib's physical angle type. -/
def angleFromDegrees (angleDegrees : ℝ) : Real.Angle :=
  ((angleDegrees * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Geometry and figure labels -/

/-- A point in the vertical cross-section, with two physical length
coordinates measured from a common Cartesian origin. -/
structure PhysicalPoint2D where
  x : LengthQuantity
  y : LengthQuantity

/-- Horizontal coordinate of a physical point, in metres. -/
def PhysicalPoint2D.xMeters (point : PhysicalPoint2D) : ℝ :=
  lengthInMeters point.x

/-- Vertical coordinate of a physical point, in metres. -/
def PhysicalPoint2D.yMeters (point : PhysicalPoint2D) : ℝ :=
  lengthInMeters point.y

/-- Individually identifiable objects and labels visible in the primary
figure. -/
inductive FigureComponent where
  | ball
  | initialVelocityArrowV0
  | straightInclinedRamp
  | horizontalPlateau
  | horizontalDistanceLabelD1
  | verticalDistanceLabelD2
  deriving DecidableEq, Repr

/-- The two pieces of the terrain on which the ball could first land. -/
inductive TerrainSection where
  | inclinedRamp
  | plateau
  deriving DecidableEq, Repr

/-!
The independent physical objects and quantities in the problem.  `Ball` is
kept abstract so that the ball is not collapsed to scalar data.  In
particular, the landing location, landing time, and trajectory are not fixed
to the requested answer.
-/
structure BallRampProjectileSetup (Ball : Type) where
  ball : Ball
  launchPoint : PhysicalPoint2D
  rampTop : PhysicalPoint2D
  landingPoint : PhysicalPoint2D
  horizontalRampLengthD1 : LengthQuantity
  rampHeightD2 : LengthQuantity
  initialSpeed : SpeedQuantity
  launchAngle : Real.Angle
  gravitationalAcceleration : AccelerationQuantity
  landingTime : TimeQuantity
  positionAt : TimeQuantity → PhysicalPoint2D
  figureShows : FigureComponent → Prop

/-- Exact problem-statement and primary-image readouts.  This records the
straight ramp's endpoint geometry and the launch data, but neither selects a
terrain section for the landing nor assigns the displacement angle. -/
structure MatchesProblemAndPrimaryFigure
    {Ball : Type} (setup : BallRampProjectileSetup Ball) : Prop where
  everyDepictedComponentIsShown : ∀ component, setup.figureShows component
  launchPointAtOrigin :
    setup.launchPoint.xMeters = 0 ∧ setup.launchPoint.yMeters = 0
  rampTopHorizontalCoordinate :
    setup.rampTop.xMeters =
      setup.launchPoint.xMeters +
        lengthInMeters setup.horizontalRampLengthD1
  rampTopVerticalCoordinate :
    setup.rampTop.yMeters =
      setup.launchPoint.yMeters + lengthInMeters setup.rampHeightD2
  horizontalLengthD1Meters :
    lengthInMeters setup.horizontalRampLengthD1 = 6
  verticalHeightD2Meters :
    lengthInMeters setup.rampHeightD2 = 18 / 5
  initialSpeedMetersPerSecond :
    speedInMetersPerSecond setup.initialSpeed = 10
  launchAngleDegrees : setup.launchAngle = angleFromDegrees 50

/-- A point lies on the closed straight incline joining the launch point to
the ramp top.  The last equation is dimensionally a metre-squared equality;
its quotient form would say `dy / dx = d₂ / d₁`. -/
def IsOnInclinedRamp {Ball : Type}
    (setup : BallRampProjectileSetup Ball) (point : PhysicalPoint2D) : Prop :=
  let dx := point.xMeters - setup.launchPoint.xMeters
  let dy := point.yMeters - setup.launchPoint.yMeters
  0 ≤ dx ∧
    dx ≤ lengthInMeters setup.horizontalRampLengthD1 ∧
    0 ≤ dy ∧
    dy ≤ lengthInMeters setup.rampHeightD2 ∧
    lengthInMeters setup.horizontalRampLengthD1 * dy =
      lengthInMeters setup.rampHeightD2 * dx

/-- A point lies on the horizontal plateau beginning at the top of the ramp. -/
def IsOnPlateau {Ball : Type}
    (setup : BallRampProjectileSetup Ball) (point : PhysicalPoint2D) : Prop :=
  lengthInMeters setup.horizontalRampLengthD1 ≤
      point.xMeters - setup.launchPoint.xMeters ∧
    point.yMeters - setup.launchPoint.yMeters =
      lengthInMeters setup.rampHeightD2

/-- A point lies on one of the two exposed terrain sections in the diagram. -/
def IsOnTerrainSurface {Ball : Type}
    (setup : BallRampProjectileSetup Ball) (point : PhysicalPoint2D) : Prop :=
  IsOnInclinedRamp setup point ∨ IsOnPlateau setup point

/-! ## Physical branch conditions and governing laws -/

/-- Positivity and forward-motion conditions for the physical branch depicted
in the image. -/
structure HasPositivePhysicalParameters
    {Ball : Type} (setup : BallRampProjectileSetup Ball) : Prop where
  horizontalRampLengthPositive :
    0 < lengthInMeters setup.horizontalRampLengthD1
  rampHeightPositive : 0 < lengthInMeters setup.rampHeightD2
  initialSpeedPositive : 0 < speedInMetersPerSecond setup.initialSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  landingTimePositive : 0 < timeInSeconds setup.landingTime
  landingIsForward :
    setup.launchPoint.xMeters < setup.landingPoint.xMeters
  launchAngleIsAcute :
    0 < setup.launchAngle.toReal ∧
      setup.launchAngle.toReal < Real.pi / 2

/-- The conventional near-Earth gravitational acceleration used by the
elementary projectile model. -/
structure UsesStandardEarthGravity
    {Ball : Type} (setup : BallRampProjectileSetup Ball) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration =
      49 / 5

/-!
The standard no-drag projectile equations under constant downward gravity.
They are imposed only through the stated landing time, so the nonnegative
physical coordinate representation is not required to describe the later
mathematical continuation below the terrain.
-/
structure ObeysUniformGravityProjectileLaw
    {Ball : Type} (setup : BallRampProjectileSetup Ball) : Prop where
  horizontalPositionLaw :
    ∀ elapsedTime,
      timeInSeconds elapsedTime ≤ timeInSeconds setup.landingTime →
        (setup.positionAt elapsedTime).xMeters =
          setup.launchPoint.xMeters +
            speedInMetersPerSecond setup.initialSpeed *
              Real.Angle.cos setup.launchAngle *
                timeInSeconds elapsedTime
  verticalPositionLaw :
    ∀ elapsedTime,
      timeInSeconds elapsedTime ≤ timeInSeconds setup.landingTime →
        (setup.positionAt elapsedTime).yMeters =
          setup.launchPoint.yMeters +
            speedInMetersPerSecond setup.initialSpeed *
                Real.Angle.sin setup.launchAngle *
                timeInSeconds elapsedTime -
              accelerationInMetersPerSecondSquared
                  setup.gravitationalAcceleration *
                (timeInSeconds elapsedTime) ^ 2 / 2

/-!
Landing means the first positive-time contact of the ballistic trajectory
with either the incline or the plateau.  The disjunction deliberately does
not assume which terrain section is reached; distinguishing the two is part
of the physics argument.
-/
structure ObeysFirstTerrainContactLaw
    {Ball : Type} (setup : BallRampProjectileSetup Ball) : Prop where
  landingPointIsTrajectoryPosition :
    setup.positionAt setup.landingTime = setup.landingPoint
  landingPointIsOnTerrain : IsOnTerrainSurface setup setup.landingPoint
  noEarlierPositiveTerrainContact :
    ∀ elapsedTime,
      0 < timeInSeconds elapsedTime →
        timeInSeconds elapsedTime < timeInSeconds setup.landingTime →
          ¬ IsOnTerrainSurface setup (setup.positionAt elapsedTime)

/-! ## Displacement angle and multiple-choice target -/

/-- The principal radian angle of the launch-to-landing displacement from the
positive horizontal direction.  Forward motion makes `Real.arctan (dy / dx)`
the appropriate branch. -/
def landingDisplacementAngleRadians {Ball : Type}
    (setup : BallRampProjectileSetup Ball) : ℝ :=
  Real.arctan
    ((setup.landingPoint.yMeters - setup.launchPoint.yMeters) /
      (setup.landingPoint.xMeters - setup.launchPoint.xMeters))

/-- Degree readout of the launch-to-landing displacement angle. -/
def landingDisplacementAngleDegrees {Ball : Type}
    (setup : BallRampProjectileSetup Ball) : ℝ :=
  landingDisplacementAngleRadians setup * 180 / Real.pi

/-- Labels printed beside the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree readout printed for each answer choice. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 132 / 5
  | .B => 144 / 5
  | .C => 31
  | .D => 181 / 5

/-- Dataset metadata: the recorded answer label is C.  This definition is not
used as a premise of either theorem. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The exact angle rounds to a displayed value to the nearest tenth of a
degree. -/
def RoundsToNearestTenth (actualDegrees displayedDegrees : ℝ) : Prop :=
  |actualDegrees - displayedDegrees| ≤ 1 / 20

/-- A displayed answer is strictly closer to the physical angle than every
other displayed answer. -/
def IsNearestAnswerChoice
    (actualDegrees : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice, otherChoice ≠ choice →
    |actualDegrees - choice.angleDegrees| <
      |actualDegrees - otherChoice.angleDegrees|

/-- The `10 m/s`, `50°` trajectory under standard gravity cannot reach the
`3.60 m` plateau; its first positive terrain contact is therefore on the
inclined section before `d₁ = 6.00 m`. -/
lemma landingPointLiesOnInclinedRamp
    {Ball : Type}
    (setup : BallRampProjectileSetup Ball)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPositive : HasPositivePhysicalParameters setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hMotion : ObeysUniformGravityProjectileLaw setup)
    (hContact : ObeysFirstTerrainContactLaw setup) :
    IsOnInclinedRamp setup setup.landingPoint := by
  have mul_bounds {a b la ua lb ub : ℝ}
      (hla : 0 ≤ la) (ha : la ≤ a ∧ a ≤ ua)
      (hlb : 0 ≤ lb) (hb : lb ≤ b ∧ b ≤ ub) :
      la * lb ≤ a * b ∧ a * b ≤ ua * ub := by
    constructor
    · have h₁ := mul_nonneg (sub_nonneg.mpr ha.1) (le_trans hlb hb.1)
      have h₂ := mul_nonneg hla (sub_nonneg.mpr hb.1)
      nlinarith
    · have h₁ := mul_nonneg (sub_nonneg.mpr ha.2) (le_trans hlb hb.1)
      have h₂ := mul_nonneg (le_trans hla ha.1) (sub_nonneg.mpr hb.2)
      nlinarith
  have double_bounds {x sl su cl cu sl' su' cl' cu' : ℝ}
      (hsl : 0 ≤ sl) (hcl : 0 ≤ cl)
      (hs : sl ≤ Real.sin x ∧ Real.sin x ≤ su)
      (hc : cl ≤ Real.cos x ∧ Real.cos x ≤ cu)
      (hsl' : sl' ≤ 2 * sl * cl) (hsu' : 2 * su * cu ≤ su')
      (hcl' : cl' ≤ 2 * cl ^ 2 - 1) (hcu' : 2 * cu ^ 2 - 1 ≤ cu') :
      (sl' ≤ Real.sin (2 * x) ∧ Real.sin (2 * x) ≤ su') ∧
        (cl' ≤ Real.cos (2 * x) ∧ Real.cos (2 * x) ≤ cu') := by
    have hsc := mul_bounds hsl hs hcl hc
    have hcc := mul_bounds hcl hc hcl hc
    rw [Real.sin_two_mul, Real.cos_two_mul]
    simp only [pow_two] at hcl' hcu' ⊢
    constructor <;> constructor <;>
      nlinarith [hsc.1, hsc.2, hcc.1, hcc.2]
  have trig1973 : Real.tan (1973 / 10000 : ℝ) < 1 / 5 := by
    let z : ℝ := 1973 / 40000
    have hs0 : (493046907 / 10000000000 : ℝ) ≤ Real.sin z ∧
        Real.sin z ≤ 493053074 / 10000000000 := by
      have h :=
        abs_le.mp (Real.sin_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have hc0 : (9987832138 / 10000000000 : ℝ) ≤ Real.cos z ∧
        Real.cos z ≤ 9987838305 / 10000000000 := by
      have h :=
        abs_le.mp (Real.cos_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have h1 := double_bounds (by norm_num) (by norm_num) hs0 hc0
      (show (984893948 / 10000000000 : ℝ) ≤
        2 * (493046907 / 10000000000) *
          (9987832138 / 10000000000) by norm_num)
      (show 2 * (493053074 / 10000000000 : ℝ) *
          (9987838305 / 10000000000) ≤
        984906876 / 10000000000 by norm_num)
      (show (9951358163 / 10000000000 : ℝ) ≤
        2 * (9987832138 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9987838305 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9951382802 / 10000000000 by norm_num)
    have h2 := double_bounds (by norm_num) (by norm_num) h1.1 h1.2
      (show (1960206485 / 10000000000 : ℝ) ≤
        2 * (984893948 / 10000000000) *
          (9951358163 / 10000000000) by norm_num)
      (show 2 * (984906876 / 10000000000 : ℝ) *
          (9951382802 / 10000000000) ≤
        1960237070 / 10000000000 by norm_num)
      (show (9805905857 / 10000000000 : ℝ) ≤
        2 * (9951358163 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9951382802 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9806003935 / 10000000000 by norm_num)
    have hy :
        (1973 / 10000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    rw [show (2 * (2 * z) : ℝ) = 1973 / 10000 by
      dsimp [z]
      norm_num] at h2
    norm_num at h2 ⊢
    nlinarith [h2.1.2, h2.2.1]
  have trig1974 : (1 : ℝ) / 5 < Real.tan (1974 / 10000) := by
    let z : ℝ := 1974 / 40000
    have hs0 : (493296597 / 10000000000 : ℝ) ≤ Real.sin z ∧
        Real.sin z ≤ 493302776 / 10000000000 := by
      have h :=
        abs_le.mp (Real.sin_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have hc0 : (9987819798 / 10000000000 : ℝ) ≤ Real.cos z ∧
        Real.cos z ≤ 9987825977 / 10000000000 := by
      have h :=
        abs_le.mp (Real.cos_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have h1 := double_bounds (by norm_num) (by norm_num) hs0 hc0
      (show (985391503 / 10000000000 : ℝ) ≤
        2 * (493296597 / 10000000000) *
          (9987819798 / 10000000000) by norm_num)
      (show 2 * (493302776 / 10000000000 : ℝ) *
          (9987825977 / 10000000000) ≤
        985404457 / 10000000000 by norm_num)
      (show (9951308863 / 10000000000 : ℝ) ≤
        2 * (9987819798 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9987825977 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9951333550 / 10000000000 by norm_num)
    have h2 := double_bounds (by norm_num) (by norm_num) h1.1 h1.2
      (show (1961187039 / 10000000000 : ℝ) ≤
        2 * (985391503 / 10000000000) *
          (9951308863 / 10000000000) by norm_num)
      (show 2 * (985404457 / 10000000000 : ℝ) *
          (9951333550 / 10000000000) ≤
        1961217687 / 10000000000 by norm_num)
      (show (9805709617 / 10000000000 : ℝ) ≤
        2 * (9951308863 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9951333550 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9805807885 / 10000000000 by norm_num)
    have hy :
        (1974 / 10000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    rw [show (2 * (2 * z) : ℝ) = 1974 / 10000 by
      dsimp [z]
      norm_num] at h2
    norm_num at h2 ⊢
    nlinarith [h2.1.1, h2.2.2]
  have trig4184 : Real.tan (4184 / 1000000 : ℝ) < 1 / 239 := by
    have hs := abs_le.mp
      (Real.sin_bound (x := (4184 / 1000000 : ℝ)) (by norm_num))
    have hc := abs_le.mp
      (Real.cos_bound (x := (4184 / 1000000 : ℝ)) (by norm_num))
    have hy :
        (4184 / 1000000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    norm_num at hs hc ⊢
    nlinarith [hs.2, hc.1]
  have trig42 : (1 : ℝ) / 239 < Real.tan (42 / 10000) := by
    have hs := abs_le.mp
      (Real.sin_bound (x := (42 / 10000 : ℝ)) (by norm_num))
    have hc := abs_le.mp
      (Real.cos_bound (x := (42 / 10000 : ℝ)) (by norm_num))
    have hy :
        (42 / 10000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    norm_num at hs hc ⊢
    nlinarith [hs.1, hc.2]
  have atan5lo : (1973 / 10000 : ℝ) < Real.arctan (1 / 5) := by
    have hy :
        (1973 / 10000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    calc
      (1973 / 10000 : ℝ) =
          Real.arctan (Real.tan (1973 / 10000)) :=
        (Real.arctan_tan hy.1 hy.2).symm
      _ < Real.arctan (1 / 5) := Real.arctan_strictMono trig1973
  have atan5hi : Real.arctan (1 / 5 : ℝ) < 1974 / 10000 := by
    have hy :
        (1974 / 10000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    calc
      Real.arctan (1 / 5 : ℝ) <
          Real.arctan (Real.tan (1974 / 10000)) :=
        Real.arctan_strictMono trig1974
      _ = 1974 / 10000 := Real.arctan_tan hy.1 hy.2
  have atan239lo :
      (4184 / 1000000 : ℝ) < Real.arctan (1 / 239) := by
    have hy :
        (4184 / 1000000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    calc
      (4184 / 1000000 : ℝ) =
          Real.arctan (Real.tan (4184 / 1000000)) :=
        (Real.arctan_tan hy.1 hy.2).symm
      _ < Real.arctan (1 / 239) := Real.arctan_strictMono trig4184
  have atan239hi :
      Real.arctan (1 / 239 : ℝ) < 42 / 10000 := by
    have hy :
        (42 / 10000 : ℝ) ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hp : (1 : ℝ) ≤ Real.pi / 2 := by
        linarith [Real.two_le_pi]
      constructor <;> norm_num <;> linarith
    calc
      Real.arctan (1 / 239 : ℝ) <
          Real.arctan (Real.tan (42 / 10000)) :=
        Real.arctan_strictMono trig42
      _ = 42 / 10000 := Real.arctan_tan hy.1 hy.2
  have hpi := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num at hpi
  have pi_lower : (157 : ℝ) / 50 < Real.pi := by
    nlinarith only [atan5lo, atan239hi, hpi]
  have pi_upper : Real.pi < (98177 : ℝ) / 31250 := by
    nlinarith only [atan5hi, atan239lo, hpi]
  have sin_launch_le : Real.sin (5 * Real.pi / 18) ≤ (4 : ℝ) / 5 := by
    have hx_nonneg : 0 ≤ (5 * Real.pi / 18 : ℝ) := by
      positivity
    have hx_lower : (157 / 180 : ℝ) ≤ 5 * Real.pi / 18 := by
      nlinarith only [pi_lower]
    have hx_upper : (5 * Real.pi / 18 : ℝ) ≤ 7 / 8 := by
      nlinarith only [pi_upper]
    have hx_abs : |(5 * Real.pi / 18 : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      linarith
    have hs := abs_le.mp
      (Real.sin_bound (x := (5 * Real.pi / 18 : ℝ)) hx_abs)
    rw [abs_of_nonneg hx_nonneg] at hs
    have hcubic :
        (157 / 180 : ℝ) ^ 3 ≤ (5 * Real.pi / 18 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx_lower 3
    have hquartic :
        (5 * Real.pi / 18 : ℝ) ^ 4 ≤ (7 / 8 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_upper 4
    norm_num at hs hcubic hquartic ⊢
    nlinarith only [hs.2, hcubic, hquartic, hx_upper]
  rcases hContact.landingPointIsOnTerrain with hIncline | hPlateau
  · exact hIncline
  · have hVertical :=
      hMotion.verticalPositionLaw setup.landingTime (le_refl _)
    rw [hContact.landingPointIsTrajectoryPosition] at hVertical
    have hLandingHeight := hPlateau.2
    rw [hFigure.verticalHeightD2Meters] at hLandingHeight
    have hLaunchY := hFigure.launchPointAtOrigin.2
    have hLandingY : setup.landingPoint.yMeters = 18 / 5 := by
      linarith
    have hTimePositive := hPositive.landingTimePositive
    have hsin :
        Real.Angle.sin setup.launchAngle =
          Real.sin (5 * Real.pi / 18) := by
      rw [hFigure.launchAngleDegrees]
      simp [angleFromDegrees]
      congr 1
      ring
    rw [hLandingY, hLaunchY, hFigure.initialSpeedMetersPerSecond,
      hGravity.gravityMetersPerSecondSquared, hsin] at hVertical
    have hproduct := mul_nonneg
      (sub_nonneg.mpr sin_launch_le) (le_of_lt hTimePositive)
    norm_num at hVertical hproduct
    nlinarith only [hVertical, hproduct, sq_nonneg
      (49 * timeInSeconds setup.landingTime - 40)]

/--
Because the landing point lies on the straight incline, its displacement has
slope `d₂ / d₁ = 3 / 5`.  Hence the exact angle is `arctan (3 / 5)`, whose
degree readout rounds to `31.0°` and uniquely selects answer C.

This formalizes `thm:physics:phyx_mini_0744:target`.
-/
theorem landingDisplacementAngleIsAnswerC
    {Ball : Type}
    (setup : BallRampProjectileSetup Ball)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPositive : HasPositivePhysicalParameters setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hMotion : ObeysUniformGravityProjectileLaw setup)
    (hContact : ObeysFirstTerrainContactLaw setup) :
    IsOnInclinedRamp setup setup.landingPoint ∧
      landingDisplacementAngleRadians setup =
        Real.arctan ((3 : ℝ) / 5) ∧
      RoundsToNearestTenth
        (landingDisplacementAngleDegrees setup)
        AnswerChoice.C.angleDegrees ∧
      IsNearestAnswerChoice
        (landingDisplacementAngleDegrees setup) .C := by
  have hIncline :=
    landingPointLiesOnInclinedRamp
      setup hFigure hPositive hGravity hMotion hContact
  have hAngle :
      landingDisplacementAngleRadians setup =
        Real.arctan ((3 : ℝ) / 5) := by
    unfold landingDisplacementAngleRadians
    apply congrArg Real.arctan
    rcases hIncline with ⟨_, _, _, _, hslope⟩
    rw [hFigure.horizontalLengthD1Meters,
      hFigure.verticalHeightD2Meters] at hslope
    have hdx :
        0 <
          setup.landingPoint.xMeters -
            setup.launchPoint.xMeters :=
      sub_pos.mpr hPositive.landingIsForward
    apply (div_eq_iff hdx.ne').2
    norm_num at hslope ⊢
    linarith
  have mul_bounds {a b la ua lb ub : ℝ}
      (hla : 0 ≤ la) (ha : la ≤ a ∧ a ≤ ua)
      (hlb : 0 ≤ lb) (hb : lb ≤ b ∧ b ≤ ub) :
      la * lb ≤ a * b ∧ a * b ≤ ua * ub := by
    constructor
    · have h₁ := mul_nonneg (sub_nonneg.mpr ha.1) (le_trans hlb hb.1)
      have h₂ := mul_nonneg hla (sub_nonneg.mpr hb.1)
      nlinarith
    · have h₁ := mul_nonneg (sub_nonneg.mpr ha.2) (le_trans hlb hb.1)
      have h₂ := mul_nonneg (le_trans hla ha.1) (sub_nonneg.mpr hb.2)
      nlinarith
  have double_bounds {x sl su cl cu sl' su' cl' cu' : ℝ}
      (hsl : 0 ≤ sl) (hcl : 0 ≤ cl)
      (hs : sl ≤ Real.sin x ∧ Real.sin x ≤ su)
      (hc : cl ≤ Real.cos x ∧ Real.cos x ≤ cu)
      (hsl' : sl' ≤ 2 * sl * cl) (hsu' : 2 * su * cu ≤ su')
      (hcl' : cl' ≤ 2 * cl ^ 2 - 1) (hcu' : 2 * cu ^ 2 - 1 ≤ cu') :
      (sl' ≤ Real.sin (2 * x) ∧ Real.sin (2 * x) ≤ su') ∧
        (cl' ≤ Real.cos (2 * x) ∧ Real.cos (2 * x) ≤ cu') := by
    have hsc := mul_bounds hsl hs hcl hc
    have hcc := mul_bounds hcl hc hcl hc
    rw [Real.sin_two_mul, Real.cos_two_mul]
    simp only [pow_two] at hcl' hcu' ⊢
    constructor <;> constructor <;>
      nlinarith [hsc.1, hsc.2, hcc.1, hcc.2]
  have small_mem {x : ℝ} (hx : |x| < 1) :
      x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hp : (1 : ℝ) ≤ Real.pi / 2 := by
      linarith [Real.two_le_pi]
    rw [abs_lt] at hx
    constructor <;> linarith
  have trig1973 : Real.tan (1973 / 10000 : ℝ) < 1 / 5 := by
    let z : ℝ := 1973 / 40000
    have hs0 : (493046907 / 10000000000 : ℝ) ≤ Real.sin z ∧
        Real.sin z ≤ 493053074 / 10000000000 := by
      have h :=
        abs_le.mp (Real.sin_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have hc0 : (9987832138 / 10000000000 : ℝ) ≤ Real.cos z ∧
        Real.cos z ≤ 9987838305 / 10000000000 := by
      have h :=
        abs_le.mp (Real.cos_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have h1 := double_bounds (by norm_num) (by norm_num) hs0 hc0
      (show (984893948 / 10000000000 : ℝ) ≤
        2 * (493046907 / 10000000000) *
          (9987832138 / 10000000000) by norm_num)
      (show 2 * (493053074 / 10000000000 : ℝ) *
          (9987838305 / 10000000000) ≤
        984906876 / 10000000000 by norm_num)
      (show (9951358163 / 10000000000 : ℝ) ≤
        2 * (9987832138 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9987838305 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9951382802 / 10000000000 by norm_num)
    have h2 := double_bounds (by norm_num) (by norm_num) h1.1 h1.2
      (show (1960206485 / 10000000000 : ℝ) ≤
        2 * (984893948 / 10000000000) *
          (9951358163 / 10000000000) by norm_num)
      (show 2 * (984906876 / 10000000000 : ℝ) *
          (9951382802 / 10000000000) ≤
        1960237070 / 10000000000 by norm_num)
      (show (9805905857 / 10000000000 : ℝ) ≤
        2 * (9951358163 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9951382802 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9806003935 / 10000000000 by norm_num)
    have hy := small_mem
      (show |(1973 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    rw [show (2 * (2 * z) : ℝ) = 1973 / 10000 by
      dsimp [z]
      norm_num] at h2
    norm_num at h2 ⊢
    nlinarith [h2.1.2, h2.2.1]
  have trig1974 : (1 : ℝ) / 5 < Real.tan (1974 / 10000) := by
    let z : ℝ := 1974 / 40000
    have hs0 : (493296597 / 10000000000 : ℝ) ≤ Real.sin z ∧
        Real.sin z ≤ 493302776 / 10000000000 := by
      have h :=
        abs_le.mp (Real.sin_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have hc0 : (9987819798 / 10000000000 : ℝ) ≤ Real.cos z ∧
        Real.cos z ≤ 9987825977 / 10000000000 := by
      have h :=
        abs_le.mp (Real.cos_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have h1 := double_bounds (by norm_num) (by norm_num) hs0 hc0
      (show (985391503 / 10000000000 : ℝ) ≤
        2 * (493296597 / 10000000000) *
          (9987819798 / 10000000000) by norm_num)
      (show 2 * (493302776 / 10000000000 : ℝ) *
          (9987825977 / 10000000000) ≤
        985404457 / 10000000000 by norm_num)
      (show (9951308863 / 10000000000 : ℝ) ≤
        2 * (9987819798 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9987825977 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9951333550 / 10000000000 by norm_num)
    have h2 := double_bounds (by norm_num) (by norm_num) h1.1 h1.2
      (show (1961187039 / 10000000000 : ℝ) ≤
        2 * (985391503 / 10000000000) *
          (9951308863 / 10000000000) by norm_num)
      (show 2 * (985404457 / 10000000000 : ℝ) *
          (9951333550 / 10000000000) ≤
        1961217687 / 10000000000 by norm_num)
      (show (9805709617 / 10000000000 : ℝ) ≤
        2 * (9951308863 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9951333550 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9805807885 / 10000000000 by norm_num)
    have hy := small_mem
      (show |(1974 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    rw [show (2 * (2 * z) : ℝ) = 1974 / 10000 by
      dsimp [z]
      norm_num] at h2
    norm_num at h2 ⊢
    nlinarith [h2.1.1, h2.2.2]
  have trig4184 : Real.tan (4184 / 1000000 : ℝ) < 1 / 239 := by
    have hs := abs_le.mp
      (Real.sin_bound (x := (4184 / 1000000 : ℝ)) (by norm_num))
    have hc := abs_le.mp
      (Real.cos_bound (x := (4184 / 1000000 : ℝ)) (by norm_num))
    have hy := small_mem
      (show |(4184 / 1000000 : ℝ)| < 1 by norm_num)
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    norm_num at hs hc ⊢
    nlinarith [hs.2, hc.1]
  have trig42 : (1 : ℝ) / 239 < Real.tan (42 / 10000) := by
    have hs := abs_le.mp
      (Real.sin_bound (x := (42 / 10000 : ℝ)) (by norm_num))
    have hc := abs_le.mp
      (Real.cos_bound (x := (42 / 10000 : ℝ)) (by norm_num))
    have hy := small_mem
      (show |(42 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    norm_num at hs hc ⊢
    nlinarith [hs.1, hc.2]
  have atan5lo :
      (1973 / 10000 : ℝ) < Real.arctan (1 / 5) := by
    have h := Real.arctan_strictMono trig1973
    have hy := small_mem
      (show |(1973 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.arctan_tan hy.1 hy.2] at h
    exact h
  have atan5hi :
      Real.arctan (1 / 5 : ℝ) < 1974 / 10000 := by
    have h := Real.arctan_strictMono trig1974
    have hy := small_mem
      (show |(1974 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.arctan_tan hy.1 hy.2] at h
    exact h
  have atan239lo :
      (4184 / 1000000 : ℝ) < Real.arctan (1 / 239) := by
    have h := Real.arctan_strictMono trig4184
    have hy := small_mem
      (show |(4184 / 1000000 : ℝ)| < 1 by norm_num)
    rw [Real.arctan_tan hy.1 hy.2] at h
    exact h
  have atan239hi :
      Real.arctan (1 / 239 : ℝ) < 42 / 10000 := by
    have h := Real.arctan_strictMono trig42
    have hy := small_mem
      (show |(42 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.arctan_tan hy.1 hy.2] at h
    exact h
  have hpi := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num at hpi
  have pi_lower : (157 : ℝ) / 50 < Real.pi := by
    nlinarith only [atan5lo, atan239hi, hpi]
  have pi_upper : Real.pi < (98177 : ℝ) / 31250 := by
    nlinarith only [atan5hi, atan239lo, hpi]
  have tan5404 : Real.tan (5404 / 10000 : ℝ) < 3 / 5 := by
    let z : ℝ := 5404 / 160000
    have hs0 : (337685107 / 10000000000 : ℝ) ≤ Real.sin z ∧
        Real.sin z ≤ 337686464 / 10000000000 := by
      have h :=
        abs_le.mp (Real.sin_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have hc0 : (9994295569 / 10000000000 : ℝ) ≤ Real.cos z ∧
        Real.cos z ≤ 9994296925 / 10000000000 := by
      have h :=
        abs_le.mp (Real.cos_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have h1 := double_bounds (by norm_num) (by norm_num) hs0 hc0
      (show (674984953 / 10000000000 : ℝ) ≤
        2 * (337685107 / 10000000000) *
          (9994295569 / 10000000000) by norm_num)
      (show 2 * (337686464 / 10000000000 : ℝ) *
          (9994296925 / 10000000000) ≤
        674987758 / 10000000000 by norm_num)
      (show (9977188784 / 10000000000 : ℝ) ≤
        2 * (9994295569 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9994296925 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9977194206 / 10000000000 by norm_num)
    have h2 := double_bounds (by norm_num) (by norm_num) h1.1 h1.2
      (show (1346890460 / 10000000000 : ℝ) ≤
        2 * (674984953 / 10000000000) *
          (9977188784 / 10000000000) by norm_num)
      (show 2 * (674987758 / 10000000000 : ℝ) *
          (9977194206 / 10000000000) ≤
        1346896790 / 10000000000 by norm_num)
      (show (9908859206 / 10000000000 : ℝ) ≤
        2 * (9977188784 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9977194206 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9908880845 / 10000000000 by norm_num)
    have h3 := double_bounds (by norm_num) (by norm_num) h2.1 h2.2
      (show (2669229586 / 10000000000 : ℝ) ≤
        2 * (1346890460 / 10000000000) *
          (9908859206 / 10000000000) by norm_num)
      (show 2 * (1346896790 / 10000000000 : ℝ) *
          (9908880845 / 10000000000) ≤
        2669247961 / 10000000000 by norm_num)
      (show (9637098152 / 10000000000 : ℝ) ≤
        2 * (9908859206 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9908880845 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9637183921 / 10000000000 by norm_num)
    have h4 := double_bounds (by norm_num) (by norm_num) h3.1 h3.2
      (show (5144725502 / 10000000000 : ℝ) ≤
        2 * (2669229586 / 10000000000) *
          (9637098152 / 10000000000) by norm_num)
      (show 2 * (2669247961 / 10000000000 : ℝ) *
          (9637183921 / 10000000000) ≤
        5144806707 / 10000000000 by norm_num)
      (show (8574732158 / 10000000000 : ℝ) ≤
        2 * (9637098152 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9637183921 / 10000000000 : ℝ) ^ 2 - 1 ≤
        8575062786 / 10000000000 by norm_num)
    have hy := small_mem
      (show |(5404 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    rw [show (2 * (2 * (2 * (2 * z))) : ℝ) = 5404 / 10000 by
      dsimp [z]
      norm_num] at h4
    norm_num at h4 ⊢
    nlinarith only [h4.1.2, h4.2.1]
  have tan5405 : (3 / 5 : ℝ) < Real.tan (5405 / 10000) := by
    let z : ℝ := 5405 / 160000
    have hs0 : (337747571 / 10000000000 : ℝ) ≤ Real.sin z ∧
        Real.sin z ≤ 337748928 / 10000000000 := by
      have h :=
        abs_le.mp (Real.sin_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have hc0 : (9994293457 / 10000000000 : ℝ) ≤ Real.cos z ∧
        Real.cos z ≤ 9994294815 / 10000000000 := by
      have h :=
        abs_le.mp (Real.cos_bound (x := z) (by dsimp [z]; norm_num))
      dsimp [z] at h ⊢
      norm_num at h ⊢
      constructor <;> linarith [h.1, h.2]
    have h1 := double_bounds (by norm_num) (by norm_num) hs0 hc0
      (show (675109667 / 10000000000 : ℝ) ≤
        2 * (337747571 / 10000000000) *
          (9994293457 / 10000000000) by norm_num)
      (show 2 * (337748928 / 10000000000 : ℝ) *
          (9994294815 / 10000000000) ≤
        675112472 / 10000000000 by norm_num)
      (show (9977180340 / 10000000000 : ℝ) ≤
        2 * (9994293457 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9994294815 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9977185770 / 10000000000 by norm_num)
    have h2 := double_bounds (by norm_num) (by norm_num) h1.1 h1.2
      (show (1347138179 / 10000000000 : ℝ) ≤
        2 * (675109667 / 10000000000) *
          (9977180340 / 10000000000) by norm_num)
      (show 2 * (675112472 / 10000000000 : ℝ) *
          (9977185770 / 10000000000) ≤
        1347144510 / 10000000000 by norm_num)
      (show (9908825507 / 10000000000 : ℝ) ≤
        2 * (9977180340 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9977185770 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9908847178 / 10000000000 by norm_num)
    have h3 := double_bounds (by norm_num) (by norm_num) h2.1 h2.2
      (show (2669711429 / 10000000000 : ℝ) ≤
        2 * (1347138179 / 10000000000) *
          (9908825507 / 10000000000) by norm_num)
      (show 2 * (1347144510 / 10000000000 : ℝ) *
          (9908847178 / 10000000000) ≤
        2669729816 / 10000000000 by norm_num)
      (show (9636964585 / 10000000000 : ℝ) ≤
        2 * (9908825507 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9908847178 / 10000000000 : ℝ) ^ 2 - 1 ≤
        9637050480 / 10000000000 by norm_num)
    have h4 := double_bounds (by norm_num) (by norm_num) h3.1 h3.2
      (show (5145582898 / 10000000000 : ℝ) ≤
        2 * (2669711429 / 10000000000) *
          (9636964585 / 10000000000) by norm_num)
      (show 2 * (2669729816 / 10000000000 : ℝ) *
          (9637050480 / 10000000000) ≤
        5145664201 / 10000000000 by norm_num)
      (show (8574217282 / 10000000000 : ℝ) ≤
        2 * (9636964585 / 10000000000) ^ 2 - 1 by norm_num)
      (show 2 * (9637050480 / 10000000000 : ℝ) ^ 2 - 1 ≤
        8574548391 / 10000000000 by norm_num)
    have hy := small_mem
      (show |(5405 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ (Real.cos_pos_of_mem_Ioo hy)).2
    rw [show (2 * (2 * (2 * (2 * z))) : ℝ) = 5405 / 10000 by
      dsimp [z]
      norm_num] at h4
    norm_num at h4 ⊢
    nlinarith only [h4.1.1, h4.2.2]
  have atan_lower :
      (5404 / 10000 : ℝ) < Real.arctan (3 / 5) := by
    have h := Real.arctan_strictMono tan5404
    have hy := small_mem
      (show |(5404 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.arctan_tan hy.1 hy.2] at h
    exact h
  have atan_upper :
      Real.arctan (3 / 5 : ℝ) < 5405 / 10000 := by
    have h := Real.arctan_strictMono tan5405
    have hy := small_mem
      (show |(5405 / 10000 : ℝ)| < 1 by norm_num)
    rw [Real.arctan_tan hy.1 hy.2] at h
    exact h
  have degree_lower :
      (619 : ℝ) / 20 ≤
        Real.arctan (3 / 5) * 180 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith only [atan_lower, pi_upper]
  have degree_upper :
      Real.arctan (3 / 5) * 180 / Real.pi ≤
        (621 : ℝ) / 20 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith only [atan_upper, pi_lower]
  have hRound :
      RoundsToNearestTenth
        (landingDisplacementAngleDegrees setup)
        AnswerChoice.C.angleDegrees := by
    unfold RoundsToNearestTenth landingDisplacementAngleDegrees
    rw [hAngle]
    norm_num [AnswerChoice.angleDegrees] at degree_lower degree_upper ⊢
    rw [abs_le]
    constructor
    · linarith only [degree_lower]
    · linarith only [degree_upper]
  have hNearest :
      IsNearestAnswerChoice
        (landingDisplacementAngleDegrees setup) .C := by
    unfold IsNearestAnswerChoice
    unfold RoundsToNearestTenth at hRound
    norm_num [AnswerChoice.angleDegrees] at hRound
    rw [abs_le] at hRound
    intro other hne
    cases other with
    | C => exact (hne rfl).elim
    | A =>
        simp only [AnswerChoice.angleDegrees]
        have hr :
            0 <
              landingDisplacementAngleDegrees setup - 132 / 5 := by
          nlinarith only [hRound.1]
        rw [abs_of_pos hr, abs_lt]
        constructor <;> nlinarith only [hRound.1, hRound.2]
    | B =>
        simp only [AnswerChoice.angleDegrees]
        have hr :
            0 <
              landingDisplacementAngleDegrees setup - 144 / 5 := by
          nlinarith only [hRound.1]
        rw [abs_of_pos hr, abs_lt]
        constructor <;> nlinarith only [hRound.1, hRound.2]
    | D =>
        simp only [AnswerChoice.angleDegrees]
        have hr :
            landingDisplacementAngleDegrees setup - 181 / 5 < 0 := by
          nlinarith only [hRound.2]
        rw [abs_of_neg hr, abs_lt]
        constructor <;> nlinarith only [hRound.1, hRound.2]
  exact ⟨hIncline, hAngle, hRound, hNearest⟩

end PhyXMiniProblems.ProblemPhyXMini0744
