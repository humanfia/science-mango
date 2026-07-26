import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Speed

/-!
# Ocean-wave refraction at an abrupt depth change

This file models problem `phyx_mini_0174`.  Ocean waves travel from deep
water into shallower water across the horizontal depth-change boundary shown
in the source figure.  The dashed vertical line is the boundary normal, and
the displayed angles `thetaOne` and `thetaTwo` are measured from that normal.

Water depths and propagation speeds are dimensionful Physlib quantities.
The real scalars below are only SI readouts, angle representatives, and
dimensionless trigonometric values.  Diagram directions are nonzero vectors,
so the propagation arrows, interface lines, normal, and wavefronts retain
their distinct geometric roles.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0174

open Dimension

/-! ## Dimensionful quantities and angular readouts -/

/-- A physical water depth carrying the dimension of length. -/
abbrev WaterDepth : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical water depth in metres. -/
def depthInMeters (depth : WaterDepth) : ℝ :=
  ((depth UnitChoices.SI).val : ℝ)

/-- Read a physical propagation speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Interpret a displayed degree value as a real angle. -/
def angleOfDegrees (degreeValue : ℝ) : Real.Angle :=
  ((degreeValue * Real.pi / 180 : ℝ) : Real.Angle)

/-- The principal real representative of an angle, converted to degrees. -/
def angleInDegrees (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-! ## Physical and figure roles -/

/-- The two constant-depth water regions separated in the figure. -/
inductive WaterRegion where
  | deepWater
  | shallowWater
  deriving DecidableEq, Repr

/-- The incident and transmitted portions of the wave path. -/
inductive WaveSegment where
  | incidentInDeepWater
  | transmittedInShallowWater
  deriving DecidableEq, Repr

/-- The two approximately horizontal physical lines visible in the figure. -/
inductive FigureBoundary where
  | depthChangeBoundary
  | shoreline
  deriving DecidableEq, Repr

/-- Idealizations for how water depth varies on crossing the named boundary. -/
inductive DepthTransitionModel where
  | abruptStep
  | gradualChange
  deriving DecidableEq, Repr

/-- The homogeneous water region occupied by each depicted wave segment. -/
def WaveSegment.region : WaveSegment → WaterRegion
  | .incidentInDeepWater => .deepWater
  | .transmittedInShallowWater => .shallowWater

/-- The two-dimensional Euclidean plane of the overhead diagram. -/
abbrev DiagramPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- A geometric direction is represented by a nonzero diagram-plane vector. -/
abbrev DiagramDirection : Type := RayVector ℝ DiagramPlane

/-- The undirected angle between two nonzero geometric directions. -/
def angleBetweenDirections
    (first second : DiagramDirection) : Real.Angle :=
  ((InnerProductGeometry.angle first.1 second.1 : ℝ) : Real.Angle)

/--
The physical quantities and named geometry in the ocean-wave refraction
scenario.  In particular, `thetaTwo` is stored as unconstrained physical data;
its numerical value is not built into this structure.
-/
structure OceanWaveRefractionSetup where
  /-- Depth in each of the deep- and shallow-water regions. -/
  waterDepth : WaterRegion → WaterDepth
  /-- The abrupt-versus-gradual idealization of the depth transition. -/
  depthTransition : DepthTransitionModel
  /-- Magnitude of the wave propagation speed in each water region. -/
  propagationSpeed : WaterRegion → DimSpeed
  /-- Propagation-arrow direction of each wave-path segment. -/
  propagationDirection : WaveSegment → DiagramDirection
  /-- Common direction of the parallel wavefronts in each segment. -/
  wavefrontDirection : WaveSegment → DiagramDirection
  /-- Tangent direction of the depth boundary and shoreline. -/
  boundaryDirection : FigureBoundary → DiagramDirection
  /-- Dashed normal direction through the depth-change boundary. -/
  depthBoundaryNormalDirection : DiagramDirection
  /-- Figure label `theta_1`, measured in deep water from the normal. -/
  thetaOne : Real.Angle
  /-- Figure label `theta_2`, measured in shallow water from the normal. -/
  thetaTwo : Real.Angle

/-- An angle lies on the nonnegative acute branch used by the figure. -/
def IsPhysicalAcuteAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal ≤ Real.pi / 2

/-!
Positivity, depth ordering, and the principal angular branch.  These premises
select the physical solution of the sine law without assigning a numerical
value to `thetaTwo`.
-/
structure HasPhysicalParameters
    (setup : OceanWaveRefractionSetup) : Prop where
  depthPositive :
    ∀ region, 0 < depthInMeters (setup.waterDepth region)
  shallowIsLessDeep :
    depthInMeters (setup.waterDepth .shallowWater) <
      depthInMeters (setup.waterDepth .deepWater)
  speedPositive :
    ∀ region, 0 < speedInMetersPerSecond (setup.propagationSpeed region)
  thetaOnePhysical : IsPhysicalAcuteAngle setup.thetaOne
  thetaTwoPhysical : IsPhysicalAcuteAngle setup.thetaTwo

/-!
Numerical and qualitative information stated in the problem: an abrupt depth
change, a `4.0 m/s` incident wave, a `3.0 m/s` transmitted wave, and
`theta_1 = 30 degrees`.  No value of `thetaTwo` occurs here.
-/
structure MatchesProblemReadouts
    (setup : OceanWaveRefractionSetup) : Prop where
  abruptDepthChange : setup.depthTransition = .abruptStep
  deepWaterSpeed :
    setup.propagationSpeed .deepWater =
      (4 : NNReal) • DimSpeed.oneMeterPerSecond
  shallowWaterSpeed :
    setup.propagationSpeed .shallowWater =
      (3 : NNReal) • DimSpeed.oneMeterPerSecond
  thetaOneReadout : setup.thetaOne = angleOfDegrees 30

/-!
Geometric information read from the primary image.  The depth boundary and
shoreline are parallel, the dashed line is normal to the depth boundary, each
drawn wavefront is perpendicular to its propagation direction, and the two
theta labels are the corresponding angles from that same normal.  These
relations interpret `thetaTwo` geometrically but do not prescribe its value.
-/
structure MatchesSuppliedFigure
    (setup : OceanWaveRefractionSetup) : Prop where
  depthBoundaryParallelToShoreline :
    angleBetweenDirections
        (setup.boundaryDirection .depthChangeBoundary)
        (setup.boundaryDirection .shoreline) =
      angleOfDegrees 0
  normalPerpendicularToDepthBoundary :
    angleBetweenDirections
        setup.depthBoundaryNormalDirection
        (setup.boundaryDirection .depthChangeBoundary) =
      angleOfDegrees 90
  wavefrontPerpendicularToPropagation :
    ∀ segment,
      angleBetweenDirections
          (setup.wavefrontDirection segment)
          (setup.propagationDirection segment) =
        angleOfDegrees 90
  thetaOneFromDirections :
    setup.thetaOne =
      angleBetweenDirections
        (setup.propagationDirection .incidentInDeepWater)
        setup.depthBoundaryNormalDirection
  thetaTwoFromDirections :
    setup.thetaTwo =
      angleBetweenDirections
        (setup.propagationDirection .transmittedInShallowWater)
        setup.depthBoundaryNormalDirection

/-!
The wave form of Snell's law at a depth boundary,

`sin(theta_1) / v_1 = sin(theta_2) / v_2`,

written without division as
`sin(theta_1) * v_2 = sin(theta_2) * v_1` using SI speed readouts.
Mathlib and Physlib provide the angle, sine, and dimensionful speed objects,
but no declaration specialized to this water-wave refraction law.
-/
def ObeysWaveSnellLaw (setup : OceanWaveRefractionSetup) : Prop :=
  Real.Angle.sin setup.thetaOne *
      speedInMetersPerSecond (setup.propagationSpeed .shallowWater) =
    Real.Angle.sin setup.thetaTwo *
      speedInMetersPerSecond (setup.propagationSpeed .deepWater)

/-! ## Derived angle and displayed answer -/

/--
The given speeds and `30 degree` incident angle reduce the wave Snell law to
`sin(theta_2) = 3/8`.
-/
lemma thetaTwo_sine_eq_three_eighths
    (setup : OceanWaveRefractionSetup)
    (hProblem : MatchesProblemReadouts setup)
    (hSnell : ObeysWaveSnellLaw setup) :
    Real.Angle.sin setup.thetaTwo = (3 / 8 : ℝ) := by
  rcases hProblem with ⟨_habrupt, hdeep, hshallow, htheta⟩
  unfold ObeysWaveSnellLaw at hSnell
  rw [hdeep, hshallow, htheta] at hSnell
  norm_num [speedInMetersPerSecond, angleOfDegrees,
    Dimensionful.smul_apply] at hSnell
  have hangle : (30 : ℝ) * Real.pi / 180 = Real.pi / 6 := by
    ring
  rw [hangle, Real.sin_pi_div_six] at hSnell
  norm_num at hSnell ⊢
  nlinarith only [hSnell]

/-- Labels of the four answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The angle in degrees printed beside each displayed answer label. -/
def AnswerChoice.directionDegrees : AnswerChoice → ℝ
  | .A => 30
  | .B => 418 / 10
  | .C => 22
  | .D => 50

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed angle rounded to the nearest tenth of a degree. -/
def MatchesDisplayedAnswer
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |angleInDegrees angle - choice.directionDegrees| ≤ 1 / 20

/-- A displayed answer is the unique candidate within the rounding tolerance. -/
def IsUniqueMatchingDisplayedAnswer
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedAnswer angle choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedAnswer angle other → other = choice

/-!
The shallow-water angle is exactly `arcsin(3/8)`, approximately `22.0` degrees,
and hence uniquely selects answer C.

This formalizes `thm:physics:phyx_mini_0174:target`.  Neither the exact
`arcsin(3/8)` result nor the `22.0 degree` answer appears in the physical,
problem-readout, figure, or Snell-law premises.
-/
theorem problem_phyx_mini_0174
    (setup : OceanWaveRefractionSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hProblem : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hSnell : ObeysWaveSnellLaw setup) :
    setup.thetaTwo = ((Real.arcsin (3 / 8 : ℝ) : ℝ) : Real.Angle) ∧
      IsUniqueMatchingDisplayedAnswer setup.thetaTwo .C := by
  have hsinAngle :
      Real.Angle.sin setup.thetaTwo = (3 / 8 : ℝ) :=
    thetaTwo_sine_eq_three_eighths setup hProblem hSnell
  have hsinReal :
      Real.sin setup.thetaTwo.toReal = (3 / 8 : ℝ) := by
    rw [Real.Angle.sin_toReal]
    exact hsinAngle
  have hthetaReal :
      setup.thetaTwo.toReal = Real.arcsin (3 / 8 : ℝ) := by
    symm
    rw [← hsinReal]
    exact Real.arcsin_sin
      (by
        rcases hPhysical.thetaTwoPhysical with ⟨h_nonneg, _h_le⟩
        nlinarith only [h_nonneg, Real.pi_pos])
      hPhysical.thetaTwoPhysical.2
  have hthetaAngle :
      setup.thetaTwo =
        ((Real.arcsin (3 / 8 : ℝ) : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_toReal setup.thetaTwo, hthetaReal]
  refine ⟨hthetaAngle, ?_⟩
  have hPiBounds : (3 : ℝ) < Real.pi ∧ Real.pi < 16 / 5 := by
    have hsinHalf : Real.sin ((1 : ℝ) / 2) < 1 / 2 := by
      have hbound :=
        Real.sin_bound (x := (1 / 2 : ℝ)) (by norm_num)
      rw [abs_le] at hbound
      norm_num at hbound ⊢
      linarith
    have hsinEightFifteenths :
        (1 / 2 : ℝ) < Real.sin ((8 : ℝ) / 15) := by
      have hbound :=
        Real.sin_bound (x := (8 / 15 : ℝ)) (by norm_num)
      rw [abs_le] at hbound
      norm_num at hbound ⊢
      linarith
    have hPiSixMem :
        Real.pi / 6 ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have hHalfMem :
        (1 / 2 : ℝ) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.one_le_pi_div_two]
    have hEightFifteenthsMem :
        (8 / 15 : ℝ) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.one_le_pi_div_two]
    constructor
    · by_contra h
      have hangle : Real.pi / 6 ≤ (1 / 2 : ℝ) := by
        nlinarith only [le_of_not_gt h]
      have hsine :=
        Real.strictMonoOn_sin.monotoneOn
          hPiSixMem hHalfMem hangle
      rw [Real.sin_pi_div_six] at hsine
      linarith only [hsinHalf, hsine]
    · by_contra h
      have hangle : (8 / 15 : ℝ) ≤ Real.pi / 6 := by
        nlinarith only [le_of_not_gt h]
      have hsine :=
        Real.strictMonoOn_sin.monotoneOn
          hEightFifteenthsMem hPiSixMem hangle
      rw [Real.sin_pi_div_six] at hsine
      linarith only [hsinEightFifteenths, hsine]
  rcases hPiBounds with ⟨hPiLower, hPiUpper⟩

  let c : ℝ := Real.sqrt (2 + Real.sqrt 2) / 2
  let q : ℝ := Real.sqrt (2 - Real.sqrt 2) / 2
  have hrootBounds :
      (9238 : ℝ) / 10000 ≤ c ∧ c ≤ (9239 : ℝ) / 10000 ∧
        (3826 : ℝ) / 10000 ≤ q ∧ q ≤ (3827 : ℝ) / 10000 := by
    have hsqrtTwoNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hsqrtTwoSq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrtTwoLower :
        (14142 : ℝ) / 10000 ≤ Real.sqrt 2 := by
      nlinarith only [hsqrtTwoNonneg, hsqrtTwoSq]
    have hsqrtTwoUpper :
        Real.sqrt 2 ≤ (14143 : ℝ) / 10000 := by
      nlinarith only [hsqrtTwoNonneg, hsqrtTwoSq]
    have hcArg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by
      positivity
    have hcNonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have hcSq : (2 * c) ^ 2 = (2 : ℝ) + Real.sqrt 2 := by
      dsimp [c]
      convert Real.sq_sqrt hcArg using 1 <;> ring
    have hqArg : 0 ≤ (2 : ℝ) - Real.sqrt 2 := by
      nlinarith only [hsqrtTwoNonneg, hsqrtTwoSq]
    have hqNonneg : 0 ≤ q := by
      dsimp [q]
      positivity
    have hqSq : (2 * q) ^ 2 = (2 : ℝ) - Real.sqrt 2 := by
      dsimp [q]
      convert Real.sq_sqrt hqArg using 1 <;> ring
    constructor
    · nlinarith only [hsqrtTwoLower, hcNonneg, hcSq]
    constructor
    · nlinarith only [hsqrtTwoUpper, hcNonneg, hcSq]
    constructor
    · nlinarith only [hsqrtTwoUpper, hqNonneg, hqSq]
    · nlinarith only [hsqrtTwoLower, hqNonneg, hqSq]
  rcases hrootBounds with
    ⟨hcLower, hcUpper, hqLower, hqUpper⟩
  have hcNonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    positivity

  let deltaLower : ℝ := 11 * Real.pi / 3600
  have hdeltaLowerNonneg : 0 ≤ deltaLower := by
    dsimp [deltaLower]
    positivity
  have hdeltaLowerLower :
      (11 : ℝ) / 1200 < deltaLower := by
    dsimp [deltaLower]
    nlinarith only [hPiLower]
  have hdeltaLowerUpper :
      deltaLower < (11 : ℝ) / 1125 := by
    dsimp [deltaLower]
    nlinarith only [hPiUpper]
  have hdeltaLowerAbs : |deltaLower| ≤ 1 := by
    rw [abs_of_nonneg hdeltaLowerNonneg]
    nlinarith only [hdeltaLowerUpper]
  have hdeltaLowerCube :
      deltaLower ^ 3 ≤ ((11 : ℝ) / 1125) ^ 3 :=
    pow_le_pow_left₀ hdeltaLowerNonneg hdeltaLowerUpper.le 3
  have hdeltaLowerFourth :
      deltaLower ^ 4 ≤ ((11 : ℝ) / 1125) ^ 4 :=
    pow_le_pow_left₀ hdeltaLowerNonneg hdeltaLowerUpper.le 4
  have hsinDeltaLower :
      (9 : ℝ) / 1000 < Real.sin deltaLower := by
    have hbound :=
      (abs_le.mp (Real.sin_bound hdeltaLowerAbs)).1
    rw [abs_of_nonneg hdeltaLowerNonneg] at hbound
    nlinarith only
      [hbound, hdeltaLowerLower, hdeltaLowerCube,
        hdeltaLowerFourth]
  have hqCosLowerUpper :
      q * Real.cos deltaLower ≤ (3827 : ℝ) / 10000 := by
    calc
      q * Real.cos deltaLower ≤ q * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.cos_le_one deltaLower) hqNonneg
      _ = q := by ring
      _ ≤ (3827 : ℝ) / 10000 := hqUpper
  have hcSinLowerLower :
      (9238 : ℝ) / 10000 * (9 / 1000) <
        c * Real.sin deltaLower := by
    calc
      (9238 : ℝ) / 10000 * (9 / 1000) ≤
          c * (9 / 1000) :=
        mul_le_mul_of_nonneg_right hcLower (by norm_num)
      _ < c * Real.sin deltaLower :=
        mul_lt_mul_of_pos_left hsinDeltaLower
          (by nlinarith only [hcLower])
  have hLowerEndpointSine :
      Real.sin (439 * Real.pi / 3600) < (3 / 8 : ℝ) := by
    have hformula :
        Real.sin (439 * Real.pi / 3600) =
          q * Real.cos deltaLower -
            c * Real.sin deltaLower := by
      rw [show 439 * Real.pi / 3600 =
          Real.pi / 8 - deltaLower by
            dsimp [deltaLower]
            ring,
        Real.sin_sub, Real.sin_pi_div_eight,
        Real.cos_pi_div_eight]
    rw [hformula]
    nlinarith only [hqCosLowerUpper, hcSinLowerLower]

  let deltaUpper : ℝ := Real.pi / 400
  have hdeltaUpperNonneg : 0 ≤ deltaUpper := by
    dsimp [deltaUpper]
    positivity
  have hdeltaUpperPos : 0 < deltaUpper := by
    dsimp [deltaUpper]
    positivity
  have hdeltaUpperUpper :
      deltaUpper < (1 : ℝ) / 125 := by
    dsimp [deltaUpper]
    nlinarith only [hPiUpper]
  have hdeltaUpperAbs : |deltaUpper| ≤ 1 := by
    rw [abs_of_nonneg hdeltaUpperNonneg]
    nlinarith only [hdeltaUpperUpper]
  have hdeltaUpperSq :
      deltaUpper ^ 2 ≤ ((1 : ℝ) / 125) ^ 2 :=
    pow_le_pow_left₀ hdeltaUpperNonneg hdeltaUpperUpper.le 2
  have hdeltaUpperFourth :
      deltaUpper ^ 4 ≤ ((1 : ℝ) / 125) ^ 4 :=
    pow_le_pow_left₀ hdeltaUpperNonneg hdeltaUpperUpper.le 4
  have hcosDeltaUpper :
      (9999 : ℝ) / 10000 < Real.cos deltaUpper := by
    have hbound :=
      (abs_le.mp (Real.cos_bound hdeltaUpperAbs)).1
    rw [abs_of_nonneg hdeltaUpperNonneg] at hbound
    nlinarith only [hbound, hdeltaUpperSq, hdeltaUpperFourth]
  have hsinDeltaUpperSelf :
      Real.sin deltaUpper < deltaUpper := by
    have hbound :=
      le_of_abs_le (Real.sin_bound hdeltaUpperAbs)
    rw [sub_le_iff_le_add',
      abs_of_nonneg hdeltaUpperNonneg] at hbound
    apply hbound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos,
      div_eq_mul_inv (deltaUpper ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num)
      (pow_pos hdeltaUpperPos 3)
    apply pow_le_pow_of_le_one hdeltaUpperNonneg
      (hdeltaUpperUpper.le.trans (by norm_num))
    simp
  have hsinDeltaUpper :
      Real.sin deltaUpper < (1 : ℝ) / 125 :=
    hsinDeltaUpperSelf.trans hdeltaUpperUpper
  have hsinDeltaUpperNonneg : 0 ≤ Real.sin deltaUpper := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi hdeltaUpperNonneg
    dsimp [deltaUpper]
    nlinarith only [Real.pi_pos]
  have hqCosUpperLower :
      (3826 : ℝ) / 10000 * (9999 / 10000) <
        q * Real.cos deltaUpper := by
    calc
      (3826 : ℝ) / 10000 * (9999 / 10000) <
          (3826 : ℝ) / 10000 * Real.cos deltaUpper :=
        mul_lt_mul_of_pos_left hcosDeltaUpper (by norm_num)
      _ ≤ q * Real.cos deltaUpper :=
        mul_le_mul_of_nonneg_right hqLower
          (by nlinarith only [hcosDeltaUpper])
  have hcSinUpperUpper :
      c * Real.sin deltaUpper <
        (9239 : ℝ) / 10000 * (1 / 125) := by
    calc
      c * Real.sin deltaUpper ≤
          (9239 : ℝ) / 10000 * Real.sin deltaUpper :=
        mul_le_mul_of_nonneg_right hcUpper hsinDeltaUpperNonneg
      _ < (9239 : ℝ) / 10000 * (1 / 125) :=
        mul_lt_mul_of_pos_left hsinDeltaUpper (by norm_num)
  have hUpperEndpointSine :
      (3 / 8 : ℝ) < Real.sin (49 * Real.pi / 400) := by
    have hformula :
        Real.sin (49 * Real.pi / 400) =
          q * Real.cos deltaUpper -
            c * Real.sin deltaUpper := by
      rw [show 49 * Real.pi / 400 =
          Real.pi / 8 - deltaUpper by
            dsimp [deltaUpper]
            ring,
        Real.sin_sub, Real.sin_pi_div_eight,
        Real.cos_pi_div_eight]
    rw [hformula]
    nlinarith only [hqCosUpperLower, hcSinUpperUpper]

  have hThreeEighthsMem :
      (3 / 8 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    norm_num
  have hLowerEndpointMem :
      439 * Real.pi / 3600 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos]
  have hUpperEndpointMem :
      49 * Real.pi / 400 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos]
  have hArcsinLower :
      439 * Real.pi / 3600 ≤ Real.arcsin (3 / 8 : ℝ) :=
    (Real.le_arcsin_iff_sin_le
      hLowerEndpointMem hThreeEighthsMem).2 hLowerEndpointSine.le
  have hArcsinUpper :
      Real.arcsin (3 / 8 : ℝ) ≤ 49 * Real.pi / 400 :=
    (Real.arcsin_le_iff_le_sin
      hThreeEighthsMem hUpperEndpointMem).2 hUpperEndpointSine.le
  have hDegreeLower :
      (439 : ℝ) / 20 ≤
        Real.arcsin (3 / 8 : ℝ) * 180 / Real.pi := by
    calc
      (439 : ℝ) / 20 =
          (439 * Real.pi / 3600) * (180 / Real.pi) := by
        field_simp [Real.pi_ne_zero] <;> norm_num
      _ ≤ Real.arcsin (3 / 8 : ℝ) * (180 / Real.pi) :=
        mul_le_mul_of_nonneg_right hArcsinLower (by positivity)
      _ = Real.arcsin (3 / 8 : ℝ) * 180 / Real.pi := by
        ring
  have hDegreeUpper :
      Real.arcsin (3 / 8 : ℝ) * 180 / Real.pi ≤
        (441 : ℝ) / 20 := by
    calc
      Real.arcsin (3 / 8 : ℝ) * 180 / Real.pi =
          Real.arcsin (3 / 8 : ℝ) * (180 / Real.pi) := by
        ring
      _ ≤ (49 * Real.pi / 400) * (180 / Real.pi) :=
        mul_le_mul_of_nonneg_right hArcsinUpper (by positivity)
      _ = (441 : ℝ) / 20 := by
        field_simp [Real.pi_ne_zero] <;> norm_num

  have hMatchesC : MatchesDisplayedAnswer setup.thetaTwo .C := by
    unfold MatchesDisplayedAnswer angleInDegrees
      AnswerChoice.directionDegrees
    rw [hthetaReal, abs_le]
    constructor
    · norm_num
      linarith only [hDegreeLower]
    · norm_num
      linarith only [hDegreeUpper]
  refine ⟨hMatchesC, ?_⟩
  intro other hother
  cases other with
  | A =>
      exfalso
      unfold MatchesDisplayedAnswer angleInDegrees
        AnswerChoice.directionDegrees at hother
      rw [hthetaReal, abs_le] at hother
      norm_num at hother
      linarith only [hDegreeUpper, hother.1]
  | B =>
      exfalso
      unfold MatchesDisplayedAnswer angleInDegrees
        AnswerChoice.directionDegrees at hother
      rw [hthetaReal, abs_le] at hother
      norm_num at hother
      linarith only [hDegreeUpper, hother.1]
  | C =>
      rfl
  | D =>
      exfalso
      unfold MatchesDisplayedAnswer angleInDegrees
        AnswerChoice.directionDegrees at hother
      rw [hthetaReal, abs_le] at hother
      norm_num at hother
      linarith only [hDegreeUpper, hother.1]

end PhyXMiniProblems.ProblemPhyXMini0174
