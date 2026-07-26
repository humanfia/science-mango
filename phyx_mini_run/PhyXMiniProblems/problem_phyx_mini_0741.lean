import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0741

open Dimension

/-!
# Launch direction of a projectile thrown from a roof

A ball leaves the left roof edge of a building, travels to the left, and
reaches the ground after `1.50 s` at horizontal distance `d = 25.0 m` from
the building.  At impact its velocity points down and left at `60.0 degrees`
to the horizontal.  The supplied figure labels the roof height by `h`, the
horizontal range by `d`, and the impact angle by `theta`.

Lengths, durations, velocity components, and acceleration are represented by
dimensionful Physlib quantities.  Real numbers occur at explicitly named SI
readout boundaries and for dimensionless radian angles.  Constant-gravity
kinematics is an assumption on an independent trajectory; the requested
initial angle is not stored in the setup.  The printed values are retained in
an answer table, but no premise selects C or asserts agreement with `40.4
degrees`; that agreement occurs only in the target.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical length, independent of the chosen unit system. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical Cartesian length component. -/
abbrev SignedLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev Duration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed physical velocity component. -/
abbrev VelocityComponent : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative physical length in SI meters. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed Cartesian length component in SI meters. -/
def signedLengthInMeters (length : SignedLength) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical duration in SI seconds. -/
def durationInSeconds (duration : Duration) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a signed velocity component in SI meters per second. -/
def velocityInMetersPerSecond (velocity : VelocityComponent) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Read an acceleration magnitude in SI meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Convert a dimensionless degree readout to a radian readout. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Projectile, coordinates, and primary-figure vocabulary -/

/-- The horizontal and vertical axes of the planar projectile diagram. -/
inductive PlanarAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical objects and geometrical marks visible in image `741.png`. -/
inductive FigureObject where
  | building
  | roofEdge
  | horizontalGround
  | impactVelocityArrow
  | impactDirectionLine
  | impactAngleArc
  deriving DecidableEq, Fintype, Repr

/-- The three symbolic labels visible in the supplied projectile figure. -/
inductive FigureLabel where
  | roofHeightH
  | horizontalDistanceD
  | impactAngleTheta
  deriving DecidableEq, Fintype, Repr

/--
An independent planar trajectory.  Its argument is elapsed time measured in
seconds from launch; its values remain dimensionful position and velocity
components rather than untyped scalar aliases.
-/
structure PlanarProjectileTrajectory where
  positionAtElapsedSeconds : ℝ → PlanarAxis → SignedLength
  velocityAtElapsedSeconds : ℝ → PlanarAxis → VelocityComponent

/--
Literal labels and spatial relations transcribed from the primary image.
The bitmap names the unknown height and the given distance and impact angle,
but contains no numerical value for the requested launch angle.
-/
structure SuppliedRoofProjectileFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  heightLabelH : LengthMagnitude
  distanceLabelD : LengthMagnitude
  impactAngleLabelThetaRadians : ℝ
  distanceLineRunsAlongHorizontalGround : Bool
  heightLineIsVerticalBesideBuilding : Bool
  thetaIsBetweenImpactDirectionAndHorizontal : Bool
  impactVelocityArrowPointsDownAndLeft : Bool
  containsNumericalLaunchAngleAnswer : Bool

/--
The independent physical quantities in the roof-projectile experiment.
Neither the trajectory nor any setup field is defined from an answer choice.
-/
structure RoofProjectileSetup where
  roofHeightH : LengthMagnitude
  horizontalDistanceD : LengthMagnitude
  flightDuration : Duration
  gravitationalAcceleration : AccelerationMagnitude
  impactAngleThetaRadians : ℝ
  trajectory : PlanarProjectileTrajectory
  figure : SuppliedRoofProjectileFigure

/-! ## Coordinate and direction readouts -/

/-- Horizontal position in meters at the stated elapsed time in seconds. -/
def horizontalPositionMeters (setup : RoofProjectileSetup)
    (elapsedSeconds : ℝ) : ℝ :=
  signedLengthInMeters
    (setup.trajectory.positionAtElapsedSeconds elapsedSeconds .horizontal)

/-- Vertical position in meters at the stated elapsed time in seconds. -/
def verticalPositionMeters (setup : RoofProjectileSetup)
    (elapsedSeconds : ℝ) : ℝ :=
  signedLengthInMeters
    (setup.trajectory.positionAtElapsedSeconds elapsedSeconds .vertical)

/-- Horizontal velocity in meters per second at the stated elapsed time. -/
def horizontalVelocityMetersPerSecond (setup : RoofProjectileSetup)
    (elapsedSeconds : ℝ) : ℝ :=
  velocityInMetersPerSecond
    (setup.trajectory.velocityAtElapsedSeconds elapsedSeconds .horizontal)

/-- Vertical velocity in meters per second at the stated elapsed time. -/
def verticalVelocityMetersPerSecond (setup : RoofProjectileSetup)
    (elapsedSeconds : ℝ) : ℝ :=
  velocityInMetersPerSecond
    (setup.trajectory.velocityAtElapsedSeconds elapsedSeconds .vertical)

/--
The acute angle between a nonvertical velocity and the horizontal, expressed
in radians.  Absolute component magnitudes make this independent of whether
the depicted velocity points left or right, above or below the horizontal.
-/
def acuteVelocityAngleRadians (setup : RoofProjectileSetup)
    (elapsedSeconds : ℝ) : ℝ :=
  Real.arctan
    (|verticalVelocityMetersPerSecond setup elapsedSeconds| /
      |horizontalVelocityMetersPerSecond setup elapsedSeconds|)

/-! ## Scenario, source readouts, figure data, and governing laws -/

/--
The roof edge is the coordinate origin horizontally, the ground is `y = 0`,
and the impact point lies to the left by the positive distance `d`.
-/
structure MatchesRoofProjectileScenario (setup : RoofProjectileSetup) : Prop where
  launchAtBuildingEdge : horizontalPositionMeters setup 0 = 0
  launchAtRoofHeight :
    verticalPositionMeters setup 0 = lengthInMeters setup.roofHeightH
  impactLeftOfBuilding :
    horizontalPositionMeters setup (durationInSeconds setup.flightDuration) =
      -lengthInMeters setup.horizontalDistanceD
  impactOnGround :
    verticalPositionMeters setup (durationInSeconds setup.flightDuration) = 0
  launchVelocityPointsLeft : horizontalVelocityMetersPerSecond setup 0 < 0
  impactVelocityPointsLeft :
    horizontalVelocityMetersPerSecond setup
      (durationInSeconds setup.flightDuration) < 0
  impactVelocityPointsDown :
    verticalVelocityMetersPerSecond setup
      (durationInSeconds setup.flightDuration) < 0

/--
Numerical data supplied by the prose: `1.50 s`, `25.0 m`, and an impact angle
of `60.0 degrees`.  No initial-angle value or answer choice is included.
-/
structure MatchesRoofProjectileReadouts (setup : RoofProjectileSetup) : Prop where
  flightDurationSeconds : durationInSeconds setup.flightDuration = 3 / 2
  horizontalDistanceMeters : lengthInMeters setup.horizontalDistanceD = 25
  impactAngleSixtyDegrees :
    setup.impactAngleThetaRadians = degreesToRadians 60
  impactVelocityHasLabelledAngle :
    acuteVelocityAngleRadians setup
      (durationInSeconds setup.flightDuration) =
        setup.impactAngleThetaRadians

/-- Standard near-Earth gravitational acceleration used by the problem. -/
structure UsesStandardNearEarthGravity (setup : RoofProjectileSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 49 / 5

/-- Objects, labels, and orientation relations read from image `741.png`. -/
structure MatchesSuppliedRoofProjectileFigure
    (setup : RoofProjectileSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  heightLabelDenotesRoofHeight : setup.figure.heightLabelH = setup.roofHeightH
  distanceLabelDenotesHorizontalRange :
    setup.figure.distanceLabelD = setup.horizontalDistanceD
  thetaLabelDenotesImpactAngle :
    setup.figure.impactAngleLabelThetaRadians = setup.impactAngleThetaRadians
  distanceLineIsHorizontal :
    setup.figure.distanceLineRunsAlongHorizontalGround = true
  heightLineIsVertical : setup.figure.heightLineIsVerticalBesideBuilding = true
  thetaIsMeasuredFromHorizontal :
    setup.figure.thetaIsBetweenImpactDirectionAndHorizontal = true
  arrowPointsDownAndLeft :
    setup.figure.impactVelocityArrowPointsDownAndLeft = true
  figureDoesNotContainNumericalLaunchAnswer :
    setup.figure.containsNumericalLaunchAngleAnswer = false

/-- Positivity and acute-angle conditions selecting the physical branch. -/
structure HasPhysicalRoofProjectileParameters
    (setup : RoofProjectileSetup) : Prop where
  roofHeightPositive : 0 < lengthInMeters setup.roofHeightH
  horizontalDistancePositive : 0 < lengthInMeters setup.horizontalDistanceD
  flightDurationPositive : 0 < durationInSeconds setup.flightDuration
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  impactAngleAcute : setup.impactAngleThetaRadians ∈ Set.Ioo 0 (Real.pi / 2)

/--
Uniform downward-gravity kinematics in SI component readouts.  The four
relations are the general constant-acceleration laws for every elapsed time;
they contain no solved initial angle or displayed answer value.
-/
structure SatisfiesUniformGravityKinematics
    (setup : RoofProjectileSetup) : Prop where
  horizontalVelocityConstant : ∀ elapsedSeconds : ℝ,
    horizontalVelocityMetersPerSecond setup elapsedSeconds =
      horizontalVelocityMetersPerSecond setup 0
  verticalVelocityEvolution : ∀ elapsedSeconds : ℝ,
    verticalVelocityMetersPerSecond setup elapsedSeconds =
      verticalVelocityMetersPerSecond setup 0 -
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration * elapsedSeconds
  horizontalPositionEvolution : ∀ elapsedSeconds : ℝ,
    horizontalPositionMeters setup elapsedSeconds =
      horizontalPositionMeters setup 0 +
        horizontalVelocityMetersPerSecond setup 0 * elapsedSeconds
  verticalPositionEvolution : ∀ elapsedSeconds : ℝ,
    verticalPositionMeters setup elapsedSeconds =
      verticalPositionMeters setup 0 +
        verticalVelocityMetersPerSecond setup 0 * elapsedSeconds -
          (1 / 2 : ℝ) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration * elapsedSeconds ^ 2

/-! ## Displayed choices and target -/

/-- Labels of the four launch-angle choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Degree value printed beside each answer label. -/
def displayedLaunchAngleDegrees : AnswerChoice → ℝ
  | .A => 38.2
  | .B => 39.6
  | .C => 40.4
  | .D => 42.4

/-- Agreement with an angle displayed to the nearest tenth of a degree. -/
def RoundsToDisplayedTenthDegree
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |angleRadians - degreesToRadians (displayedLaunchAngleDegrees choice)| <
    degreesToRadians 0.05

/-- A choice uniquely matches the physical angle at the displayed precision. -/
def IsUniqueRoundedLaunchAngleAnswer
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedTenthDegree angleRadians choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedTenthDegree angleRadians other → other = choice

/--
For the depicted constant-gravity flight, the initial velocity makes an acute
angle that rounds to `40.4 degrees` relative to the horizontal.  Thus C is the
unique answer at the precision displayed in the options.

Blueprint: `thm:physics:phyx_mini_0741:target`.
-/
theorem problem_phyx_mini_0741
    (setup : RoofProjectileSetup)
    (scenario : MatchesRoofProjectileScenario setup)
    (readouts : MatchesRoofProjectileReadouts setup)
    (gravity : UsesStandardNearEarthGravity setup)
    (figure : MatchesSuppliedRoofProjectileFigure setup)
    (physical : HasPhysicalRoofProjectileParameters setup)
    (kinematics : SatisfiesUniformGravityKinematics setup) :
    IsUniqueRoundedLaunchAngleAnswer
      (acuteVelocityAngleRadians setup 0) .C := by
  have hHorizontalPosition :=
    kinematics.horizontalPositionEvolution
      (durationInSeconds setup.flightDuration)
  have hInitialHorizontalVelocity :
      horizontalVelocityMetersPerSecond setup 0 = -(50 / 3 : ℝ) := by
    have hImpactPosition := scenario.impactLeftOfBuilding
    rw [scenario.launchAtBuildingEdge,
      readouts.flightDurationSeconds] at hHorizontalPosition
    rw [readouts.flightDurationSeconds,
      readouts.horizontalDistanceMeters] at hImpactPosition
    nlinarith [hImpactPosition, hHorizontalPosition]
  have hImpactHorizontalVelocity :
      horizontalVelocityMetersPerSecond setup
          (durationInSeconds setup.flightDuration) = -(50 / 3 : ℝ) := by
    rw [kinematics.horizontalVelocityConstant]
    exact hInitialHorizontalVelocity
  have hImpactAngle :
      Real.arctan
          (|verticalVelocityMetersPerSecond setup
              (durationInSeconds setup.flightDuration)| /
            |horizontalVelocityMetersPerSecond setup
              (durationInSeconds setup.flightDuration)|) =
        Real.pi / 3 := by
    have h := readouts.impactVelocityHasLabelledAngle
    rw [readouts.impactAngleSixtyDegrees] at h
    rw [acuteVelocityAngleRadians, degreesToRadians] at h
    convert h using 1 <;> ring
  have hImpactRatio :
      |verticalVelocityMetersPerSecond setup
          (durationInSeconds setup.flightDuration)| /
        |horizontalVelocityMetersPerSecond setup
          (durationInSeconds setup.flightDuration)| =
          Real.sqrt 3 := by
    apply Real.arctan_injective
    rw [hImpactAngle, Real.arctan_sqrt_three]
  have hImpactVerticalVelocity :
      verticalVelocityMetersPerSecond setup
          (durationInSeconds setup.flightDuration) =
        -(50 / 3 : ℝ) * Real.sqrt 3 := by
    rw [abs_of_neg scenario.impactVelocityPointsDown,
      abs_of_neg scenario.impactVelocityPointsLeft,
      hImpactHorizontalVelocity] at hImpactRatio
    norm_num at hImpactRatio
    nlinarith
  have hVerticalVelocity :=
    kinematics.verticalVelocityEvolution
      (durationInSeconds setup.flightDuration)
  have hInitialVerticalVelocity :
      verticalVelocityMetersPerSecond setup 0 =
        147 / 10 - (50 / 3 : ℝ) * Real.sqrt 3 := by
    rw [hImpactVerticalVelocity, readouts.flightDurationSeconds,
      gravity.gravityMetersPerSecondSquared] at hVerticalVelocity
    nlinarith
  have hSqrtThreeSquared : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtThreeNonnegative : 0 ≤ Real.sqrt 3 :=
    Real.sqrt_nonneg 3
  have hSqrtThreeGreaterThanOne : (1 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hInitialVerticalVelocityNegative :
      verticalVelocityMetersPerSecond setup 0 < 0 := by
    rw [hInitialVerticalVelocity]
    nlinarith
  have hLaunchAngle :
      acuteVelocityAngleRadians setup 0 =
        Real.arctan (Real.sqrt 3 - 441 / 500) := by
    rw [acuteVelocityAngleRadians,
      abs_of_neg hInitialVerticalVelocityNegative,
      abs_of_neg scenario.launchVelocityPointsLeft,
      hInitialHorizontalVelocity, hInitialVerticalVelocity]
    congr 1
    ring
  rw [hLaunchAngle]
  clear hLaunchAngle hInitialVerticalVelocityNegative
    hSqrtThreeGreaterThanOne hSqrtThreeNonnegative hSqrtThreeSquared
    hInitialVerticalVelocity hVerticalVelocity hImpactVerticalVelocity
    hImpactRatio hImpactAngle hImpactHorizontalVelocity
    hInitialHorizontalVelocity hHorizontalPosition
  clear figure physical scenario readouts gravity kinematics setup
  let q : ℝ := Real.sqrt 3 - 441 / 500
  let x : ℝ := (1 - q) / (1 + q)
  change IsUniqueRoundedLaunchAngleAnswer (Real.arctan q) .C
  have hSqrtThreeLower :
      (173205 / 100000 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtThreeUpper :
      Real.sqrt 3 < (86603 / 50000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hQPositive : 0 < q := by
    dsimp [q]
    nlinarith
  have hQLessThanOne : q < 1 := by
    dsimp [q]
    nlinarith
  have hOnePlusQPositive : 0 < 1 + q := by linarith
  have hXLower : (81 / 1000 : ℝ) < x := by
    dsimp [x]
    rw [lt_div_iff₀ hOnePlusQPositive]
    dsimp [q] at *
    nlinarith
  have hXUpper : x < (8106 / 100000 : ℝ) := by
    dsimp [x]
    rw [div_lt_iff₀ hOnePlusQPositive]
    dsimp [q] at *
    nlinarith
  have hXPositive : 0 < x := by nlinarith
  have hXLessThanOne : x < 1 := by nlinarith
  have hQXLessThanOne : q * x < 1 := by
    dsimp [x]
    rw [← mul_div_assoc, div_lt_iff₀ hOnePlusQPositive]
    nlinarith [sq_nonneg q]
  have hOnePlusQSquaredPositive : 0 < 1 + q ^ 2 := by
    nlinarith [sq_nonneg q]
  have hArctanComplement :
      Real.arctan q + Real.arctan x = Real.pi / 4 := by
    rw [Real.arctan_add hQXLessThanOne, ← Real.arctan_one]
    congr 1
    dsimp [x]
    field_simp [ne_of_gt hOnePlusQPositive,
      ne_of_gt hOnePlusQSquaredPositive]
    have hDenominatorPositive :
        0 < 1 + q - q * (1 - q) := by
      nlinarith [sq_nonneg q]
    rw [div_eq_iff (ne_of_gt hDenominatorPositive)]
    ring
  have r_lt_arctan_of_poly {r y : ℝ}
      (hr0 : 0 < r) (hr1 : r < 1) (hy0 : 0 ≤ y)
      (hpoly :
        r - r ^ 3 / 6 + r ^ 4 * (5 / 96) <
          y * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96))) :
      r < Real.arctan y := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsinUpper :
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hs |>.2]
    have hcosLower :
        1 - r ^ 2 / 2 - r ^ 4 * (5 / 96) ≤ Real.cos r := by
      linarith [abs_le.mp hc |>.1]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPositive : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : Real.tan r < y := by
      rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcosPositive]
      calc
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := hsinUpper
        _ < y * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96)) := hpoly
        _ ≤ y * Real.cos r :=
          mul_le_mul_of_nonneg_left hcosLower hy0
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan
  have arctan_lt_r_of_poly {y r : ℝ}
      (hr0 : 0 < r) (hr1 : r < 1) (hy0 : 0 ≤ y)
      (hpoly :
        y * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) <
          r - r ^ 3 / 6 - r ^ 4 * (5 / 96)) :
      Real.arctan y < r := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsinLower :
        r - r ^ 3 / 6 - r ^ 4 * (5 / 96) ≤ Real.sin r := by
      linarith [abs_le.mp hs |>.1]
    have hcosUpper :
        Real.cos r ≤ 1 - r ^ 2 / 2 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hc |>.2]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPositive : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : y < Real.tan r := by
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcosPositive]
      calc
        y * Real.cos r ≤ y * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) :=
          mul_le_mul_of_nonneg_left hcosUpper hy0
        _ < r - r ^ 3 / 6 - r ^ 4 * (5 / 96) := hpoly
        _ ≤ Real.sin r := hsinLower
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan
  have hCorrectionLower : (2 / 25 : ℝ) < Real.arctan x := by
    have hpoly :
        (2 / 25 : ℝ) - (2 / 25 : ℝ) ^ 3 / 6 +
            (2 / 25 : ℝ) ^ 4 * (5 / 96) <
          x * (1 - (2 / 25 : ℝ) ^ 2 / 2 -
            (2 / 25 : ℝ) ^ 4 * (5 / 96)) := by
      norm_num
      linarith only [hXLower]
    exact r_lt_arctan_of_poly (by norm_num) (by norm_num)
      hXPositive.le hpoly
  have hCorrectionUpper :
      Real.arctan x < (8107 / 100000 : ℝ) := by
    have hpoly :
        x * (1 - (8107 / 100000 : ℝ) ^ 2 / 2 +
            (8107 / 100000 : ℝ) ^ 4 * (5 / 96)) <
          (8107 / 100000 : ℝ) -
            (8107 / 100000 : ℝ) ^ 3 / 6 -
            (8107 / 100000 : ℝ) ^ 4 * (5 / 96) := by
      norm_num
      linarith only [hXUpper]
    exact arctan_lt_r_of_poly (by norm_num) (by norm_num)
      hXPositive.le hpoly
  have hArctanFifthLower :
      (19729 / 100000 : ℝ) < Real.arctan (1 / 5 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hArctanFifthUpper :
      Real.arctan (1 / 5 : ℝ) < (79 / 400 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hArctan239Upper :
      Real.arctan (1 / 239 : ℝ) < (1 / 239 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hArctan239Positive :
      0 < Real.arctan (1 / 239 : ℝ) :=
    Real.arctan_pos.mpr (by norm_num)
  have hMachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [inv_eq_one_div] at hMachin
  have hPiLower : (3139 / 1000 : ℝ) < Real.pi := by
    linarith only [hMachin, hArctanFifthLower, hArctan239Upper]
  have hPiUpper : Real.pi < (79 / 25 : ℝ) := by
    linarith only [hMachin, hArctanFifthUpper, hArctan239Positive]
  have hCorrectionAngleLower :
      91 * Real.pi / 3600 < Real.arctan x := by
    linarith only [hPiUpper, hCorrectionLower]
  have hCorrectionAngleUpper :
      Real.arctan x < 31 * Real.pi / 1200 := by
    linarith only [hPiLower, hCorrectionUpper]
  have hAngleLower :
      269 * Real.pi / 1200 < Real.arctan q := by
    linarith only [hArctanComplement, hCorrectionAngleUpper]
  have hAngleUpper :
      Real.arctan q < 809 * Real.pi / 3600 := by
    linarith only [hArctanComplement, hCorrectionAngleLower]
  unfold IsUniqueRoundedLaunchAngleAnswer
  constructor
  · unfold RoundsToDisplayedTenthDegree
    rw [abs_lt]
    norm_num [displayedLaunchAngleDegrees, degreesToRadians]
    constructor
    · linarith only [hAngleLower]
    · linarith only [hAngleUpper]
  · intro other hOther
    cases other with
    | A =>
        unfold RoundsToDisplayedTenthDegree at hOther
        rw [abs_lt] at hOther
        have hOtherUpper := hOther.2
        change Real.arctan q - (38.2 : ℝ) * Real.pi / 180 <
            (0.05 : ℝ) * Real.pi / 180 at hOtherUpper
        linarith only [hOtherUpper, hAngleLower, Real.pi_pos]
    | B =>
        unfold RoundsToDisplayedTenthDegree at hOther
        rw [abs_lt] at hOther
        have hOtherUpper := hOther.2
        change Real.arctan q - (39.6 : ℝ) * Real.pi / 180 <
            (0.05 : ℝ) * Real.pi / 180 at hOtherUpper
        linarith only [hOtherUpper, hAngleLower, Real.pi_pos]
    | C => rfl
    | D =>
        unfold RoundsToDisplayedTenthDegree at hOther
        rw [abs_lt] at hOther
        have hOtherLower := hOther.1
        change -((0.05 : ℝ) * Real.pi / 180) <
            Real.arctan q - (42.4 : ℝ) * Real.pi / 180 at hOtherLower
        have hDLowerRaw :=
          add_lt_add_right hOtherLower ((42.4 : ℝ) * Real.pi / 180)
        have hDLower :
            847 * Real.pi / 3600 < Real.arctan q := by
          convert hDLowerRaw using 1 <;> ring
        have hImpossible :
            847 * Real.pi / 3600 < 809 * Real.pi / 3600 :=
          hDLower.trans hAngleUpper
        have hReverse :
            809 * Real.pi / 3600 < 847 * Real.pi / 3600 := by
          nlinarith only [Real.pi_pos]
        exact False.elim ((not_lt_of_ge hReverse.le) hImpossible)

end PhyXMiniProblems.ProblemPhyXMini0741
