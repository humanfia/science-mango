import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0742

open Dimension

/-!
# Archer-fish drop reaching an insect at the top of its trajectory

The fish's mouth is the origin of a vertical cross-section.  The water
surface supplies the positive horizontal reference direction.  The insect is
seen at line-of-sight distance `d` and elevation angle `φ`, while the water
drop is launched at an independent angle `θ₀`.  The requested drop reaches
the insect exactly when its vertical velocity vanishes.

Assumption/target split:

* governing laws: straight-line polar geometry and ideal no-drag projectile
  motion in uniform downward gravity;
* previous-part results: none;
* figure/data readouts: the fish, water surface, insect, twig, dashed sight
  line, labels `d` and `φ`, `d = 0.900 m`, `φ = 36.0°`, and the four displayed
  angle choices;
* current target: derive `tan θ₀ = 2 tan φ`, identify the acute launch angle,
  and select the uniquely closest displayed answer `55.5°` (choice C).

Lengths, times, speeds, and accelerations are unit-independent Physlib
quantities.  Real numbers are used only for coherent SI readouts,
dimensionless trigonometric values, and displayed numerical data.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- The physical dimension `L T⁻¹` of a signed velocity component. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension `L T⁻²` of an acceleration magnitude. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed Cartesian position component. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed velocity component. -/
abbrev SignedSpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension ℝ)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed Cartesian length component in SI metres. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a duration in SI seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a speed magnitude in SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a signed velocity component in SI metres per second. -/
def signedSpeedInMetersPerSecond (speed : SignedSpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Read an acceleration magnitude in SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Convert a numerical degree readout to Mathlib's physical angle type. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Primary-figure vocabulary -/

/-- Physical objects and geometric features visible in the supplied bitmap. -/
inductive FigureObject where
  | archerFish
  | waterSurface
  | insect
  | twig
  | straightSightLine
  deriving DecidableEq, Fintype, Repr

/-- Literal or symbolic labels visible in the supplied bitmap. -/
inductive FigureLabel where
  | archerFishText
  | insectOnTwigText
  | sightDistanceD
  | sightAnglePhi
  deriving DecidableEq, Fintype, Repr

/-- Line styles relevant to the drawn line of sight. -/
inductive FigureLineStyle where
  | dashed
  | solid
  deriving DecidableEq, Repr

/-!
Typed evidence transcribed from the primary image.  The marked distance and
angle remain physical quantities.  The last field records that the unknown
launch angle is not itself displayed in the figure.
-/
structure ArcherFishFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  markedSightDistanceD : LengthQuantity
  markedSightAnglePhi : Real.Angle
  sightLineStyle : FigureLineStyle
  waterSurfaceDrawnHorizontal : Bool
  fishBodyDrawnBelowSurface : Bool
  fishMouthDrawnAtSurface : Bool
  insectDrawnAboveSurface : Bool
  insectDrawnToRightOfFish : Bool
  twigOverhangsWater : Bool
  sightLineStartsAtFishMouth : Bool
  sightLineEndsAtInsect : Bool
  containsLaunchAngleReadout : Bool

/-! ## Physical setup and assumptions -/

/-- The kind of projectile named in the scenario. -/
inductive ProjectileKind where
  | waterDrop
  | other
  deriving DecidableEq, Repr

/-- The idealized dynamics used between launch and arrival. -/
inductive ProjectileModel where
  | uniformDownwardGravityNegligibleDrag
  | other
  deriving DecidableEq, Repr

/-- Reference direction from which an elevation angle is measured. -/
inductive AngleReference where
  | horizontalWaterSurface
  | other
  deriving DecidableEq, Repr

/-!
Independent physical quantities and trajectory observables.  Horizontal
displacement is positive toward the insect and vertical displacement is
positive upward.  In particular, `launchAngleTheta0` is not defined from the
requested answer.
-/
structure ArcherFishDropSetup where
  figure : ArcherFishFigure
  projectileKind : ProjectileKind
  projectileModel : ProjectileModel
  sightAngleReference : AngleReference
  launchAngleReference : AngleReference
  lineOfSightDistanceD : LengthQuantity
  horizontalSeparationToInsect : LengthQuantity
  verticalSeparationToInsect : LengthQuantity
  sightAnglePhi : Real.Angle
  launchAngleTheta0 : Real.Angle
  launchSpeed : SpeedQuantity
  gravitationalAcceleration : AccelerationQuantity
  apexArrivalTime : TimeQuantity
  horizontalDisplacementAt : TimeQuantity → SignedLengthQuantity
  verticalDisplacementAt : TimeQuantity → SignedLengthQuantity
  verticalVelocityAt : TimeQuantity → SignedSpeedQuantity

/-- Qualitative assumptions stated or implicit in the scenario. -/
structure MatchesArcherFishScenario
    (setup : ArcherFishDropSetup) : Prop where
  squirtsWaterDrop : setup.projectileKind = .waterDrop
  idealParabolicFlight :
    setup.projectileModel = .uniformDownwardGravityNegligibleDrag
  sightAngleMeasuredFromWaterSurface :
    setup.sightAngleReference = .horizontalWaterSurface
  launchAngleMeasuredFromWaterSurface :
    setup.launchAngleReference = .horizontalWaterSurface

/-!
Exact labeled and qualitative evidence from the supplied bitmap.  This
predicate identifies `d` and `φ` but supplies no value or formula for `θ₀`.
-/
structure MatchesSuppliedFigure (setup : ArcherFishDropSetup) : Prop where
  everyObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyLabelShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  distanceLabelDenotesD :
    setup.figure.markedSightDistanceD = setup.lineOfSightDistanceD
  phiLabelDenotesSightAngle :
    setup.figure.markedSightAnglePhi = setup.sightAnglePhi
  dashedSightLine : setup.figure.sightLineStyle = .dashed
  horizontalWaterSurface : setup.figure.waterSurfaceDrawnHorizontal = true
  fishUnderWater : setup.figure.fishBodyDrawnBelowSurface = true
  launchPointAtSurface : setup.figure.fishMouthDrawnAtSurface = true
  insectAboveWater : setup.figure.insectDrawnAboveSurface = true
  insectToRight : setup.figure.insectDrawnToRightOfFish = true
  overhangingTwig : setup.figure.twigOverhangsWater = true
  sightLineBeginsAtFish : setup.figure.sightLineStartsAtFishMouth = true
  sightLineTerminatesAtInsect : setup.figure.sightLineEndsAtInsect = true
  noLaunchAngleValueInFigure :
    setup.figure.containsLaunchAngleReadout = false

/-- Numerical readouts supplied in the prose: `d = 0.900 m` and `φ = 36.0°`. -/
structure MatchesProblemReadouts (setup : ArcherFishDropSetup) : Prop where
  sightDistanceMeters : lengthInMeters setup.lineOfSightDistanceD = 9 / 10
  sightAngleDegrees : setup.sightAnglePhi = degrees 36

/-!
Polar-coordinate geometry of the straight sight line.  These assumptions
assign no value to the launch angle.
-/
structure SatisfiesSightLineGeometry
    (setup : ArcherFishDropSetup) : Prop where
  horizontalComponent :
    lengthInMeters setup.horizontalSeparationToInsect =
      lengthInMeters setup.lineOfSightDistanceD *
        Real.Angle.cos setup.sightAnglePhi
  verticalComponent :
    lengthInMeters setup.verticalSeparationToInsect =
      lengthInMeters setup.lineOfSightDistanceD *
        Real.Angle.sin setup.sightAnglePhi

/-- Positivity and acute-angle conditions selecting the pictured shot. -/
structure HasPhysicalParameters (setup : ArcherFishDropSetup) : Prop where
  sightDistancePositive : 0 < lengthInMeters setup.lineOfSightDistanceD
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparationToInsect
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparationToInsect
  launchSpeedPositive : 0 < speedInMetersPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  arrivalTimePositive : 0 < timeInSeconds setup.apexArrivalTime
  sightAngleAcute : setup.sightAnglePhi.toReal ∈ Set.Ioo 0 (Real.pi / 2)
  launchAngleAcute : setup.launchAngleTheta0.toReal ∈ Set.Ioo 0 (Real.pi / 2)

/-!
The ideal two-dimensional projectile equations under uniform downward
gravity.  They are general laws and contain neither the insect boundary
condition nor the required launch-angle relation.
-/
structure SatisfiesIdealProjectileMotion
    (setup : ArcherFishDropSetup) : Prop where
  horizontalTrajectory : ∀ elapsed : TimeQuantity,
    signedLengthInMeters (setup.horizontalDisplacementAt elapsed) =
      speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.cos setup.launchAngleTheta0 * timeInSeconds elapsed
  verticalTrajectory : ∀ elapsed : TimeQuantity,
    signedLengthInMeters (setup.verticalDisplacementAt elapsed) =
      speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngleTheta0 * timeInSeconds elapsed -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration * timeInSeconds elapsed ^ 2
  verticalVelocity : ∀ elapsed : TimeQuantity,
    signedSpeedInMetersPerSecond (setup.verticalVelocityAt elapsed) =
      speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngleTheta0 -
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration * timeInSeconds elapsed

/-!
The event condition in the question: the drop is at the insect and its
vertical velocity vanishes at one positive physical time.  With positive
downward gravity, that instant is the top of the parabola.
-/
structure ReachesInsectAtTop (setup : ArcherFishDropSetup) : Prop where
  horizontalPositionAtInsect :
    signedLengthInMeters
        (setup.horizontalDisplacementAt setup.apexArrivalTime) =
      lengthInMeters setup.horizontalSeparationToInsect
  verticalPositionAtInsect :
    signedLengthInMeters
        (setup.verticalDisplacementAt setup.apexArrivalTime) =
      lengthInMeters setup.verticalSeparationToInsect
  verticalVelocityVanishes :
    signedSpeedInMetersPerSecond
        (setup.verticalVelocityAt setup.apexArrivalTime) = 0

/-! ## Derived angle and displayed-answer metadata -/

/-!
The acute launch angle predicted after eliminating launch speed, gravity,
flight time, and sight distance.  This does not assign the independent setup
angle this value.
-/
def requiredLaunchAngle (sightAngle : Real.Angle) : Real.Angle :=
  ((Real.arctan (2 * Real.Angle.tan sightAngle) : ℝ) : Real.Angle)

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Degree readout printed beside each answer label. -/
def displayedAnswerAngleDegrees : AnswerChoice → ℝ
  | .A => 194 / 5
  | .B => 231 / 5
  | .C => 111 / 2
  | .D => 306 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The standard representative of a physical angle, read in degrees. -/
def angleInDegrees (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- An angle rounds to a displayed tenth of a degree. -/
def RoundsToNearestTenthDegree
    (angle : Real.Angle) (displayedValue : ℝ) : Prop :=
  |angleInDegrees angle - displayedValue| < (1 / 20 : ℝ)

/-- The launch angle agrees, to displayed precision, with an answer choice. -/
def MatchesAnswerChoice
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenthDegree angle (displayedAnswerAngleDegrees choice)

/-- Absolute degree error between an angle and a displayed choice. -/
def displayedChoiceError
    (angle : Real.Angle) (choice : AnswerChoice) : ℝ :=
  |angleInDegrees angle - displayedAnswerAngleDegrees choice|

/-- One answer is at least as close as every displayed alternative. -/
def IsClosestDisplayedAngleChoice
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    displayedChoiceError angle choice ≤ displayedChoiceError angle other

/-- One answer is the unique closest displayed alternative. -/
def IsUniqueClosestDisplayedAngleChoice
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedAngleChoice angle choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedAngleChoice angle other → other = choice

/-!
At the apex, `v₀ sin θ₀ = g t`.  Substitution into the displacement equations
and comparison with the sight-line components yields
`tan θ₀ = 2 tan φ`.
-/
lemma launch_tangent_eq_twice_sight_tangent
    (setup : ArcherFishDropSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hSightLine : SatisfiesSightLineGeometry setup)
    (hMotion : SatisfiesIdealProjectileMotion setup)
    (hApexHit : ReachesInsectAtTop setup) :
    Real.Angle.tan setup.launchAngleTheta0 =
      2 * Real.Angle.tan setup.sightAnglePhi := by
  let d := lengthInMeters setup.lineOfSightDistanceD
  let x := lengthInMeters setup.horizontalSeparationToInsect
  let y := lengthInMeters setup.verticalSeparationToInsect
  let v := speedInMetersPerSecond setup.launchSpeed
  let g :=
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  let t := timeInSeconds setup.apexArrivalTime
  let θ := setup.launchAngleTheta0
  let φ := setup.sightAnglePhi
  have hd : 0 < d := hPhysical.sightDistancePositive
  have hx : 0 < x := hPhysical.horizontalSeparationPositive
  have hv : 0 < v := hPhysical.launchSpeedPositive
  have ht : 0 < t := hPhysical.arrivalTimePositive
  have hSightX : x = d * Real.Angle.cos φ :=
    hSightLine.horizontalComponent
  have hSightY : y = d * Real.Angle.sin φ :=
    hSightLine.verticalComponent
  have hTrajectoryX : x = v * Real.Angle.cos θ * t := by
    simpa [x, v, t, θ] using
      hApexHit.horizontalPositionAtInsect.symm.trans
        (hMotion.horizontalTrajectory setup.apexArrivalTime)
  have hTrajectoryY :
      y = v * Real.Angle.sin θ * t - (1 / 2 : ℝ) * g * t ^ 2 := by
    simpa [y, v, g, t, θ] using
      hApexHit.verticalPositionAtInsect.symm.trans
        (hMotion.verticalTrajectory setup.apexArrivalTime)
  have hApexVelocity : v * Real.Angle.sin θ - g * t = 0 := by
    simpa [v, g, t, θ] using
      (hMotion.verticalVelocity setup.apexArrivalTime).symm.trans
        hApexHit.verticalVelocityVanishes
  have hVerticalElimination : 2 * y = v * Real.Angle.sin θ * t := by
    nlinarith
  have hHorizontal :
      d * Real.Angle.cos φ = v * Real.Angle.cos θ * t :=
    hSightX.symm.trans hTrajectoryX
  have hVertical :
      2 * d * Real.Angle.sin φ = v * Real.Angle.sin θ * t := by
    rw [← hVerticalElimination, hSightY]
    ring
  have hHorizontalScaled :=
    congrArg (fun z : ℝ => z * Real.Angle.sin θ) hHorizontal
  have hVerticalScaled :=
    congrArg (fun z : ℝ => z * Real.Angle.cos θ) hVertical
  have hCross :
      Real.Angle.sin θ * Real.Angle.cos φ =
        2 * Real.Angle.sin φ * Real.Angle.cos θ := by
    apply (mul_left_cancel₀ (ne_of_gt hd) : _)
    nlinarith [hHorizontalScaled, hVerticalScaled]
  have hcosθ : Real.Angle.cos θ ≠ 0 := by
    intro hzero
    rw [hzero] at hTrajectoryX
    simp at hTrajectoryX
    linarith
  have hcosφ : Real.Angle.cos φ ≠ 0 := by
    intro hzero
    rw [hzero] at hSightX
    simp at hSightX
    linarith
  change Real.Angle.tan θ = 2 * Real.Angle.tan φ
  rw [Real.Angle.tan_eq_sin_div_cos,
    Real.Angle.tan_eq_sin_div_cos]
  field_simp [hcosθ, hcosφ]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hCross

/-- The acute-angle branch of the tangent relation selects the arctangent. -/
lemma launch_angle_eq_requiredLaunchAngle
    (setup : ArcherFishDropSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hSightLine : SatisfiesSightLineGeometry setup)
    (hMotion : SatisfiesIdealProjectileMotion setup)
    (hApexHit : ReachesInsectAtTop setup) :
    setup.launchAngleTheta0 = requiredLaunchAngle setup.sightAnglePhi := by
  have htan :=
    launch_tangent_eq_twice_sight_tangent
      setup hPhysical hSightLine hMotion hApexHit
  have hthetaReal :
      setup.launchAngleTheta0.toReal =
        Real.arctan (2 * Real.Angle.tan setup.sightAnglePhi) := by
    symm
    apply Real.arctan_eq_of_tan_eq
    · simpa only [Real.Angle.tan_toReal] using htan
    · exact
        ⟨by linarith [hPhysical.launchAngleAcute.1, Real.pi_pos],
          hPhysical.launchAngleAcute.2⟩
  unfold requiredLaunchAngle
  rw [← hthetaReal]
  exact (Real.Angle.coe_toReal setup.launchAngleTheta0).symm

/-!
For `φ = 36.0°`, the predicted angle is approximately `55.46°`, so it rounds
to `55.5°` and is uniquely closest to displayed choice C.
-/
lemma required_angle_for_thirty_six_degrees_matches_choice_C :
    MatchesAnswerChoice (requiredLaunchAngle (degrees 36)) .C ∧
      IsUniqueClosestDisplayedAngleChoice
        (requiredLaunchAngle (degrees 36)) .C := by
  have hdegrees :
      degrees 36 = ((Real.pi / 5 : ℝ) : Real.Angle) := by
    unfold degrees
    congr 1
    ring
  rw [hdegrees]
  let q : ℝ := 2 * Real.tan (Real.pi / 5)
  have hpiFifthPositive : 0 < Real.pi / 5 := by
    positivity
  have hpiFifthAcute : Real.pi / 5 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have htanPositive : 0 < Real.tan (Real.pi / 5) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two
      hpiFifthPositive hpiFifthAcute
  have hqPositive : 0 < q := by
    dsimp [q]
    positivity
  have hsqrtFiveNonnegative : 0 ≤ Real.sqrt 5 :=
    Real.sqrt_nonneg 5
  have hsqrtFiveSquared : Real.sqrt 5 ^ 2 = 5 := by
    norm_num
  have hcosPositive : 0 < Real.cos (Real.pi / 5) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], hpiFifthAcute⟩
  have htanSquared :
      Real.tan (Real.pi / 5) ^ 2 = 5 - 2 * Real.sqrt 5 := by
    rw [Real.tan_eq_sin_div_cos]
    have htrig := Real.sin_sq_add_cos_sq (Real.pi / 5)
    rw [Real.cos_pi_div_five] at htrig ⊢
    field_simp [ne_of_gt hcosPositive]
    nlinarith
  have hqSquared : q ^ 2 = 4 * (5 - 2 * Real.sqrt 5) := by
    dsimp [q]
    nlinarith [htanSquared]
  have hsqrtFiveUpper :
      Real.sqrt 5 < (223607 / 100000 : ℝ) := by
    nlinarith
  have hsqrtFiveLower :
      (559 / 250 : ℝ) < Real.sqrt 5 := by
    nlinarith
  have hqLower : (1453 / 1000 : ℝ) < q := by
    have hsquare :
        (1453 / 1000 : ℝ) ^ 2 < q ^ 2 := by
      rw [hqSquared]
      nlinarith
    nlinarith
  have hqUpper : q < (727 / 500 : ℝ) := by
    have hsquare :
        q ^ 2 < (727 / 500 : ℝ) ^ 2 := by
      rw [hqSquared]
      nlinarith
    nlinarith
  let z : ℝ := (q - 1) / (q + 1)
  have hqGreaterThanOne : 1 < q := by
    linarith
  have hzPositive : 0 < z := by
    dsimp [z]
    positivity
  have hzLessThanOne : z < 1 := by
    dsimp [z]
    rw [div_lt_one (by positivity)]
    linarith
  have hzLower : (453 / 2453 : ℝ) < z := by
    dsimp [z]
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hzUpper : z < (227 / 1227 : ℝ) := by
    dsimp [z]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hzTransform : (z + 1) / (1 - z) = q := by
    dsimp [z]
    field_simp [ne_of_gt (by linarith : 0 < q + 1)]
    ring
  have hArctanDecomposition :
      Real.arctan q = Real.pi / 4 + Real.arctan z := by
    have hadd :=
      Real.arctan_add (x := z) (y := (1 : ℝ))
        (by simpa only [mul_one] using hzLessThanOne)
    simp only [mul_one] at hadd
    rw [Real.arctan_one, hzTransform] at hadd
    linarith
  have r_lt_arctan_of_poly {r s : ℝ}
      (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 ≤ s)
      (hpoly :
        r - r ^ 3 / 6 + r ^ 4 * (5 / 96) <
          s * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96))) :
      r < Real.arctan s := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hsinBound := Real.sin_bound habs
    have hcosBound := Real.cos_bound habs
    rw [abs_of_pos hr0] at hsinBound hcosBound
    have hsinUpper :
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hsinBound |>.2]
    have hcosLower :
        1 - r ^ 2 / 2 - r ^ 4 * (5 / 96) ≤ Real.cos r := by
      linarith [abs_le.mp hcosBound |>.1]
    have hrPi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPos : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrPi⟩
    have htan : Real.tan r < s := by
      rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcosPos]
      calc
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) :=
          hsinUpper
        _ < s * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96)) := hpoly
        _ ≤ s * Real.cos r :=
          mul_le_mul_of_nonneg_left hcosLower hs0
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrPi]
    exact Real.arctan_strictMono htan
  have arctan_lt_r_of_poly {s r : ℝ}
      (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 ≤ s)
      (hpoly :
        s * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) <
          r - r ^ 3 / 6 - r ^ 4 * (5 / 96)) :
      Real.arctan s < r := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hsinBound := Real.sin_bound habs
    have hcosBound := Real.cos_bound habs
    rw [abs_of_pos hr0] at hsinBound hcosBound
    have hsinLower :
        r - r ^ 3 / 6 - r ^ 4 * (5 / 96) ≤ Real.sin r := by
      linarith [abs_le.mp hsinBound |>.1]
    have hcosUpper :
        Real.cos r ≤ 1 - r ^ 2 / 2 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hcosBound |>.2]
    have hrPi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPos : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrPi⟩
    have htan : s < Real.tan r := by
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcosPos]
      calc
        s * Real.cos r ≤
            s * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) :=
          mul_le_mul_of_nonneg_left hcosUpper hs0
        _ < r - r ^ 3 / 6 - r ^ 4 * (5 / 96) := hpoly
        _ ≤ Real.sin r := hsinLower
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrPi]
    exact Real.arctan_strictMono htan
  have hSmallLower :
      (73 / 400 : ℝ) < Real.arctan (453 / 2453 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hSmallUpper :
      Real.arctan (227 / 1227 : ℝ) < (23 / 125 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hArctanFifthDecomposition :
      Real.arctan (1 / 10 : ℝ) + Real.arctan (5 / 51 : ℝ) =
        Real.arctan (1 / 5 : ℝ) := by
    rw [Real.arctan_add] <;> norm_num
  have hArctanTenthLower :
      (249 / 2500 : ℝ) < Real.arctan (1 / 10 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hArctanFiveFiftyOneLower :
      (977 / 10000 : ℝ) < Real.arctan (5 / 51 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hArctanTenthUpper :
      Real.arctan (1 / 10 : ℝ) < (997 / 10000 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hArctanFiveFiftyOneUpper :
      Real.arctan (5 / 51 : ℝ) < (9779 / 100000 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hArctanFifthLower :
      (1973 / 10000 : ℝ) < Real.arctan (1 / 5 : ℝ) := by
    linarith
  have hArctanFifthUpper :
      Real.arctan (1 / 5 : ℝ) < (19749 / 100000 : ℝ) := by
    linarith
  have hArctanTwoThirtyNineLower :
      (41 / 10000 : ℝ) < Real.arctan (1 / 239 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hArctanTwoThirtyNineUpper :
      Real.arctan (1 / 239 : ℝ) < (21 / 5000 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hMachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [inv_eq_one_div] at hMachin
  have hPiLower : (157 / 50 : ℝ) < Real.pi := by
    nlinarith only
      [hArctanFifthLower, hArctanTwoThirtyNineUpper, hMachin]
  have hPiUpper : Real.pi < (39293 / 12500 : ℝ) := by
    nlinarith only
      [hArctanFifthUpper, hArctanTwoThirtyNineLower, hMachin]
  have hDeltaLower :
      209 * Real.pi / 3600 < Real.arctan z := by
    have hPiBound :
        209 * Real.pi / 3600 < (73 / 400 : ℝ) := by
      nlinarith only [hPiUpper]
    have hMonotone :
        Real.arctan (453 / 2453 : ℝ) < Real.arctan z :=
      Real.arctan_strictMono hzLower
    linarith
  have hDeltaUpper :
      Real.arctan z < 211 * Real.pi / 3600 := by
    have hPiBound :
        (23 / 125 : ℝ) < 211 * Real.pi / 3600 := by
      nlinarith only [hPiLower]
    have hMonotone :
        Real.arctan z < Real.arctan (227 / 1227 : ℝ) :=
      Real.arctan_strictMono hzUpper
    linarith
  have hAngleRadiansLower :
      1109 * Real.pi / 3600 < Real.arctan q := by
    rw [hArctanDecomposition]
    nlinarith only [hDeltaLower]
  have hAngleRadiansUpper :
      Real.arctan q < 1111 * Real.pi / 3600 := by
    rw [hArctanDecomposition]
    nlinarith only [hDeltaUpper]
  have hAngleDegreesLower :
      (1109 / 20 : ℝ) <
        Real.arctan q * 180 / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith only [hAngleRadiansLower, Real.pi_pos]
  have hAngleDegreesUpper :
      Real.arctan q * 180 / Real.pi <
        (1111 / 20 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith only [hAngleRadiansUpper, Real.pi_pos]
  have hRequiredLaunchAngle :
      requiredLaunchAngle
          (((Real.pi / 5 : ℝ) : Real.Angle)) =
        ((Real.arctan q : ℝ) : Real.Angle) := by
    unfold requiredLaunchAngle
    rw [Real.Angle.tan_coe]
  have hArctanToReal :
      (((Real.arctan q : ℝ) : Real.Angle).toReal) =
        Real.arctan q := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan q, Real.pi_pos]
    · linarith [Real.arctan_lt_pi_div_two q, Real.pi_pos]
  have hDegreeReadout :
      angleInDegrees
          (requiredLaunchAngle
            (((Real.pi / 5 : ℝ) : Real.Angle))) =
        Real.arctan q * 180 / Real.pi := by
    rw [hRequiredLaunchAngle, angleInDegrees, hArctanToReal]
  let a :=
    angleInDegrees
      (requiredLaunchAngle (((Real.pi / 5 : ℝ) : Real.Angle)))
  have haLower : (1109 / 20 : ℝ) < a := by
    dsimp [a]
    rw [hDegreeReadout]
    exact hAngleDegreesLower
  have haUpper : a < (1111 / 20 : ℝ) := by
    dsimp [a]
    rw [hDegreeReadout]
    exact hAngleDegreesUpper
  have hChoiceCError : |a - (111 / 2 : ℝ)| < (1 / 20 : ℝ) := by
    rw [abs_lt]
    constructor
    · linarith only [haLower]
    · linarith only [haUpper]
  have hOtherFar :
      ∀ other : AnswerChoice, other ≠ .C →
        (1 / 20 : ℝ) <
          displayedChoiceError
            (requiredLaunchAngle
              (((Real.pi / 5 : ℝ) : Real.Angle))) other := by
    intro other hne
    unfold displayedChoiceError
    change (1 / 20 : ℝ) < |a - displayedAnswerAngleDegrees other|
    cases other with
    | A =>
        rw [displayedAnswerAngleDegrees,
          abs_of_pos (by linarith only [haLower] : 0 < a - 194 / 5)]
        linarith only [haLower]
    | B =>
        rw [displayedAnswerAngleDegrees,
          abs_of_pos (by linarith only [haLower] : 0 < a - 231 / 5)]
        linarith only [haLower]
    | C =>
        exact (hne rfl).elim
    | D =>
        rw [displayedAnswerAngleDegrees,
          abs_of_neg (by linarith only [haUpper] : a - 306 / 5 < 0)]
        linarith only [haUpper]
  have hClosestC :
      IsClosestDisplayedAngleChoice
        (requiredLaunchAngle
          (((Real.pi / 5 : ℝ) : Real.Angle))) .C := by
    intro other
    unfold displayedChoiceError
    change
      |a - displayedAnswerAngleDegrees .C| ≤
        |a - displayedAnswerAngleDegrees other|
    cases other with
    | A =>
        rw [displayedAnswerAngleDegrees, displayedAnswerAngleDegrees,
          abs_of_pos
            (by linarith only [haLower] : 0 < a - 194 / 5),
          abs_le]
        constructor <;> linarith only [haLower, haUpper]
    | B =>
        rw [displayedAnswerAngleDegrees, displayedAnswerAngleDegrees,
          abs_of_pos
            (by linarith only [haLower] : 0 < a - 231 / 5),
          abs_le]
        constructor <;> linarith only [haLower, haUpper]
    | C =>
        exact le_rfl
    | D =>
        rw [displayedAnswerAngleDegrees, displayedAnswerAngleDegrees,
          abs_of_neg
            (by linarith only [haUpper] : a - 306 / 5 < 0),
          abs_le]
        constructor <;> linarith only [haLower, haUpper]
  constructor
  · simpa [MatchesAnswerChoice, RoundsToNearestTenthDegree, a,
      displayedAnswerAngleDegrees] using hChoiceCError
  · refine ⟨hClosestC, ?_⟩
    intro other hother
    by_contra hne
    have hfar := hOtherFar other hne
    unfold displayedChoiceError at hfar
    change
      (1 / 20 : ℝ) <
        |a - displayedAnswerAngleDegrees other| at hfar
    have hle := hother .C
    unfold displayedChoiceError at hle
    change
      |a - displayedAnswerAngleDegrees other| ≤
        |a - displayedAnswerAngleDegrees .C| at hle
    rw [displayedAnswerAngleDegrees] at hle
    linarith only [hfar, hle, hChoiceCError]

/-!
Under the stated figure, data, geometry, projectile laws, and apex-arrival
condition, the required launch angle is the acute angle
`arctan (2 tan 36°)`, which rounds to `55.5°`, answer choice C.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0742:target`.
-/
theorem problem_phyx_mini_0742
    (setup : ArcherFishDropSetup)
    (hScenario : MatchesArcherFishScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hSightLine : SatisfiesSightLineGeometry setup)
    (hMotion : SatisfiesIdealProjectileMotion setup)
    (hApexHit : ReachesInsectAtTop setup) :
    setup.launchAngleTheta0 = requiredLaunchAngle (degrees 36) ∧
      MatchesAnswerChoice setup.launchAngleTheta0 .C ∧
      IsUniqueClosestDisplayedAngleChoice setup.launchAngleTheta0 .C := by
  have hLaunchAngle :=
    launch_angle_eq_requiredLaunchAngle
      setup hPhysical hSightLine hMotion hApexHit
  rw [hReadouts.sightAngleDegrees] at hLaunchAngle
  rcases required_angle_for_thirty_six_degrees_matches_choice_C with
    ⟨hMatches, hUnique⟩
  refine ⟨hLaunchAngle, ?_, ?_⟩
  · rw [hLaunchAngle]
    exact hMatches
  · rw [hLaunchAngle]
    exact hUnique

end PhyXMiniProblems.ProblemPhyXMini0742
