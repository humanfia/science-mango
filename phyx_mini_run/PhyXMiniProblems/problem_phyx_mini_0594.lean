import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0594

open Dimension

/-!
# Apparent superluminal motion of an ionized-gas knot

An ionized-gas knot moves at constant velocity along a galactic jet and emits
two bursts of light.  The path makes an angle `theta` with the direction from
the bursts toward Earth.  The transverse separation of the two burst events is
the apparent distance `D_app`, while the difference of the light arrival times
at Earth is `T_app`.

Lengths, durations, and speeds below are unit-independent Physlib quantities.
Real numbers are used only for coherent SI readouts, dimensionless speed
fractions, angles, and the multiples of the speed of light printed in the
answer choices.

Assumption/target boundary:

* `MatchesProblemReadouts` contains only `v = 0.980 c` and `theta = 30 degrees`.
* `MatchesSuppliedJetFigure` records the labels and qualitative geometry in the
  primary raster.
* `HasPhysicalJetObservationParameters` selects the positive, approaching,
  subluminal branch of the setup.
* `SatisfiesApparentMotionLaws` states constant-speed kinematics, the two
  geometric projections, the light-travel arrival-time law, and the definition
  `V_app = D_app / T_app`.
* The derived apparent-speed formula and agreement with `3.24 c` occur only in
  the conclusion of the final theorem.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Second readout of a duration measured in the stationary burst frame. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Dimensionless speed as a multiple of the vacuum speed of light. -/
def speedFractionOfLight (speed : SpeedQuantity) : ℝ :=
  speedInMetersPerSecond speed / vacuumSpeedOfLightInMetersPerSecond

/-- Convert a degree readout to Mathlib's type of angles. -/
def angleFromDegrees (degrees : ℝ) : Real.Angle :=
  ((degrees * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two light-emission events marked by red starbursts in the figure. -/
inductive BurstLabel where
  | burstOne
  | burstTwo
  deriving DecidableEq, Fintype, Repr

/-- The astrophysical source from which the jet is expelled. -/
inductive AstrophysicalSource where
  | galaxy
  deriving DecidableEq, Repr

/-- The moving object whose apparent speed is observed. -/
inductive MovingObject where
  | knotOfIonizedGas
  deriving DecidableEq, Repr

/-- The motion model explicitly stated in the problem. -/
inductive KnotMotionModel where
  | constantVelocityAlongJetPath
  deriving DecidableEq, Repr

/-- Literal mathematical or descriptive labels visible in the primary image. -/
inductive FigureTextLabel where
  | pathOfKnotOfIonizedGas
  | burstOne
  | burstTwo
  | velocityV
  | angleTheta
  | apparentDistanceDApp
  | lightRaysHeadedToEarth
  deriving DecidableEq, Fintype, Repr

/-- The four salient arrows drawn in the primary image. -/
inductive FigureArrow where
  | knotVelocity
  | burstOneLightRay
  | burstTwoLightRay
  | apparentDistance
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions of arrows relative to the observer and jet path. -/
inductive FigureDirection where
  | alongPathTowardBurstTwo
  | towardEarth
  | acrossObserverView
  deriving DecidableEq, Repr

/--
Semantic transcription of the supplied diagram.  These fields record only
which objects, labels, and directional relations are drawn; no numerical
apparent speed is stored here.
-/
structure SuperluminalJetFigure where
  labelShown : FigureTextLabel → Bool
  burstShown : BurstLabel → Bool
  burstOnJetPath : BurstLabel → Bool
  arrowShown : FigureArrow → Bool
  arrowDirection : FigureArrow → FigureDirection
  burstOnePrecedesBurstTwoAlongMotion : Bool
  thetaBetweenJetPathAndEarthDirection : Bool
  apparentDistanceConnectsLightRays : Bool

/-!
The independent physical quantities in the observation.  In particular,
`apparentSpeed` is an observable field; it is not defined from an answer choice
or from the requested numerical result.
-/
structure ApparentJetMotionSetup where
  source : AstrophysicalSource
  movingObject : MovingObject
  motionModel : KnotMotionModel
  emitsLightBurst : BurstLabel → Prop
  lightEventuallyDetectedOnEarth : BurstLabel → Prop
  knotSpeed : SpeedQuantity
  viewingAngle : Real.Angle
  emissionInterval : DurationQuantity
  pathDistanceBetweenBursts : LengthQuantity
  earthwardAdvanceBetweenBursts : LengthQuantity
  apparentDistance : LengthQuantity
  apparentArrivalInterval : DurationQuantity
  apparentSpeed : SpeedQuantity
  figure : SuperluminalJetFigure

/-! ## Scenario, data, figure readouts, and governing laws -/

/-- Categorical physical facts stated in the scenario. -/
structure MatchesJetScenario (setup : ApparentJetMotionSetup) : Prop where
  sourceIsGalaxy : setup.source = .galaxy
  objectIsIonizedGasKnot : setup.movingObject = .knotOfIonizedGas
  motionIsConstantVelocity :
    setup.motionModel = .constantVelocityAlongJetPath
  bothBurstsAreEmitted : ∀ burst, setup.emitsLightBurst burst
  bothBurstsAreEventuallyDetectedOnEarth :
    ∀ burst, setup.lightEventuallyDetectedOnEarth burst

/-!
The two numerical readouts supplied by the problem.  No apparent-distance,
arrival-time, apparent-speed, or answer-choice value occurs here.
-/
structure MatchesProblemReadouts (setup : ApparentJetMotionSetup) : Prop where
  knotSpeedIsPointNineEightZeroC :
    speedInMetersPerSecond setup.knotSpeed =
      (98 : ℝ) / 100 * vacuumSpeedOfLightInMetersPerSecond
  viewingAngleIsThirtyDegrees :
    setup.viewingAngle = angleFromDegrees 30

/-! Qualitative geometry read directly from the primary raster. -/
structure MatchesSuppliedJetFigure (setup : ApparentJetMotionSetup) : Prop where
  everyTextLabelIsShown : ∀ label, setup.figure.labelShown label = true
  bothBurstsAreShown : ∀ burst, setup.figure.burstShown burst = true
  bothBurstsLieOnJetPath :
    ∀ burst, setup.figure.burstOnJetPath burst = true
  everySalientArrowIsShown :
    ∀ arrow, setup.figure.arrowShown arrow = true
  velocityArrowRunsAlongPathTowardBurstTwo :
    setup.figure.arrowDirection .knotVelocity =
      .alongPathTowardBurstTwo
  burstOneLightHeadsTowardEarth :
    setup.figure.arrowDirection .burstOneLightRay = .towardEarth
  burstTwoLightHeadsTowardEarth :
    setup.figure.arrowDirection .burstTwoLightRay = .towardEarth
  apparentDistanceRunsAcrossObserverView :
    setup.figure.arrowDirection .apparentDistance = .acrossObserverView
  burstOrderAgreesWithMotion :
    setup.figure.burstOnePrecedesBurstTwoAlongMotion = true
  thetaHasDisplayedGeometricRole :
    setup.figure.thetaBetweenJetPathAndEarthDirection = true
  apparentDistanceJoinsTheTwoLightRays :
    setup.figure.apparentDistanceConnectsLightRays = true

/-!
Physical-domain conditions for the approaching-jet branch depicted in the
figure.  They state only positivity, acuteness, and subluminal true motion.
-/
structure HasPhysicalJetObservationParameters
    (setup : ApparentJetMotionSetup) : Prop where
  emissionIntervalPositive :
    0 < durationInSeconds setup.emissionInterval
  apparentArrivalIntervalPositive :
    0 < durationInSeconds setup.apparentArrivalInterval
  pathDistancePositive :
    0 < lengthInMeters setup.pathDistanceBetweenBursts
  earthwardAdvancePositive :
    0 < lengthInMeters setup.earthwardAdvanceBetweenBursts
  apparentDistancePositive :
    0 < lengthInMeters setup.apparentDistance
  trueKnotSpeedPositive :
    0 < speedInMetersPerSecond setup.knotSpeed
  trueKnotSpeedIsSubluminal :
    speedInMetersPerSecond setup.knotSpeed <
      vacuumSpeedOfLightInMetersPerSecond
  viewingAngleHasPositiveSine : 0 < Real.Angle.sin setup.viewingAngle
  viewingAngleHasPositiveCosine : 0 < Real.Angle.cos setup.viewingAngle

/-!
The governing constant-velocity, projection, and light-arrival relations.

The second burst occurs closer to Earth by the earthward projection of the
knot's displacement.  Its light therefore has less distance to travel, so the
arrival interval is the emission interval minus that projection divided by
`c`.  These laws contain no numerical value for the requested apparent speed.
-/
structure SatisfiesApparentMotionLaws
    (setup : ApparentJetMotionSetup) : Prop where
  constantSpeedPathKinematics :
    lengthInMeters setup.pathDistanceBetweenBursts =
      speedInMetersPerSecond setup.knotSpeed *
        durationInSeconds setup.emissionInterval
  transverseProjectionGivesApparentDistance :
    lengthInMeters setup.apparentDistance =
      lengthInMeters setup.pathDistanceBetweenBursts *
        Real.Angle.sin setup.viewingAngle
  earthwardProjectionOfDisplacement :
    lengthInMeters setup.earthwardAdvanceBetweenBursts =
      lengthInMeters setup.pathDistanceBetweenBursts *
        Real.Angle.cos setup.viewingAngle
  lightTravelArrivalInterval :
    durationInSeconds setup.apparentArrivalInterval =
      durationInSeconds setup.emissionInterval -
        lengthInMeters setup.earthwardAdvanceBetweenBursts /
          vacuumSpeedOfLightInMetersPerSecond
  apparentSpeedIsDistanceOverArrivalTime :
    speedInMetersPerSecond setup.apparentSpeed =
      lengthInMeters setup.apparentDistance /
        durationInSeconds setup.apparentArrivalInterval

/-! ## Displayed answers and formalization target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Multiple of `c` printed beside each answer label. -/
def AnswerChoice.speedOfLightMultiple : AnswerChoice → ℝ
  | .A => (11 : ℝ) / 4
  | .B => (49 : ℝ) / 25
  | .C => (81 : ℝ) / 25
  | .D => (9 : ℝ) / 2

/--
A speed matches a displayed answer to the nearest hundredth of `c` when its
dimensionless ratio to `c` differs by at most `0.005`.
-/
def MatchesAnswerToNearestHundredth
    (speed : SpeedQuantity) (choice : AnswerChoice) : Prop :=
  |speedFractionOfLight speed - choice.speedOfLightMultiple| ≤
    (1 : ℝ) / 200

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/--
For a knot moving at `0.980 c` at `30 degrees` toward the observer, light from
the second burst has a shorter travel time.  The resulting apparent-speed
formula agrees, to the displayed precision, with answer C, `3.24 c`.

Blueprint label: `thm:physics:phyx_mini_0594:target`.
-/
theorem apparent_speed_of_ionized_gas_knot_matches_answer_C
    (setup : ApparentJetMotionSetup)
    (_scenario : MatchesJetScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedJetFigure setup)
    (_physical : HasPhysicalJetObservationParameters setup)
    (_laws : SatisfiesApparentMotionLaws setup) :
    speedFractionOfLight setup.apparentSpeed =
        (speedFractionOfLight setup.knotSpeed *
            Real.Angle.sin setup.viewingAngle) /
          (1 - speedFractionOfLight setup.knotSpeed *
            Real.Angle.cos setup.viewingAngle) ∧
      MatchesAnswerToNearestHundredth setup.apparentSpeed .C := by
  have hc_pos : 0 < vacuumSpeedOfLightInMetersPerSecond := by
    norm_num [vacuumSpeedOfLightInMetersPerSecond,
      DimSpeed.speedOfLight_in_SI]
  have hc_ne : vacuumSpeedOfLightInMetersPerSecond ≠ 0 :=
    ne_of_gt hc_pos
  have harrival_factor :
      durationInSeconds setup.apparentArrivalInterval =
        durationInSeconds setup.emissionInterval *
          (1 -
            speedInMetersPerSecond setup.knotSpeed /
                vacuumSpeedOfLightInMetersPerSecond *
              Real.Angle.cos setup.viewingAngle) := by
    rw [_laws.lightTravelArrivalInterval,
      _laws.earthwardProjectionOfDisplacement,
      _laws.constantSpeedPathKinematics]
    field_simp
  have harrival_pos :=
    _physical.apparentArrivalIntervalPositive
  rw [harrival_factor] at harrival_pos
  have hden_pos :
      0 <
        1 -
          speedInMetersPerSecond setup.knotSpeed /
              vacuumSpeedOfLightInMetersPerSecond *
            Real.Angle.cos setup.viewingAngle :=
    pos_of_mul_pos_right harrival_pos
      (le_of_lt _physical.emissionIntervalPositive)
  have hformula :
      speedFractionOfLight setup.apparentSpeed =
        (speedFractionOfLight setup.knotSpeed *
            Real.Angle.sin setup.viewingAngle) /
          (1 -
            speedFractionOfLight setup.knotSpeed *
              Real.Angle.cos setup.viewingAngle) := by
    change
      speedInMetersPerSecond setup.apparentSpeed /
          vacuumSpeedOfLightInMetersPerSecond =
        (speedInMetersPerSecond setup.knotSpeed /
              vacuumSpeedOfLightInMetersPerSecond *
            Real.Angle.sin setup.viewingAngle) /
          (1 -
            speedInMetersPerSecond setup.knotSpeed /
                vacuumSpeedOfLightInMetersPerSecond *
              Real.Angle.cos setup.viewingAngle)
    rw [_laws.apparentSpeedIsDistanceOverArrivalTime,
      _laws.transverseProjectionGivesApparentDistance,
      _laws.constantSpeedPathKinematics, harrival_factor]
    field_simp [ne_of_gt _physical.emissionIntervalPositive]
  constructor
  · exact hformula
  · have hbeta :
        speedFractionOfLight setup.knotSpeed = (49 : ℝ) / 50 := by
      rw [speedFractionOfLight,
        _readouts.knotSpeedIsPointNineEightZeroC]
      field_simp
      norm_num
    have hsin :
        Real.Angle.sin setup.viewingAngle = (1 : ℝ) / 2 := by
      rw [_readouts.viewingAngleIsThirtyDegrees, angleFromDegrees,
        Real.Angle.sin_coe]
      convert Real.sin_pi_div_six using 1
      ring_nf
    have hcos :
        Real.Angle.cos setup.viewingAngle = Real.sqrt 3 / 2 := by
      rw [_readouts.viewingAngleIsThirtyDegrees, angleFromDegrees,
        Real.Angle.cos_coe]
      convert Real.cos_pi_div_six using 1
      ring_nf
    unfold MatchesAnswerToNearestHundredth
    rw [hformula, hbeta, hsin, hcos]
    change
      |(((49 : ℝ) / 50 * ((1 : ℝ) / 2)) /
            (1 - (49 : ℝ) / 50 * (Real.sqrt 3 / 2))) -
          (81 : ℝ) / 25| ≤
        (1 : ℝ) / 200
    have hsqrt_nonneg : 0 ≤ Real.sqrt 3 :=
      Real.sqrt_nonneg 3
    have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_lower : (1732 : ℝ) / 1000 < Real.sqrt 3 := by
      nlinarith
    have hsqrt_upper : Real.sqrt 3 < (17321 : ℝ) / 10000 := by
      nlinarith
    have hsqrt_den_pos :
        0 < 1 - (49 : ℝ) / 50 * (Real.sqrt 3 / 2) := by
      nlinarith
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hsqrt_den_pos]
      nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hsqrt_den_pos]
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0594
