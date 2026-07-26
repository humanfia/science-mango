import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0816

open Dimension

/-!
# Final speed in a two-puck elastic collision

Puck A (`0.500 kg`) initially moves at `4.00 m/s` along positive `x`, while
puck B (`0.300 kg`) is at rest.  The collision takes place on a frictionless
air-hockey table and is elastic.  Afterwards A has speed `2.00 m/s` at the
angle `alpha` above positive `x`; B leaves at the angle `beta` below positive
`x`, with its speed requested.

Masses, speed magnitudes, and planar velocities are unit-independent Physlib
dimensionful quantities.  Real numbers occur only as coherent-unit readouts,
dimensionless angle readouts, literal figure metadata, and displayed answer
values.

Assumption/target boundary:

* `MatchesPuckCollisionProblemData` contains the stated mass and speed data.
* `MatchesSuppliedPuckCollisionFigure` records only literal and qualitative
  information visible in image `816.png`.
* `MatchesFigureVelocityGeometry` and `HasVelocityMagnitudeKinematics` connect
  the labelled arrows and angles to the physical velocity vectors.
* `SatisfiesElasticCollisionConservationLaws` states conservation of planar
  linear momentum and kinetic energy.
* There are no previous-part results.
* The requested value `Real.sqrt 20 m/s`, its `4.47 m/s` displayed rounding,
  and answer B occur only in conclusions or in the separate answer table.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- The physical dimension of velocity, `L T⁻¹`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed magnitude. -/
abbrev SpeedMagnitudeQuantity : Type := DimSpeed

/-- A signed, unit-independent velocity vector in the table plane. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, the positive horizontal axis pointing right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, the positive vertical axis pointing up. -/
def yAxis : Fin 2 := 1

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a speed magnitude in coherent selected length and time units. -/
def speedMagnitudeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedMagnitudeQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a planar velocity in coherent selected length and time units. -/
def planarVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocityQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre-per-second readout of a physical speed magnitude. -/
def speedMagnitudeInMetersPerSecond
    (speed : SpeedMagnitudeQuantity) : ℝ :=
  speedMagnitudeReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metre-per-second readout of a physical planar velocity. -/
def planarVelocityInMetersPerSecond
    (velocity : PlanarVelocityQuantity) : EuclideanSpace ℝ (Fin 2) :=
  planarVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-! ## Pucks, collision stages, and primary-image vocabulary -/

/-- The two colliding pucks labelled in the problem. -/
inductive PuckLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The two panels in the supplied before/after collision diagram. -/
inductive CollisionStage where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- The coordinate axes drawn through the origin `O` in both panels. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions of the three velocity arrows in the raster. -/
inductive VelocityArrowDirection where
  | positiveX
  | abovePositiveX
  | belowPositiveX
  deriving DecidableEq, Repr

/-- The two outgoing angle labels printed in the after-collision panel. -/
inductive OutgoingAngleLabel where
  | alpha
  | beta
  deriving DecidableEq, Fintype, Repr

/-- The outgoing puck whose direction is named by each printed angle. -/
def puckForOutgoingAngle : OutgoingAngleLabel → PuckLabel
  | .alpha => .A
  | .beta => .B

/-- The qualitative outgoing direction associated with each angle label. -/
def directionForOutgoingAngle : OutgoingAngleLabel → VelocityArrowDirection
  | .alpha => .abovePositiveX
  | .beta => .belowPositiveX

/-!
Literal and schematic content transcribed from the primary image.  The
`displayedSpeedMetersPerSecond` field is optional because the raster prints no
numerical value next to B's outgoing velocity arrow.
-/
structure PuckCollisionFigure where
  panelTitleShown : CollisionStage → Bool
  originLabelShown : CollisionStage → Bool
  axisShown : CollisionStage → DiagramAxis → Bool
  positiveXAxisPointsRight : CollisionStage → Bool
  positiveYAxisPointsUp : CollisionStage → Bool
  puckShown : CollisionStage → PuckLabel → Bool
  massLabelKilograms : PuckLabel → ℝ
  velocityArrowShown : CollisionStage → PuckLabel → Bool
  velocityArrowDirection : CollisionStage → PuckLabel → VelocityArrowDirection
  displayedSpeedMetersPerSecond : CollisionStage → PuckLabel → Option ℝ
  initialRestTextShownForB : Bool
  angleLabelShown : OutgoingAngleLabel → Bool
  angleMeasuredFromPositiveXAxis : OutgoingAngleLabel → Bool

/-- The idealized table model stated in the prose. -/
inductive TableSurfaceModel where
  | frictionlessAirHockey
  | other
  deriving DecidableEq, Repr

/-- The collision model stated in the prose. -/
inductive CollisionModel where
  | elastic
  | other
  deriving DecidableEq, Repr

/-!
Independent physical fields of the experiment.  In particular, B's outgoing
speed is an independent dimensionful field and is not defined from a displayed
answer value.
-/
structure ElasticPuckCollisionSetup where
  figure : PuckCollisionFigure
  spatialDimension : ℕ
  tableSurfaceModel : TableSurfaceModel
  collisionModel : CollisionModel
  puckMass : PuckLabel → MassQuantity
  velocity : CollisionStage → PuckLabel → PlanarVelocityQuantity
  speedMagnitude : CollisionStage → PuckLabel → SpeedMagnitudeQuantity
  alphaRadians : ℝ
  betaRadians : ℝ

/-! ## Scenario, data, figure geometry, and governing laws -/

/-- The qualitative physical scenario supplied in the problem statement. -/
structure MatchesElasticAirHockeyScenario
    (setup : ElasticPuckCollisionSetup) : Prop where
  motionIsPlanar : setup.spatialDimension = 2
  tableIsFrictionless :
    setup.tableSurfaceModel = .frictionlessAirHockey
  collisionIsElastic : setup.collisionModel = .elastic

/-!
Numerical physical readouts stated in the prose and shown in the image.  No
outgoing speed for puck B, exact result, rounded answer, or answer label occurs
in this record.
-/
structure MatchesPuckCollisionProblemData
    (setup : ElasticPuckCollisionSetup) : Prop where
  puckAMassKilograms : massInKilograms (setup.puckMass .A) = 1 / 2
  puckBMassKilograms : massInKilograms (setup.puckMass .B) = 3 / 10
  puckAInitialSpeedMetersPerSecond :
    speedMagnitudeInMetersPerSecond
        (setup.speedMagnitude .before .A) = 4
  puckAFinalSpeedMetersPerSecond :
    speedMagnitudeInMetersPerSecond
        (setup.speedMagnitude .after .A) = 2
  puckBInitialSpeedMetersPerSecond :
    speedMagnitudeInMetersPerSecond
        (setup.speedMagnitude .before .B) = 0

/-- Positive, nondegenerate physical masses for the two pucks. -/
structure HasPhysicalPuckMasses
    (setup : ElasticPuckCollisionSetup) : Prop where
  eachPuckHasPositiveMass :
    ∀ puck, 0 < massInKilograms (setup.puckMass puck)

/-!
Primary-image evidence from `816.png`.  The image supplies the mass and two
A-speed labels, identifies B as initially at rest, and shows B's final arrow
without a numerical speed label.  Thus this structure cannot contain the
requested answer.
-/
structure MatchesSuppliedPuckCollisionFigure
    (setup : ElasticPuckCollisionSetup) : Prop where
  bothPanelTitlesShown :
    ∀ stage, setup.figure.panelTitleShown stage = true
  bothOriginsLabelled :
    ∀ stage, setup.figure.originLabelShown stage = true
  bothCoordinateFramesShown :
    ∀ stage axis, setup.figure.axisShown stage axis = true
  positiveXPointsRight :
    ∀ stage, setup.figure.positiveXAxisPointsRight stage = true
  positiveYPointsUp :
    ∀ stage, setup.figure.positiveYAxisPointsUp stage = true
  bothPucksShownInBothPanels :
    ∀ stage puck, setup.figure.puckShown stage puck = true
  displayedMassOfA : setup.figure.massLabelKilograms .A = 1 / 2
  displayedMassOfB : setup.figure.massLabelKilograms .B = 3 / 10
  initialArrowForAIsShown :
    setup.figure.velocityArrowShown .before .A = true
  initialArrowForAPointsAlongPositiveX :
    setup.figure.velocityArrowDirection .before .A = .positiveX
  noInitialVelocityArrowForB :
    setup.figure.velocityArrowShown .before .B = false
  puckBIsLabelledAtRest : setup.figure.initialRestTextShownForB = true
  finalArrowForAIsShown :
    setup.figure.velocityArrowShown .after .A = true
  finalArrowForAPointsAbovePositiveX :
    setup.figure.velocityArrowDirection .after .A = .abovePositiveX
  finalArrowForBIsShown :
    setup.figure.velocityArrowShown .after .B = true
  finalArrowForBPointsBelowPositiveX :
    setup.figure.velocityArrowDirection .after .B = .belowPositiveX
  displayedInitialSpeedOfA :
    setup.figure.displayedSpeedMetersPerSecond .before .A = some 4
  displayedFinalSpeedOfA :
    setup.figure.displayedSpeedMetersPerSecond .after .A = some 2
  noDisplayedFinalSpeedForB :
    setup.figure.displayedSpeedMetersPerSecond .after .B = none
  bothOutgoingAngleLabelsShown :
    ∀ angle, setup.figure.angleLabelShown angle = true
  bothAnglesUsePositiveXAxis :
    ∀ angle,
      setup.figure.angleMeasuredFromPositiveXAxis angle = true

/-!
Every scalar speed field is the Euclidean magnitude of its associated planar
velocity vector.  This is a kinematic relation, not a numerical answer for B.
-/
structure HasVelocityMagnitudeKinematics
    (setup : ElasticPuckCollisionSetup) : Prop where
  speedIsVelocityNorm :
    ∀ (stage : CollisionStage) (puck : PuckLabel)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedMagnitudeReadout lengthUnit timeUnit
          (setup.speedMagnitude stage puck) =
        ‖planarVelocityReadout lengthUnit timeUnit
          (setup.velocity stage puck)‖

/-!
Cartesian realization of the directions shown in the image.  `alpha` is
measured counterclockwise above positive `x`; `beta` is represented as a
positive magnitude measured clockwise below positive `x`, hence B's negative
`y` component.
-/
structure MatchesFigureVelocityGeometry
    (setup : ElasticPuckCollisionSetup) : Prop where
  alphaIsAcute : 0 < setup.alphaRadians ∧ setup.alphaRadians < Real.pi / 2
  betaIsAcute : 0 < setup.betaRadians ∧ setup.betaRadians < Real.pi / 2
  initialAAlongPositiveX :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (setup.velocity .before .A) xAxis =
        speedMagnitudeReadout lengthUnit timeUnit
          (setup.speedMagnitude .before .A)
  initialAHasZeroYComponent :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (setup.velocity .before .A) yAxis = 0
  initialBIsAtRest :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (setup.velocity .before .B) = 0
  finalAXComponent :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (setup.velocity .after .A) xAxis =
        speedMagnitudeReadout lengthUnit timeUnit
            (setup.speedMagnitude .after .A) *
          Real.cos setup.alphaRadians
  finalAYComponent :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (setup.velocity .after .A) yAxis =
        speedMagnitudeReadout lengthUnit timeUnit
            (setup.speedMagnitude .after .A) *
          Real.sin setup.alphaRadians
  finalBXComponent :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (setup.velocity .after .B) xAxis =
        speedMagnitudeReadout lengthUnit timeUnit
            (setup.speedMagnitude .after .B) *
          Real.cos setup.betaRadians
  finalBYComponent :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (setup.velocity .after .B) yAxis =
        -(speedMagnitudeReadout lengthUnit timeUnit
            (setup.speedMagnitude .after .B) *
          Real.sin setup.betaRadians)

/-!
The governing laws for an isolated elastic two-puck collision.  Momentum is a
two-dimensional vector equation.  Kinetic energy uses the classical
`(1/2) m v²` expression.  Both laws hold in arbitrary coherent base units and
constrain, but do not state, B's requested final speed.
-/
structure SatisfiesElasticCollisionConservationLaws
    (setup : ElasticPuckCollisionSetup) : Prop where
  planarLinearMomentumConserved :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit (setup.puckMass .A) •
            planarVelocityReadout lengthUnit timeUnit
              (setup.velocity .before .A) +
          massReadout massUnit (setup.puckMass .B) •
            planarVelocityReadout lengthUnit timeUnit
              (setup.velocity .before .B) =
        massReadout massUnit (setup.puckMass .A) •
            planarVelocityReadout lengthUnit timeUnit
              (setup.velocity .after .A) +
          massReadout massUnit (setup.puckMass .B) •
            planarVelocityReadout lengthUnit timeUnit
              (setup.velocity .after .B)
  kineticEnergyConserved :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      (1 / 2 : ℝ) * massReadout massUnit (setup.puckMass .A) *
            speedMagnitudeReadout lengthUnit timeUnit
                (setup.speedMagnitude .before .A) ^ 2 +
          (1 / 2 : ℝ) * massReadout massUnit (setup.puckMass .B) *
            speedMagnitudeReadout lengthUnit timeUnit
                (setup.speedMagnitude .before .B) ^ 2 =
        (1 / 2 : ℝ) * massReadout massUnit (setup.puckMass .A) *
            speedMagnitudeReadout lengthUnit timeUnit
                (setup.speedMagnitude .after .A) ^ 2 +
          (1 / 2 : ℝ) * massReadout massUnit (setup.puckMass .B) *
            speedMagnitudeReadout lengthUnit timeUnit
                (setup.speedMagnitude .after .B) ^ 2

/-! ## Exact speed and displayed answer target -/

/-- The four speed-answer labels displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in `m/s` printed beside each displayed answer choice. -/
def AnswerChoice.speedMetersPerSecond : AnswerChoice → ℝ
  | .A => 381 / 100
  | .B => 447 / 100
  | .C => 296 / 100
  | .D => 362 / 100

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Absolute discrepancy between B's physical final speed and one choice. -/
def answerChoiceErrorMetersPerSecond
    (setup : ElasticPuckCollisionSetup) (choice : AnswerChoice) : ℝ :=
  |speedMagnitudeInMetersPerSecond
      (setup.speedMagnitude .after .B) - choice.speedMetersPerSecond|

/-- Agreement with a speed displayed to the nearest `0.01 m/s`. -/
def MatchesDisplayedSpeed
    (setup : ElasticPuckCollisionSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorMetersPerSecond setup choice ≤ (1 : ℝ) / 200

/-- A displayed speed is strictly closer than every alternative. -/
def IsUniqueClosestSpeedChoice
    (setup : ElasticPuckCollisionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMetersPerSecond setup choice <
      answerChoiceErrorMetersPerSecond setup other

/--
Energy conservation and the stated readouts determine the square of B's final
speed to be `20 (m/s)²`.
-/
lemma puckBFinalSpeedSquared
    (setup : ElasticPuckCollisionSetup)
    (_data : MatchesPuckCollisionProblemData setup)
    (_laws : SatisfiesElasticCollisionConservationLaws setup) :
    speedMagnitudeInMetersPerSecond
        (setup.speedMagnitude .after .B) ^ 2 = 20 := by
  have henergy :=
    _laws.kineticEnergyConserved
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change (1 / 2 : ℝ) * massInKilograms (setup.puckMass .A) *
        speedMagnitudeInMetersPerSecond
            (setup.speedMagnitude .before .A) ^ 2 +
      (1 / 2 : ℝ) * massInKilograms (setup.puckMass .B) *
        speedMagnitudeInMetersPerSecond
            (setup.speedMagnitude .before .B) ^ 2 =
    (1 / 2 : ℝ) * massInKilograms (setup.puckMass .A) *
        speedMagnitudeInMetersPerSecond
            (setup.speedMagnitude .after .A) ^ 2 +
      (1 / 2 : ℝ) * massInKilograms (setup.puckMass .B) *
        speedMagnitudeInMetersPerSecond
            (setup.speedMagnitude .after .B) ^ 2 at henergy
  rw [_data.puckAMassKilograms, _data.puckBMassKilograms,
    _data.puckAInitialSpeedMetersPerSecond,
    _data.puckAFinalSpeedMetersPerSecond,
    _data.puckBInitialSpeedMetersPerSecond] at henergy
  norm_num at henergy ⊢
  nlinarith

/-- B's exact final speed is `sqrt 20 m/s`. -/
lemma puckBFinalSpeedExact
    (setup : ElasticPuckCollisionSetup)
    (_data : MatchesPuckCollisionProblemData setup)
    (_laws : SatisfiesElasticCollisionConservationLaws setup) :
    speedMagnitudeInMetersPerSecond
        (setup.speedMagnitude .after .B) = Real.sqrt 20 := by
  have hsq := puckBFinalSpeedSquared setup _data _laws
  have hnonneg : 0 ≤ speedMagnitudeInMetersPerSecond
      (setup.speedMagnitude .after .B) := by
    unfold speedMagnitudeInMetersPerSecond speedMagnitudeReadout
    positivity
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)
  have hsqrt_nonneg := Real.sqrt_nonneg (20 : ℝ)
  nlinarith

/--
In the supplied elastic-collision scenario, puck B leaves with exact speed
`sqrt 20 m/s`, which rounds to `4.47 m/s`; displayed choice B is uniquely
closest.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0816:target`.
-/
theorem elasticPuckCollision_finalSpeed
    (setup : ElasticPuckCollisionSetup)
    (_scenario : MatchesElasticAirHockeyScenario setup)
    (_data : MatchesPuckCollisionProblemData setup)
    (_physical : HasPhysicalPuckMasses setup)
    (_figure : MatchesSuppliedPuckCollisionFigure setup)
    (_kinematics : HasVelocityMagnitudeKinematics setup)
    (_geometry : MatchesFigureVelocityGeometry setup)
    (_laws : SatisfiesElasticCollisionConservationLaws setup) :
    speedMagnitudeInMetersPerSecond
          (setup.speedMagnitude .after .B) = Real.sqrt 20 ∧
      MatchesDisplayedSpeed setup .B ∧
      IsUniqueClosestSpeedChoice setup .B := by
  have hExact := puckBFinalSpeedExact setup _data _laws
  have hsqrt_nonneg : 0 ≤ Real.sqrt (20 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (20 : ℝ)) ^ 2 = 20 :=
    Real.sq_sqrt (by norm_num)
  have hlo : (447 : ℝ) / 100 ≤ Real.sqrt 20 := by
    nlinarith
  have hhi : Real.sqrt 20 ≤ (895 : ℝ) / 200 := by
    nlinarith
  refine ⟨hExact, ?_, ?_⟩
  · unfold MatchesDisplayedSpeed answerChoiceErrorMetersPerSecond
    rw [hExact]
    change |Real.sqrt 20 - (447 : ℝ) / 100| ≤ (1 : ℝ) / 200
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · intro other hne
    cases other with
    | A =>
        unfold answerChoiceErrorMetersPerSecond
        rw [hExact]
        change |Real.sqrt 20 - (447 : ℝ) / 100| <
          |Real.sqrt 20 - (381 : ℝ) / 100|
        rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
        norm_num
    | B => exact (hne rfl).elim
    | C =>
        unfold answerChoiceErrorMetersPerSecond
        rw [hExact]
        change |Real.sqrt 20 - (447 : ℝ) / 100| <
          |Real.sqrt 20 - (296 : ℝ) / 100|
        rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
        norm_num
    | D =>
        unfold answerChoiceErrorMetersPerSecond
        rw [hExact]
        change |Real.sqrt 20 - (447 : ℝ) / 100| <
          |Real.sqrt 20 - (362 : ℝ) / 100|
        rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
        norm_num

end PhyXMiniProblems.ProblemPhyXMini0816
