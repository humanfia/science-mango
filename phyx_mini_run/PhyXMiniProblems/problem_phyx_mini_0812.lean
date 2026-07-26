import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Crate sliding up and back down a rough ramp

A `12 kg` crate is launched from the bottom of a `2.5 m` ramp inclined at
`30 degrees`.  It initially moves up the ramp at `5.0 m/s`, stops after
travelling `1.6 m`, and then slides back to the bottom.  The supplied figure
labels the launch point as point 1, the turning point as point 2, and the
return point at the same base location as point 3.

Mass, length, speed, acceleration, force, and energy remain unit-independent
Physlib quantities.  Real numbers are used only for coherent-unit readouts,
the dimensionless angle, and displayed multiple-choice values.

Assumption/target boundary:

* `MatchesRampProblemData` records the stated mass, standard terrestrial
  gravity, the worker's frictionless planning model, release after launch,
  and the actual non-negligible kinetic-friction regime.
* `MatchesPrimaryRampFigure` records the objects, labels, geometry, distances,
  angle, and the point-1 and point-2 speed labels visible in the raster.
* `SatisfiesInclineWorkEnergyLaws` states the kinetic-energy formula and the
  work--energy equations on the upward and downward legs.
* There are no previous-part results.
* The return speed and choice B occur only in the final theorem conclusion and
  in the table of displayed answer choices, never in a premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0812

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T^-2`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the chosen readout units. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length or distance. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A physical energy, represented by Physlib's energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a nonnegative dimensionful scalar in a coherent unit system. -/
def nonnegativeQuantityReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a physical energy in the coherent energy unit induced by `units`. -/
def energyReadout (units : UnitChoices) (energy : EnergyQuantity) : ℝ :=
  (energy units).val

/-- Kilogram readout of the crate's mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI mass

/-- Metre readout of a ramp length or distance. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI length

/-- Metres-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI speed

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI acceleration

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI force

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  energyReadout UnitChoices.SI energy

/-!
The classical scalar kinetic-energy expression in any coherent unit system.
This is a general physical formula helper and contains no problem answer.
-/
def kineticEnergyFromReadouts
    (units : UnitChoices) (mass : MassQuantity) (speed : SpeedQuantity) : ℝ :=
  (1 / 2 : ℝ) * nonnegativeQuantityReadout units mass *
    nonnegativeQuantityReadout units speed ^ 2

/-! ## Primary-figure labels and independent physical setup -/

/-- The three points explicitly numbered in the supplied figure. -/
inductive RampPoint where
  | point1BottomLaunch
  | point2Turning
  | point3BottomReturn
  deriving DecidableEq, Fintype, Repr

/-- The two directions of travel along the ramp. -/
inductive AlongRampDirection where
  | upRamp
  | downRamp
  deriving DecidableEq, Repr

/-- Individually identifiable objects visible in the supplied raster. -/
inductive FigureComponent where
  | worker
  | crate
  | ramp
  | truck
  | greenVelocityArrow
  deriving DecidableEq, Fintype, Repr

/-- Whether friction is omitted or retained in a model. -/
inductive FrictionModel where
  | ignored
  | nonnegligibleKinetic
  deriving DecidableEq, Repr

/-- The worker's qualitative prediction under his frictionless calculation. -/
inductive WorkerPrediction where
  | crateReachesTruckBed
  deriving DecidableEq, Repr

/-!
Literal labels and qualitative geometry transcribed from the primary image.
Point 3 has no speed label: its speed is the requested unknown.
-/
structure RampFigure where
  componentShown : FigureComponent → Bool
  pointLabelShown : RampPoint → Bool
  point1AndPoint3CoincideAtBase : Bool
  point2LiesBetweenBaseAndRampTop : Bool
  returnPathRetracesAscent : Bool
  velocityArrowAtPoint1Direction : AlongRampDirection
  rampLengthLabelMeters : ℝ
  turningDistanceLabelMeters : ℝ
  inclineAngleLabelDegrees : ℝ
  speedLabelMetersPerSecond : RampPoint → Option ℝ

/-!
Independent quantities describing the crate and ramp.  In particular,
`speedAt .point3BottomReturn` is not defined from an answer choice.
-/
structure CrateRampSetup where
  figure : RampFigure
  crateMass : MassQuantity
  rampLength : LengthQuantity
  upwardTravelDistance : LengthQuantity
  returnTravelDistance : LengthQuantity
  speedAt : RampPoint → SpeedQuantity
  kineticEnergyAt : RampPoint → EnergyQuantity
  gravitationalAcceleration : AccelerationQuantity
  kineticFrictionMagnitude : ForceQuantity
  inclineAngleRadians : ℝ
  workerFrictionModel : FrictionModel
  actualFrictionModel : FrictionModel
  workerPrediction : WorkerPrediction
  crateReleasedAfterLaunch : Bool

/-! ## Problem data, primary-image evidence, and governing laws -/

/-!
Prose/model data not supplied as literal graphical labels.  Standard gravity
is the terrestrial calibration implicit in the numerical mechanics problem.
-/
structure MatchesRampProblemData (setup : CrateRampSetup) : Prop where
  crateMassKilograms : massInKilograms setup.crateMass = 12
  standardGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5
  workerIgnoredFriction : setup.workerFrictionModel = .ignored
  workerExpectedToReachTruck :
    setup.workerPrediction = .crateReachesTruckBed
  actualFrictionIsNonnegligible :
    setup.actualFrictionModel = .nonnegligibleKinetic
  releasedAfterInitialPush : setup.crateReleasedAfterLaunch = true

/-!
Primary-raster evidence and its calibration to the physical quantities.
The point-3 speed label is explicitly absent, so no return-speed value enters
this premise.
-/
structure MatchesPrimaryRampFigure (setup : CrateRampSetup) : Prop where
  allComponentsShown : ∀ component, setup.figure.componentShown component = true
  allPointLabelsShown : ∀ point, setup.figure.pointLabelShown point = true
  points1And3AtSameBaseLocation :
    setup.figure.point1AndPoint3CoincideAtBase = true
  point2IsOnRampBeforeTop :
    setup.figure.point2LiesBetweenBaseAndRampTop = true
  returnRetracesUpwardPath : setup.figure.returnPathRetracesAscent = true
  point1ArrowPointsUpRamp :
    setup.figure.velocityArrowAtPoint1Direction = .upRamp
  rampLengthLabel : setup.figure.rampLengthLabelMeters = 5 / 2
  turningDistanceLabel : setup.figure.turningDistanceLabelMeters = 8 / 5
  inclineAngleLabel : setup.figure.inclineAngleLabelDegrees = 30
  point1SpeedLabel :
    setup.figure.speedLabelMetersPerSecond .point1BottomLaunch = some 5
  point2SpeedLabel :
    setup.figure.speedLabelMetersPerSecond .point2Turning = some 0
  point3SpeedIsUnlabeled :
    setup.figure.speedLabelMetersPerSecond .point3BottomReturn = none
  physicalRampLengthMatchesLabel :
    lengthInMeters setup.rampLength = setup.figure.rampLengthLabelMeters
  physicalTurningDistanceMatchesLabel :
    lengthInMeters setup.upwardTravelDistance =
      setup.figure.turningDistanceLabelMeters
  physicalPoint1SpeedMatchesLabel :
    speedInMetersPerSecond (setup.speedAt .point1BottomLaunch) = 5
  physicalPoint2SpeedMatchesLabel :
    speedInMetersPerSecond (setup.speedAt .point2Turning) = 0
  angleLabelMatchesRadians :
    setup.inclineAngleRadians =
      setup.figure.inclineAngleLabelDegrees * Real.pi / 180
  equalDistancesOnRetracedPath :
    setup.returnTravelDistance = setup.upwardTravelDistance

/-! Positivity conditions selecting the intended physical ramp model. -/
structure HasPhysicalRampParameters (setup : CrateRampSetup) : Prop where
  crateMassPositive : 0 < massInKilograms setup.crateMass
  rampLengthPositive : 0 < lengthInMeters setup.rampLength
  upwardDistancePositive : 0 < lengthInMeters setup.upwardTravelDistance
  turningPointBeforeRampTop :
    lengthInMeters setup.upwardTravelDistance < lengthInMeters setup.rampLength
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  frictionMagnitudePositive : 0 < forceInNewtons setup.kineticFrictionMagnitude
  inclineAnglePositive : 0 < setup.inclineAngleRadians
  inclineAngleAcute : setup.inclineAngleRadians < Real.pi / 2
  kineticEnergiesNonnegative :
    ∀ point, 0 ≤ energyInJoules (setup.kineticEnergyAt point)

/-!
The classical work--energy model for the two legs.

* Every stored kinetic energy is related to its independent speed and mass by
  `K = (1/2) m v^2`.
* On the upward leg, both gravity's incline component and kinetic friction do
  negative work.
* On the downward leg, gravity does positive work and the same kinetic
  friction magnitude does negative work.

These laws hold in every coherent unit system and contain no numerical return
speed or answer-choice label.
-/
structure SatisfiesInclineWorkEnergyLaws (setup : CrateRampSetup) : Prop where
  kineticEnergyFormula : ∀ (units : UnitChoices) (point : RampPoint),
    energyReadout units (setup.kineticEnergyAt point) =
      kineticEnergyFromReadouts units setup.crateMass (setup.speedAt point)
  upwardLegWorkEnergy : ∀ units : UnitChoices,
    energyReadout units (setup.kineticEnergyAt .point2Turning) -
        energyReadout units (setup.kineticEnergyAt .point1BottomLaunch) =
      -(nonnegativeQuantityReadout units setup.crateMass *
          nonnegativeQuantityReadout units setup.gravitationalAcceleration *
          Real.sin setup.inclineAngleRadians *
          nonnegativeQuantityReadout units setup.upwardTravelDistance) -
        nonnegativeQuantityReadout units setup.kineticFrictionMagnitude *
          nonnegativeQuantityReadout units setup.upwardTravelDistance
  downwardLegWorkEnergy : ∀ units : UnitChoices,
    energyReadout units (setup.kineticEnergyAt .point3BottomReturn) -
        energyReadout units (setup.kineticEnergyAt .point2Turning) =
      nonnegativeQuantityReadout units setup.crateMass *
          nonnegativeQuantityReadout units setup.gravitationalAcceleration *
          Real.sin setup.inclineAngleRadians *
          nonnegativeQuantityReadout units setup.returnTravelDistance -
        nonnegativeQuantityReadout units setup.kineticFrictionMagnitude *
          nonnegativeQuantityReadout units setup.returnTravelDistance

/-! ## Displayed answers and formalization target -/

/-- Labels attached to the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in metres per second printed beside each answer choice. -/
def AnswerChoice.displayedSpeedMetersPerSecond : AnswerChoice → ℝ
  | .A => 16 / 5
  | .B => 5 / 2
  | .C => 5
  | .D => 3 / 2

/-!
An answer is closest when its printed speed has no greater absolute error than
any other printed option.  This makes the dataset's rounding explicit.
-/
def IsClosestAnswerChoice
    (actualSpeedMetersPerSecond : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |actualSpeedMetersPerSecond - selected.displayedSpeedMetersPerSecond| ≤
      |actualSpeedMetersPerSecond - other.displayedSpeedMetersPerSecond|

/-!
The work--energy equations give the exact idealized return speed
`sqrt (159/25) m/s`, approximately `2.52 m/s`; hence the displayed `2.5 m/s`
value, choice B, is closest.

This formalizes blueprint label `thm:physics:phyx_mini_0812:target`.
-/
theorem returnSpeedAtRampBottom_is_answerB
    (setup : CrateRampSetup)
    (hProblem : MatchesRampProblemData setup)
    (hFigure : MatchesPrimaryRampFigure setup)
    (hPhysical : HasPhysicalRampParameters setup)
    (hLaws : SatisfiesInclineWorkEnergyLaws setup) :
    speedInMetersPerSecond (setup.speedAt .point3BottomReturn) =
        Real.sqrt (159 / 25 : ℝ) ∧
      IsClosestAnswerChoice
        (speedInMetersPerSecond (setup.speedAt .point3BottomReturn)) .B := by
  have hMass :
      nonnegativeQuantityReadout UnitChoices.SI setup.crateMass = 12 := by
    simpa [massInKilograms] using hProblem.crateMassKilograms
  have hGravity :
      nonnegativeQuantityReadout UnitChoices.SI
          setup.gravitationalAcceleration =
        49 / 5 := by
    simpa [accelerationInMetersPerSecondSquared] using
      hProblem.standardGravityMetersPerSecondSquared
  have hDistance :
      nonnegativeQuantityReadout UnitChoices.SI
          setup.upwardTravelDistance =
        8 / 5 := by
    simpa [lengthInMeters] using
      hFigure.physicalTurningDistanceMatchesLabel.trans
        hFigure.turningDistanceLabel
  have hReturnDistance :
      nonnegativeQuantityReadout UnitChoices.SI setup.returnTravelDistance =
        8 / 5 := by
    rw [hFigure.equalDistancesOnRetracedPath]
    exact hDistance
  have hInitialSpeed :
      nonnegativeQuantityReadout UnitChoices.SI
          (setup.speedAt .point1BottomLaunch) =
        5 := by
    simpa [speedInMetersPerSecond] using
      hFigure.physicalPoint1SpeedMatchesLabel
  have hTurningSpeed :
      nonnegativeQuantityReadout UnitChoices.SI
          (setup.speedAt .point2Turning) =
        0 := by
    simpa [speedInMetersPerSecond] using
      hFigure.physicalPoint2SpeedMatchesLabel
  have hAngle : setup.inclineAngleRadians = Real.pi / 6 := by
    calc
      setup.inclineAngleRadians =
          setup.figure.inclineAngleLabelDegrees * Real.pi / 180 :=
        hFigure.angleLabelMatchesRadians
      _ = 30 * Real.pi / 180 := by rw [hFigure.inclineAngleLabel]
      _ = Real.pi / 6 := by ring
  have hUp := hLaws.upwardLegWorkEnergy UnitChoices.SI
  have hDown := hLaws.downwardLegWorkEnergy UnitChoices.SI
  rw [hLaws.kineticEnergyFormula UnitChoices.SI .point2Turning,
      hLaws.kineticEnergyFormula UnitChoices.SI .point1BottomLaunch] at hUp
  rw [hLaws.kineticEnergyFormula UnitChoices.SI .point3BottomReturn,
      hLaws.kineticEnergyFormula UnitChoices.SI .point2Turning] at hDown
  norm_num [kineticEnergyFromReadouts, hMass, hGravity, hDistance,
    hReturnDistance, hInitialSpeed, hTurningSpeed, hAngle,
    Real.sin_pi_div_six] at hUp hDown
  have hSpeedSq :
      speedInMetersPerSecond (setup.speedAt .point3BottomReturn) ^ 2 =
        (159 / 25 : ℝ) := by
    unfold speedInMetersPerSecond
    nlinarith [hUp, hDown]
  have hSpeedNonneg :
      0 ≤ speedInMetersPerSecond (setup.speedAt .point3BottomReturn) := by
    unfold speedInMetersPerSecond nonnegativeQuantityReadout
    exact NNReal.coe_nonneg _
  have hRadicand : 0 ≤ (159 / 25 : ℝ) := by norm_num
  have hSqrtSq : (Real.sqrt (159 / 25 : ℝ)) ^ 2 = 159 / 25 := by
    exact Real.sq_sqrt hRadicand
  have hSpeed :
      speedInMetersPerSecond (setup.speedAt .point3BottomReturn) =
        Real.sqrt (159 / 25 : ℝ) := by
    nlinarith [hSpeedSq, hSqrtSq, Real.sqrt_nonneg (159 / 25 : ℝ)]
  constructor
  · exact hSpeed
  · rw [hSpeed]
    have hLower : (5 / 2 : ℝ) ≤ Real.sqrt (159 / 25 : ℝ) := by
      nlinarith [hSqrtSq, Real.sqrt_nonneg (159 / 25 : ℝ)]
    have hUpper : Real.sqrt (159 / 25 : ℝ) ≤ 57 / 20 := by
      nlinarith [hSqrtSq, Real.sqrt_nonneg (159 / 25 : ℝ)]
    intro other
    cases other <;>
      simp only [AnswerChoice.displayedSpeedMetersPerSecond]
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · exact le_rfl
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0812
