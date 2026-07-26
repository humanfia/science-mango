import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0828

open Dimension

/-!
# Ground speed of a plane in a crosswind

Cleveland is 300 miles east of Chicago. A plane leaves Chicago with an
eastward air-relative velocity of 500 miles per hour, while the air moves
south relative to the ground at 50 miles per hour. The supplied vector
diagram labels the air-relative plane velocity `vPA`, the ground-relative
plane velocity `vPG`, and the ground-relative air velocity `vAG`.

Positions, distances, velocities, and speeds below are unit-independent
Physlib quantities. Real scalars occur only at explicitly named mile or
mile-per-hour readout boundaries. The current target--the plane's numerical
ground speed--does not occur in any setup, data, figure, or law field.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- Velocity has physical dimension length divided by time. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The Euclidean plane in which the city positions and velocity components are read. -/
abbrev PlaneReadout : Type := EuclideanSpace ℝ (Fin 2)

/-- A nonnegative, unit-independent physical distance. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude supplied by Physlib. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A unit-independent signed planar position. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 PlaneReadout)

/-- A unit-independent signed planar velocity. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension PlaneReadout)

/-- Read a physical distance in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a planar position in a selected length unit. -/
def planarPositionReadout
    (unit : LengthUnit) (position : PlanarPositionQuantity) : PlaneReadout :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a planar velocity in coherent selected length and time units. -/
def planarVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocityQuantity) : PlaneReadout :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Mile readout used for the Chicago--Cleveland separation. -/
def lengthInMiles (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.miles length

/-- Mile-per-hour readout used for all speeds in the problem and choices. -/
def speedInMilesPerHour (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.miles TimeUnit.hours speed

/-- Planar position read in miles, with east as positive x and north as positive y. -/
def positionInMiles (position : PlanarPositionQuantity) : PlaneReadout :=
  planarPositionReadout LengthUnit.miles position

/-- Planar velocity read in miles per hour in the same east/north coordinates. -/
def velocityInMilesPerHour (velocity : PlanarVelocityQuantity) : PlaneReadout :=
  planarVelocityReadout LengthUnit.miles TimeUnit.hours velocity

/-! ## Named objects, reference bodies, and figure vocabulary -/

/-- The two cities named in the written scenario and drawn as black dots. -/
inductive CityLabel where
  | chicago
  | cleveland
  deriving DecidableEq, Fintype, Repr

/-- Bodies used to interpret the two-letter subscripts on relative velocities. -/
inductive PhysicalBody where
  | plane
  | air
  | ground
  deriving DecidableEq, Fintype, Repr

/-- The three literal vector labels printed in primary image `828.png`. -/
inductive RelativeVelocityLabel where
  | vPA
  | vPG
  | vAG
  deriving DecidableEq, Fintype, Repr

/-- The moving body denoted by the first letter of each velocity subscript. -/
def movingBody : RelativeVelocityLabel → PhysicalBody
  | .vPA => .plane
  | .vPG => .plane
  | .vAG => .air

/-- The reference body denoted by the second letter of each velocity subscript. -/
def referenceBody : RelativeVelocityLabel → PhysicalBody
  | .vPA => .air
  | .vPG => .ground
  | .vAG => .ground

/-- Cardinal directions needed to transcribe the prose data. -/
inductive CardinalDirection where
  | east
  | south
  deriving DecidableEq, Repr

/-- The pilot's stated knowledge of the wind before departure. -/
inductive PilotWindKnowledge where
  | unawareOfSouthWind
  | awareOfSouthWind
  deriving DecidableEq, Repr

/-- Distinguished endpoints in the head-to-tail vector diagram. -/
inductive FigurePoint where
  | chicago
  | cleveland
  | driftedGroundEndpoint
  deriving DecidableEq, Fintype, Repr

/-- Physical and graphical objects visible in the supplied image. -/
inductive FigureObject where
  | chicagoDot
  | clevelandDot
  | airRelativePlane
  | groundRelativePlane
  | velocityArrowVPA
  | velocityArrowVPG
  | velocityArrowVAG
  deriving DecidableEq, Fintype, Repr

/-- Literal city and vector-description text printed in the supplied image. -/
inductive FigureTextLabel where
  | chicago
  | cleveland
  | vPAPlaneRelativeToAir
  | vPGPlaneRelativeToGround
  | vAGAir
  deriving DecidableEq, Fintype, Repr

/-!
Typed primary-image data. The diagram's three vector values remain physical
planar velocities. Arrow endpoints record the head-to-tail geometry without
postulating any numerical value for `vPG`.
-/
structure SuppliedVelocityDiagram where
  showsObject : FigureObject → Bool
  showsText : FigureTextLabel → Bool
  velocityShown : RelativeVelocityLabel → PlanarVelocityQuantity
  arrowStart : RelativeVelocityLabel → FigurePoint
  arrowEnd : RelativeVelocityLabel → FigurePoint
  showsPlaneIconAlong : RelativeVelocityLabel → Bool

/-!
Independent physical observables in the written problem. In particular,
`planeVelocityRelativeToGround` and `planeGroundSpeed` are unconstrained here;
their relation to the given velocities is supplied only by governing laws.
-/
structure PlaneWindSetup where
  cityPosition : CityLabel → PlanarPositionQuantity
  chicagoToClevelandDistance : LengthQuantity
  planeAirspeed : SpeedQuantity
  windSpeed : SpeedQuantity
  planeVelocityRelativeToAir : PlanarVelocityQuantity
  airVelocityRelativeToGround : PlanarVelocityQuantity
  planeVelocityRelativeToGround : PlanarVelocityQuantity
  planeGroundSpeed : SpeedQuantity
  intendedDestination : CityLabel
  planeHeadingRelativeToAir : CardinalDirection
  windDirectionRelativeToGround : CardinalDirection
  pilotWindKnowledge : PilotWindKnowledge
  figure : SuppliedVelocityDiagram

/-! ## Scenario, figure evidence, stated data, and governing laws -/

/-!
Qualitative prose and primary-image facts. These fields identify the three
pictured velocity vectors but do not give the magnitude of `vPG` or the
plane's ground speed.
-/
structure MatchesScenarioAndSuppliedFigure (setup : PlaneWindSetup) : Prop where
  intendedDestinationIsCleveland : setup.intendedDestination = .cleveland
  dueEastHeading : setup.planeHeadingRelativeToAir = .east
  southWind : setup.windDirectionRelativeToGround = .south
  pilotDidNotKnowWind : setup.pilotWindKnowledge = .unawareOfSouthWind
  everyFigureObjectShown : ∀ object, setup.figure.showsObject object = true
  everyFigureTextShown : ∀ label, setup.figure.showsText label = true
  airRelativePlaneIconShown :
    setup.figure.showsPlaneIconAlong .vPA = true
  groundRelativePlaneIconShown :
    setup.figure.showsPlaneIconAlong .vPG = true
  noPlaneIconOnAirVelocity :
    setup.figure.showsPlaneIconAlong .vAG = false
  vPAStartsAtChicago : setup.figure.arrowStart .vPA = .chicago
  vPAEndsAtCleveland : setup.figure.arrowEnd .vPA = .cleveland
  vAGStartsAtCleveland : setup.figure.arrowStart .vAG = .cleveland
  vAGEndsAtDriftedEndpoint :
    setup.figure.arrowEnd .vAG = .driftedGroundEndpoint
  vPGStartsAtChicago : setup.figure.arrowStart .vPG = .chicago
  vPGEndsAtDriftedEndpoint :
    setup.figure.arrowEnd .vPG = .driftedGroundEndpoint
  vPALabelMeansPlaneRelativeToAir :
    setup.figure.velocityShown .vPA = setup.planeVelocityRelativeToAir
  vPGLabelMeansPlaneRelativeToGround :
    setup.figure.velocityShown .vPG = setup.planeVelocityRelativeToGround
  vAGLabelMeansAirRelativeToGround :
    setup.figure.velocityShown .vAG = setup.airVelocityRelativeToGround

/-!
The numerical values and directions explicitly given in the prose. East is
positive x and north is positive y, so a southward component is negative.
No field assigns a component or magnitude to the ground-relative velocity.
-/
structure StatedPlaneWindData (setup : PlaneWindSetup) : Prop where
  clevelandDisplacementFromChicago :
    positionInMiles (setup.cityPosition .cleveland) -
        positionInMiles (setup.cityPosition .chicago) =
      !₂[300, 0]
  citySeparationMiles :
    lengthInMiles setup.chicagoToClevelandDistance = 300
  planeAirspeedMilesPerHour :
    speedInMilesPerHour setup.planeAirspeed = 500
  windSpeedMilesPerHour :
    speedInMilesPerHour setup.windSpeed = 50
  planeVelocityDueEast :
    velocityInMilesPerHour setup.planeVelocityRelativeToAir =
      !₂[speedInMilesPerHour setup.planeAirspeed, 0]
  windVelocityDueSouth :
    velocityInMilesPerHour setup.airVelocityRelativeToGround =
      !₂[0, -speedInMilesPerHour setup.windSpeed]

/-!
Governing geometry and Galilean kinematics. Each law is stated for every
coherent choice of length and time units. The final numerical ground speed is
not a law field: it must be derived by adding `vPA` and `vAG` and taking the
Euclidean norm of `vPG`.
-/
structure PlaneWindKinematicsLaws (setup : PlaneWindSetup) : Prop where
  cityDistanceIsDisplacementMagnitude :
    ∀ lengthUnit,
      lengthReadout lengthUnit setup.chicagoToClevelandDistance =
        ‖planarPositionReadout lengthUnit (setup.cityPosition .cleveland) -
          planarPositionReadout lengthUnit (setup.cityPosition .chicago)‖
  airspeedIsVelocityMagnitude :
    ∀ lengthUnit timeUnit,
      speedReadout lengthUnit timeUnit setup.planeAirspeed =
        ‖planarVelocityReadout lengthUnit timeUnit
          setup.planeVelocityRelativeToAir‖
  windSpeedIsVelocityMagnitude :
    ∀ lengthUnit timeUnit,
      speedReadout lengthUnit timeUnit setup.windSpeed =
        ‖planarVelocityReadout lengthUnit timeUnit
          setup.airVelocityRelativeToGround‖
  relativeVelocityAddition :
    ∀ lengthUnit timeUnit,
      planarVelocityReadout lengthUnit timeUnit
          setup.planeVelocityRelativeToGround =
        planarVelocityReadout lengthUnit timeUnit
            setup.planeVelocityRelativeToAir +
          planarVelocityReadout lengthUnit timeUnit
            setup.airVelocityRelativeToGround
  groundSpeedIsVelocityMagnitude :
    ∀ lengthUnit timeUnit,
      speedReadout lengthUnit timeUnit setup.planeGroundSpeed =
        ‖planarVelocityReadout lengthUnit timeUnit
          setup.planeVelocityRelativeToGround‖

/-! ## Answer choices and target -/

/-- The four answer-choice labels from the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The numerical mile-per-hour values printed beside the choices. The source's
`pmh` spellings in choices A and C are interpreted as the evident `mph` typo.
-/
def answerChoiceMilesPerHour : AnswerChoice → ℤ
  | .A => 510
  | .B => 502
  | .C => 490
  | .D => 498

/-!
Blueprint target `thm:physics:phyx_mini_0828:target`.

The exact ground speed is `sqrt (500^2 + 50^2) = 50 * sqrt 101` miles per
hour. Mathlib's nearest-integer `round` gives 502, and hence uniquely selects
choice B among the displayed choices.
-/
theorem problem_phyx_mini_0828
    (setup : PlaneWindSetup)
    (hScenario : MatchesScenarioAndSuppliedFigure setup)
    (hData : StatedPlaneWindData setup)
    (hLaws : PlaneWindKinematicsLaws setup) :
    speedInMilesPerHour setup.planeGroundSpeed =
        50 * Real.sqrt 101 ∧
      round (speedInMilesPerHour setup.planeGroundSpeed) = 502 ∧
      ∀ choice,
        (round (speedInMilesPerHour setup.planeGroundSpeed) =
          answerChoiceMilesPerHour choice ↔ choice = .B) := by
  have hVelocityAdd :
      velocityInMilesPerHour setup.planeVelocityRelativeToGround =
        velocityInMilesPerHour setup.planeVelocityRelativeToAir +
          velocityInMilesPerHour setup.airVelocityRelativeToGround := by
    simpa only [velocityInMilesPerHour] using
      hLaws.relativeVelocityAddition LengthUnit.miles TimeUnit.hours
  have hPlaneVelocity :
      velocityInMilesPerHour setup.planeVelocityRelativeToAir = !₂[500, 0] := by
    rw [hData.planeVelocityDueEast, hData.planeAirspeedMilesPerHour]
  have hWindVelocity :
      velocityInMilesPerHour setup.airVelocityRelativeToGround = !₂[0, -50] := by
    rw [hData.windVelocityDueSouth, hData.windSpeedMilesPerHour]
  have hGroundVelocity :
      velocityInMilesPerHour setup.planeVelocityRelativeToGround = !₂[500, -50] := by
    rw [hVelocityAdd, hPlaneVelocity, hWindVelocity]
    ext i
    fin_cases i <;> norm_num
  have hGroundSpeed :
      speedInMilesPerHour setup.planeGroundSpeed =
        ‖velocityInMilesPerHour setup.planeVelocityRelativeToGround‖ := by
    simpa only [speedInMilesPerHour, velocityInMilesPerHour] using
      hLaws.groundSpeedIsVelocityMagnitude LengthUnit.miles TimeUnit.hours
  have hExact :
      speedInMilesPerHour setup.planeGroundSpeed = 50 * Real.sqrt 101 := by
    rw [hGroundSpeed, hGroundVelocity, EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs]
    norm_num [abs_of_nonneg]
    rw [show (252500 : ℝ) = 2500 * 101 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2500)]
    have hsqrt : Real.sqrt (2500 : ℝ) = 50 := by
      rw [show (2500 : ℝ) = 50 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [hsqrt]
  have hRound :
      round (speedInMilesPerHour setup.planeGroundSpeed) = 502 := by
    rw [hExact, round_eq_iff]
    constructor
    · norm_num
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 101),
        Real.sqrt_nonneg (101 : ℝ)]
    · norm_num
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 101),
        Real.sqrt_nonneg (101 : ℝ)]
  refine ⟨hExact, hRound, ?_⟩
  intro choice
  rw [hRound]
  cases choice <;> simp [answerChoiceMilesPerHour]

end PhyXMiniProblems.ProblemPhyXMini0828
