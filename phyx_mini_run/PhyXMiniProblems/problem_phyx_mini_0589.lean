import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0589

open Dimension

/-!
# Equal approach speeds seen by a relativistic cruiser

Cruisers `A` and `B` move rightward along a common horizontal axis toward a
space station.  In the station frame, cruiser `A` has speed `0.800 c`.
Cruiser `B` is ahead of `A` in the supplied image.  The question asks for the
station-frame speed of `B` for which the pilot of `B` sees `A`, approaching
from behind, and the station, approaching from ahead, at equal speeds.

Speed magnitudes and signed axial velocities are represented by
unit-independent Physlib quantities.  Real numbers occur only as named-unit
readouts, dimensionless fractions of the vacuum speed of light, qualitative
drawing coordinates, and displayed answer coefficients.

Assumption/target split:

* `MatchesPrimaryFigure` records the two colored cruisers, their ordering, the
  rightward `v_A` and `v_B` arrows, the station, and the horizontal `x` axis;
* `MatchesProblemData` records the observer frames, rightward physical motion,
  and only the supplied station-frame speed `v_A/c = 4/5`;
* `HasPhysicalSpeedParameters` and `RepresentsApproachDirections` record the
  physical subluminal domain and the two approach directions;
* `SatisfiesCollinearEinsteinVelocityTransformations` and
  `ApproachSpeedsAreVelocityMagnitudes` state the governing relativistic and
  operational laws;
* `PilotSeesEqualApproachSpeeds` states the requirement imposed by the
  question, without assigning cruiser `B` a numerical speed; and
* `v_B/c = 1/2` and the unique selection of answer C occur only in
  conclusions.
-/

/-! ## Dimensionful speeds, signed velocities, and scalar readouts -/

/-- A nonnegative physical speed magnitude, independent of a unit system. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed one-dimensional physical velocity of dimension length per time. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical speed magnitude in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed axial velocity in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Physlib's exact dimensionful vacuum light speed, read in named units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- A nonnegative speed expressed as a dimensionless fraction of vacuum `c`. -/
def speedFractionOfLight (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-- A signed axial velocity expressed as a dimensionless fraction of `c`. -/
def velocityFractionOfLight (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-! ## Frames, physical directions, and primary-figure labels -/

/-- The two inertial frames needed for the stated and pilot-observed speeds. -/
inductive InertialFrameLabel where
  | stationRestFrame
  | cruiserBRestFrame
  deriving DecidableEq, Repr

/-- The cruisers named in the prose and printed as `A` and `B` in the figure. -/
inductive CruiserLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Physical objects explicitly distinguished by the primary image. -/
inductive FigureObject where
  | cruiserA
  | cruiserB
  | station
  deriving DecidableEq, Fintype, Repr

/-- The two cruiser colors visible in the bitmap. -/
inductive CruiserColor where
  | red
  | blue
  deriving DecidableEq, Repr

/-- Direction along the left-to-right horizontal axis. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Mathematical labels printed over the two velocity arrows. -/
inductive VelocityArrowLabel where
  | vA
  | vB
  deriving DecidableEq, Repr

/-- The coordinate label printed at the right end of the horizontal axis. -/
inductive CoordinateAxisLabel where
  | x
  deriving DecidableEq, Repr

/-!
Typed qualitative evidence from `phyx_data/test_image/589.png`.  Horizontal
coordinates preserve visual ordering only and are not physical distances or a
quantitative position scale.
-/
structure CruiserStationFigure where
  objectHorizontalCoordinate : FigureObject → ℝ
  cruiserColor : CruiserLabel → CruiserColor
  cruiserDrawnAsRocket : CruiserLabel → Bool
  velocityArrowDirection : CruiserLabel → HorizontalDirection
  velocityArrowLabel : CruiserLabel → VelocityArrowLabel
  stationText : String
  horizontalAxisLabel : CoordinateAxisLabel
  stationHasTwoBlueBars : Bool
  stationHasDashedVerticalMarker : Bool
  hasQuantitativePositionScale : Bool

/-!
All physical observables in the scenario.  In particular,
`cruiserBSpeedRelativeToStation` is an independent dimensionful quantity: it
is not defined from an answer choice or from the solved value `1/2`.
-/
structure EqualApproachCruiserSetup where
  stationMeasurementFrame : InertialFrameLabel
  pilotObservationFrame : InertialFrameLabel
  cruiserAMotionInStationFrame : HorizontalDirection
  cruiserBMotionInStationFrame : HorizontalDirection
  cruiserASpeedRelativeToStation : SpeedQuantity
  cruiserBSpeedRelativeToStation : SpeedQuantity
  cruiserAVelocityRelativeToB : SignedVelocityQuantity
  stationVelocityRelativeToB : SignedVelocityQuantity
  cruiserAApproachSpeedSeenByB : SpeedQuantity
  stationApproachSpeedSeenByB : SpeedQuantity
  figure : CruiserStationFigure

/-! ## Figure evidence and stated problem data -/

/-!
The primary bitmap places the red cruiser `A` left of the blue cruiser `B`,
and places both left of the station.  Both labeled arrows point right.  The
axis and station markings are retained without assigning physical distances
to the drawing.
-/
structure MatchesPrimaryFigure
    (setup : EqualApproachCruiserSetup) : Prop where
  cruiserALeftOfCruiserB :
    setup.figure.objectHorizontalCoordinate .cruiserA <
      setup.figure.objectHorizontalCoordinate .cruiserB
  cruiserBLeftOfStation :
    setup.figure.objectHorizontalCoordinate .cruiserB <
      setup.figure.objectHorizontalCoordinate .station
  cruiserAIsRed : setup.figure.cruiserColor .A = .red
  cruiserBIsBlue : setup.figure.cruiserColor .B = .blue
  cruiserADrawnAsRocket : setup.figure.cruiserDrawnAsRocket .A = true
  cruiserBDrawnAsRocket : setup.figure.cruiserDrawnAsRocket .B = true
  cruiserAArrowPointsRight :
    setup.figure.velocityArrowDirection .A = .rightward
  cruiserBArrowPointsRight :
    setup.figure.velocityArrowDirection .B = .rightward
  cruiserAArrowLabel : setup.figure.velocityArrowLabel .A = .vA
  cruiserBArrowLabel : setup.figure.velocityArrowLabel .B = .vB
  stationLabel : setup.figure.stationText = "Station"
  axisLabel : setup.figure.horizontalAxisLabel = .x
  twoStationBarsShown : setup.figure.stationHasTwoBlueBars = true
  dashedStationMarkerShown :
    setup.figure.stationHasDashedVerticalMarker = true
  noQuantitativePositionScale :
    setup.figure.hasQuantitativePositionScale = false

/-!
Frame assignments, physical directions, and the sole numerical input supplied
by the prose.  No station-frame speed is supplied for cruiser `B`.
-/
structure MatchesProblemData
    (setup : EqualApproachCruiserSetup) : Prop where
  givenSpeedMeasuredInStationFrame :
    setup.stationMeasurementFrame = .stationRestFrame
  pilotMeasurementsUseCruiserBFrame :
    setup.pilotObservationFrame = .cruiserBRestFrame
  cruiserAMovesRightTowardStation :
    setup.cruiserAMotionInStationFrame = .rightward
  cruiserBMovesRightTowardStation :
    setup.cruiserBMotionInStationFrame = .rightward
  cruiserAStationSpeedFraction :
    speedFractionOfLight setup.cruiserASpeedRelativeToStation = 4 / 5

/-!
Positivity and subluminality of the physical speeds.  These domain conditions
exclude the superluminal algebraic root but do not determine cruiser `B`'s
speed within the physical interval.
-/
structure HasPhysicalSpeedParameters
    (setup : EqualApproachCruiserSetup) : Prop where
  lightSpeedReadoutPositive :
    0 < vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds
  cruiserASpeedPositive :
    0 < speedFractionOfLight setup.cruiserASpeedRelativeToStation
  cruiserASpeedSubluminal :
    speedFractionOfLight setup.cruiserASpeedRelativeToStation < 1
  cruiserBSpeedPositive :
    0 < speedFractionOfLight setup.cruiserBSpeedRelativeToStation
  cruiserBSpeedSubluminal :
    speedFractionOfLight setup.cruiserBSpeedRelativeToStation < 1
  cruiserAApproachSpeedPositive :
    0 < speedFractionOfLight setup.cruiserAApproachSpeedSeenByB
  stationApproachSpeedPositive :
    0 < speedFractionOfLight setup.stationApproachSpeedSeenByB

/-!
The signs that give the word "approach" its directional meaning in `B`'s
frame: `A`, behind `B`, moves in the positive direction toward `B`, while the
station, ahead of `B`, moves in the negative direction toward `B`.
-/
structure RepresentsApproachDirections
    (setup : EqualApproachCruiserSetup) : Prop where
  cruiserAApproachesFromBehind :
    0 < velocityFractionOfLight setup.cruiserAVelocityRelativeToB
  stationApproachesFromAhead :
    velocityFractionOfLight setup.stationVelocityRelativeToB < 0

/-! ## Governing special-relativistic and operational laws -/

/-!
The collinear Einstein velocity transformation, written in dimensionless
fractions of `c`.  Since both cruisers move right in the station frame,

`beta_A|B = (beta_A - beta_B) / (1 - beta_A * beta_B)`.

The station has zero station-frame velocity, so its velocity in `B`'s frame
is `-beta_B`.  These are symbolic laws involving the still-unknown speed of
`B`; neither equation contains its solved numerical value.
-/
structure SatisfiesCollinearEinsteinVelocityTransformations
    (setup : EqualApproachCruiserSetup) : Prop where
  cruiserAVelocityInBFrame :
    velocityFractionOfLight setup.cruiserAVelocityRelativeToB =
      (speedFractionOfLight setup.cruiserASpeedRelativeToStation -
          speedFractionOfLight setup.cruiserBSpeedRelativeToStation) /
        (1 -
          speedFractionOfLight setup.cruiserASpeedRelativeToStation *
            speedFractionOfLight setup.cruiserBSpeedRelativeToStation)
  stationVelocityInBFrame :
    velocityFractionOfLight setup.stationVelocityRelativeToB =
      -speedFractionOfLight setup.cruiserBSpeedRelativeToStation

/-!
Operational interpretation of each pilot-reported nonnegative approach speed
as the magnitude of the corresponding signed B-frame velocity.
-/
structure ApproachSpeedsAreVelocityMagnitudes
    (setup : EqualApproachCruiserSetup) : Prop where
  cruiserAApproachSpeedMagnitude :
    speedFractionOfLight setup.cruiserAApproachSpeedSeenByB =
      |velocityFractionOfLight setup.cruiserAVelocityRelativeToB|
  stationApproachSpeedMagnitude :
    speedFractionOfLight setup.stationApproachSpeedSeenByB =
      |velocityFractionOfLight setup.stationVelocityRelativeToB|

/-!
The requirement posed by the question: the two independent physical approach
speed observables measured by the pilot of `B` are equal.  This premise does
not give either speed a numerical value and does not assign an answer choice.
-/
def PilotSeesEqualApproachSpeeds
    (setup : EqualApproachCruiserSetup) : Prop :=
  setup.cruiserAApproachSpeedSeenByB =
    setup.stationApproachSpeedSeenByB

/-! ## Displayed answers and current target -/

/-- Labels of the four choices printed with the source question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Candidate station-frame speeds of cruiser `B`, as fractions of `c`. -/
def displayedCruiserBSpeedFraction : AnswerChoice → ℝ
  | .A => 3 / 5
  | .B => 2 / 5
  | .C => 1 / 2
  | .D => 7 / 10

/-- The answer label recorded by the dataset; it is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice exactly matches the modeled station-frame speed of cruiser `B`. -/
def MatchesAnswerChoice
    (setup : EqualApproachCruiserSetup) (choice : AnswerChoice) : Prop :=
  speedFractionOfLight setup.cruiserBSpeedRelativeToStation =
    displayedCruiserBSpeedFraction choice

/-- The selected choice is the unique displayed exact speed fraction. -/
def IsUniqueMatchingAnswerChoice
    (setup : EqualApproachCruiserSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Substituting `beta_A = 4/5` into the Einstein transformation and equating the
two pilot-observed approach speeds gives the physical solution
`beta_B = 1/2`.  The second algebraic root is superluminal and is excluded by
`HasPhysicalSpeedParameters`.
-/
lemma required_cruiser_B_speed_fraction
    (setup : EqualApproachCruiserSetup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalSpeedParameters setup)
    (hApproach : RepresentsApproachDirections setup)
    (hRelativity : SatisfiesCollinearEinsteinVelocityTransformations setup)
    (hMagnitude : ApproachSpeedsAreVelocityMagnitudes setup)
    (hEqual : PilotSeesEqualApproachSpeeds setup) :
    speedFractionOfLight setup.cruiserBSpeedRelativeToStation = 1 / 2 := by
  have hbLt :
      speedFractionOfLight setup.cruiserBSpeedRelativeToStation < 1 :=
    hPhysical.cruiserBSpeedSubluminal
  have hEqualSigned :
      velocityFractionOfLight setup.cruiserAVelocityRelativeToB =
        -velocityFractionOfLight setup.stationVelocityRelativeToB := by
    unfold PilotSeesEqualApproachSpeeds at hEqual
    have h := congrArg speedFractionOfLight hEqual
    rw [hMagnitude.cruiserAApproachSpeedMagnitude,
      hMagnitude.stationApproachSpeedMagnitude,
      abs_of_pos hApproach.cruiserAApproachesFromBehind,
      abs_of_neg hApproach.stationApproachesFromAhead] at h
    exact h
  rw [hRelativity.cruiserAVelocityInBFrame,
    hRelativity.stationVelocityInBFrame,
    hData.cruiserAStationSpeedFraction] at hEqualSigned
  simp only [neg_neg] at hEqualSigned
  have hNormalizedDenominator :
      5 - 4 * speedFractionOfLight setup.cruiserBSpeedRelativeToStation ≠ 0 := by
    nlinarith
  field_simp [hNormalizedDenominator] at hEqualSigned
  have hFactor :
      (2 * speedFractionOfLight setup.cruiserBSpeedRelativeToStation - 1) *
          (speedFractionOfLight setup.cruiserBSpeedRelativeToStation - 2) = 0 := by
    nlinarith [hEqualSigned]
  rcases mul_eq_zero.mp hFactor with hHalf | hTwo
  · nlinarith
  · nlinarith

/-!
Thus cruiser `B` must move at `0.5 c` relative to the station, uniquely
selecting choice C.

This formalizes `thm:physics:phyx_mini_0589:target`.
-/
theorem problem_phyx_mini_0589
    (setup : EqualApproachCruiserSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalSpeedParameters setup)
    (hApproach : RepresentsApproachDirections setup)
    (hRelativity : SatisfiesCollinearEinsteinVelocityTransformations setup)
    (hMagnitude : ApproachSpeedsAreVelocityMagnitudes setup)
    (hEqual : PilotSeesEqualApproachSpeeds setup) :
    speedFractionOfLight setup.cruiserBSpeedRelativeToStation = 1 / 2 ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hSpeed := required_cruiser_B_speed_fraction setup hData hPhysical
    hApproach hRelativity hMagnitude hEqual
  refine ⟨hSpeed, ?_⟩
  unfold IsUniqueMatchingAnswerChoice
  constructor
  · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedCruiserBSpeedFraction] using hSpeed
  · intro other hOther
    unfold MatchesAnswerChoice at hOther
    rw [hSpeed] at hOther
    cases other with
    | A => norm_num [displayedCruiserBSpeedFraction] at hOther
    | B => norm_num [displayedCruiserBSpeedFraction] at hOther
    | C => rfl
    | D => norm_num [displayedCruiserBSpeedFraction] at hOther

end PhyXMiniProblems.ProblemPhyXMini0589
