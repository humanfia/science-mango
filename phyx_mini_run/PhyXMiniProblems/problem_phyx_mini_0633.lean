import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Apply
import Physlib.SpaceAndTime.SpaceTime.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0633

open Dimension

/-!
# Relativity of the railroad-car firecracker explosions

Ryan's ground frame is `S`, and Peggy's railroad-car frame is `S'`.  The
primary figure places the left and right explosion events at `-300 m` and
`300 m`, respectively, at Ryan-frame time zero.  Peggy passes Ryan at the
common frame origin, also at time zero, while the car moves toward positive
`x` with speed `0.8 c`.

The spacetime coordinates are genuine `SpaceTime 1` values, and the relative
speed is a unit-independent Physlib `DimSpeed`.  Real numbers below occur only
as coordinate readouts in named units, dimensionless speed ratios, printed
figure values, and displayed multiple-choice values.
-/

/-! ## Physical quantities and coordinate readouts -/

/-- Read a nonnegative physical speed in coherent SI units, metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- The exact vacuum speed of light, read in metres per microsecond. -/
def vacuumSpeedOfLightInMetersPerMicrosecond : ℝ :=
  vacuumSpeedOfLightInMetersPerSecond / 10 ^ 6

/-- The two inertial frames printed in the supplied image. -/
inductive InertialFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Fintype, Repr

/-- The two observers associated with the frames. -/
inductive ObserverLabel where
  | Ryan
  | Peggy
  deriving DecidableEq, Fintype, Repr

/-- The left and right firecrackers, explosion events, and light flashes. -/
inductive ExplosionSide where
  | L
  | R
  deriving DecidableEq, Fintype, Repr

/-- Events needed to state the scenario and its light-propagation evidence. -/
inductive EventLabel where
  | passing
  | explosion (side : ExplosionSide)
  | flashArrival (side : ExplosionSide)
  deriving DecidableEq, Repr

/-- Qualitative location of each observer in the scenario. -/
inductive ObserverLocation where
  | ground
  | railroadCarCenter
  deriving DecidableEq, Fintype, Repr

/-- Horizontal direction relative to the orientation of the image. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Fintype, Repr

/-- Named visual elements in image `phyx_data/test_image/633.png`. -/
inductive FigureFeature where
  | Ryan
  | Peggy
  | groundFrameS
  | carFrameSPrime
  | railroadCar
  | tracks
  | leftExplosion
  | rightExplosion
  | horizontalXAxis
  | velocityArrow
  | passingAnnotation
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative and numerical content of the primary image.  The figure's
event times are printed in seconds, while the working coordinates below use
microseconds; their common displayed value is zero.
-/
structure RailroadCarRelativityFigure where
  shows : FigureFeature → Bool
  observerFrame : ObserverLabel → InertialFrameLabel
  observerLocation : ObserverLabel → ObserverLocation
  velocityArrowDirection : HorizontalDirection
  horizontalAxisLengthUnit : LengthUnit
  printedExplosionPositionMeters : ExplosionSide → ℝ
  printedExplosionTimeSeconds : ExplosionSide → ℝ
  printedPassingTimeSeconds : InertialFrameLabel → ℝ

/-!
Independent physical quantities and spacetime coordinates for the problem.
No Peggy-frame explosion time is defined from an answer choice.
-/
structure RailroadCarRelativitySetup where
  figure : RailroadCarRelativityFigure
  coordinateLengthUnit : LengthUnit
  coordinateTimeUnit : TimeUnit
  coordinateSpeedOfLight : SpeedOfLight
  relativeSpeed : DimSpeed
  motionDirection : HorizontalDirection
  frameCoordinate : InertialFrameLabel → EventLabel → SpaceTime 1
  burnMarkPositionReadout : ExplosionSide → ℝ

/-- The dimensionless speed parameter `β = v / c`. -/
def speedFractionOfLight (setup : RailroadCarRelativitySetup) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- Time-coordinate readout in the time unit selected by the setup. -/
def timeCoordinateReadout
    (setup : RailroadCarRelativitySetup)
    (frame : InertialFrameLabel) (event : EventLabel) : ℝ :=
  (SpaceTime.time setup.coordinateSpeedOfLight
    (setup.frameCoordinate frame event)).val

/-- Axial position-coordinate readout in the length unit selected by the setup. -/
def xCoordinateReadout
    (setup : RailroadCarRelativitySetup)
    (frame : InertialFrameLabel) (event : EventLabel) : ℝ :=
  (SpaceTime.space (setup.frameCoordinate frame event)) 0

/-- Peggy's microsecond time readout for one of the two explosion events. -/
def peggyExplosionTimeMicroseconds
    (setup : RailroadCarRelativitySetup) (side : ExplosionSide) : ℝ :=
  timeCoordinateReadout setup .SPrime (.explosion side)

/-! ## Scenario, figure evidence, and supplied numerical readouts -/

/-- The setup uses metre and microsecond coordinates with the calibrated `c`. -/
structure UsesMeterMicrosecondCoordinates
    (setup : RailroadCarRelativitySetup) : Prop where
  lengthUnitIsMeters : setup.coordinateLengthUnit = LengthUnit.meters
  timeUnitIsMicroseconds : setup.coordinateTimeUnit = TimeUnit.microseconds
  coordinateLightSpeedCalibration :
    setup.coordinateSpeedOfLight.val =
      vacuumSpeedOfLightInMetersPerMicrosecond

/-!
Primary-image evidence: Ryan is in ground frame `S`, Peggy is at the center
of the railroad car in frame `S'`, the car moves right, the two explosions
are at `(x_L,t_L)=(-300 m,0 s)` and `(x_R,t_R)=(300 m,0 s)`, and the passing
event is the common origin `t=t'=0`.
-/
structure MatchesSuppliedRailroadCarFigure
    (setup : RailroadCarRelativitySetup) : Prop where
  everyNamedFeatureShown : ∀ feature, setup.figure.shows feature = true
  RyanUsesGroundFrame : setup.figure.observerFrame .Ryan = .S
  PeggyUsesCarFrame : setup.figure.observerFrame .Peggy = .SPrime
  RyanStandsOnGround : setup.figure.observerLocation .Ryan = .ground
  PeggyStandsAtCarCenter :
    setup.figure.observerLocation .Peggy = .railroadCarCenter
  velocityArrowPointsRight :
    setup.figure.velocityArrowDirection = .rightward
  motionPointsRight : setup.motionDirection = .rightward
  figureAxisUsesMeters :
    setup.figure.horizontalAxisLengthUnit = LengthUnit.meters
  leftPositionAnnotation :
    setup.figure.printedExplosionPositionMeters .L = -300
  rightPositionAnnotation :
    setup.figure.printedExplosionPositionMeters .R = 300
  leftRyanTimeAnnotation :
    setup.figure.printedExplosionTimeSeconds .L = 0
  rightRyanTimeAnnotation :
    setup.figure.printedExplosionTimeSeconds .R = 0
  passingRyanTimeAnnotation :
    setup.figure.printedPassingTimeSeconds .S = 0
  passingPeggyTimeAnnotation :
    setup.figure.printedPassingTimeSeconds .SPrime = 0
  RyanExplosionPositionAgrees : ∀ side,
    xCoordinateReadout setup .S (.explosion side) =
      setup.figure.printedExplosionPositionMeters side
  RyanExplosionTimeAgrees : ∀ side,
    timeCoordinateReadout setup .S (.explosion side) =
      10 ^ 6 * setup.figure.printedExplosionTimeSeconds side
  passingAtRyanSpatialOrigin :
    xCoordinateReadout setup .S .passing = 0
  passingAtPeggySpatialOrigin :
    xCoordinateReadout setup .SPrime .passing = 0
  passingAtRyanTimeOrigin :
    timeCoordinateReadout setup .S .passing = 0
  passingAtPeggyTimeOrigin :
    timeCoordinateReadout setup .SPrime .passing = 0

/-- Agreement with a time printed to one decimal place in microseconds. -/
def AgreesWithOneDecimalMicrosecondReadout
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| ≤ 1 / 20

/-!
Prose data not supplied by the coordinate labels alone: `v=0.8c`, both
flashes reach Ryan together about `1.0 μs` after passing, and the two burn
marks lie `300 m` on opposite sides of Ryan's initial position.
-/
structure MatchesProblemReadouts
    (setup : RailroadCarRelativitySetup) : Prop where
  speedIsEightTenthsOfLight : speedFractionOfLight setup = 4 / 5
  simultaneousFlashArrivalAtRyan :
    timeCoordinateReadout setup .S (.flashArrival .L) =
      timeCoordinateReadout setup .S (.flashArrival .R)
  leftFlashArrivesAtRyan :
    xCoordinateReadout setup .S (.flashArrival .L) =
      xCoordinateReadout setup .S .passing
  rightFlashArrivesAtRyan :
    xCoordinateReadout setup .S (.flashArrival .R) =
      xCoordinateReadout setup .S .passing
  arrivalDelayReadout : ∀ side,
    AgreesWithOneDecimalMicrosecondReadout
      (timeCoordinateReadout setup .S (.flashArrival side) -
        timeCoordinateReadout setup .S .passing)
      1
  leftBurnMarkPosition : setup.burnMarkPositionReadout .L = -300
  rightBurnMarkPosition : setup.burnMarkPositionReadout .R = 300
  explosionOccursAtBurnMark : ∀ side,
    xCoordinateReadout setup .S (.explosion side) =
      setup.burnMarkPositionReadout side

/-- Positivity and subluminality conditions selecting the physical branch. -/
structure HasPhysicalRelativisticParameters
    (setup : RailroadCarRelativitySetup) : Prop where
  coordinateLightSpeedPositive : 0 < setup.coordinateSpeedOfLight.val
  relativeSpeedPositive : 0 < speedFractionOfLight setup
  relativeSpeedSubluminal : |speedFractionOfLight setup| < 1
  flashArrivesAfterExplosion : ∀ side,
    timeCoordinateReadout setup .S (.explosion side) <
      timeCoordinateReadout setup .S (.flashArrival side)

/-! ## Governing physical laws -/

/-!
Vacuum light propagation between each explosion and its arrival at Ryan.  In
the selected metre/microsecond coordinates, a lightlike interval obeys
`|Δx| = c Δt`.  This is a generic governing law and does not contain either
Peggy-frame answer time.
-/
structure SatisfiesVacuumLightPropagation
    (setup : RailroadCarRelativitySetup) : Prop where
  lightlikeTravel : ∀ side,
    |xCoordinateReadout setup .S (.flashArrival side) -
        xCoordinateReadout setup .S (.explosion side)| =
      setup.coordinateSpeedOfLight.val *
        (timeCoordinateReadout setup .S (.flashArrival side) -
          timeCoordinateReadout setup .S (.explosion side))

/-!
The passive Lorentz boost from Ryan's ground coordinates to Peggy's car
coordinates.  Physlib's boost acts on the complete `SpaceTime 1` event, with
the standard time component `γ(β) (ct - βx)`.  The law is quantified over all
events and contains no solved explosion-time value or answer-choice label.
-/
structure SatisfiesRyanToPeggyLorentzBoost
    (setup : RailroadCarRelativitySetup) : Prop where
  betaSubluminal : |speedFractionOfLight setup| < 1
  coordinateTransformation : ∀ event,
    setup.frameCoordinate .SPrime event =
      LorentzGroup.boost (0 : Fin 1) (speedFractionOfLight setup)
          betaSubluminal •
        setup.frameCoordinate .S event

/-! ## Derived explosion times and displayed-answer semantics -/

/-- Magnitude predicted from `β=0.8`, `|x|=300 m`, and exact vacuum `c`. -/
def predictedPeggyExplosionTimeMagnitudeMicroseconds : ℝ :=
  LorentzGroup.γ (4 / 5) *
    ((4 / 5) * 300 / vacuumSpeedOfLightInMetersPerMicrosecond)

/-!
The two Ryan-simultaneous explosions are not simultaneous for Peggy: the
left event is later and the right event is earlier by equal magnitudes.
This is a derived conclusion, not a governing-law field.
-/
lemma peggy_explosion_times_exact
    (setup : RailroadCarRelativitySetup)
    (_units : UsesMeterMicrosecondCoordinates setup)
    (_figure : MatchesSuppliedRailroadCarFigure setup)
    (_data : MatchesProblemReadouts setup)
    (_lorentz : SatisfiesRyanToPeggyLorentzBoost setup) :
    peggyExplosionTimeMicroseconds setup .L =
        predictedPeggyExplosionTimeMagnitudeMicroseconds ∧
      peggyExplosionTimeMicroseconds setup .R =
        -predictedPeggyExplosionTimeMagnitudeMicroseconds := by
  have hβ : speedFractionOfLight setup = (4 / 5 : ℝ) :=
    _data.speedIsEightTenthsOfLight
  have hc : setup.coordinateSpeedOfLight.val =
      vacuumSpeedOfLightInMetersPerMicrosecond :=
    _units.coordinateLightSpeedCalibration
  have hLx : xCoordinateReadout setup .S (.explosion .L) = -300 := by
    calc
      xCoordinateReadout setup .S (.explosion .L) =
          setup.figure.printedExplosionPositionMeters .L :=
        _figure.RyanExplosionPositionAgrees .L
      _ = -300 := _figure.leftPositionAnnotation
  have hRx : xCoordinateReadout setup .S (.explosion .R) = 300 := by
    calc
      xCoordinateReadout setup .S (.explosion .R) =
          setup.figure.printedExplosionPositionMeters .R :=
        _figure.RyanExplosionPositionAgrees .R
      _ = 300 := _figure.rightPositionAnnotation
  have hLt : timeCoordinateReadout setup .S (.explosion .L) = 0 := by
    rw [_figure.RyanExplosionTimeAgrees, _figure.leftRyanTimeAnnotation]
    norm_num
  have hRt : timeCoordinateReadout setup .S (.explosion .R) = 0 := by
    rw [_figure.RyanExplosionTimeAgrees, _figure.rightRyanTimeAnnotation]
    norm_num
  have hLtime :
      setup.frameCoordinate .S (.explosion .L) (Sum.inl 0) = 0 := by
    unfold timeCoordinateReadout at hLt
    rw [SpaceTime.time_val_toCoord_symm] at hLt
    field_simp at hLt
    simpa using hLt
  have hRtime :
      setup.frameCoordinate .S (.explosion .R) (Sum.inl 0) = 0 := by
    unfold timeCoordinateReadout at hRt
    rw [SpaceTime.time_val_toCoord_symm] at hRt
    field_simp at hRt
    simpa using hRt
  have hLspace :
      setup.frameCoordinate .S (.explosion .L) (Sum.inr (0 : Fin 1)) = -300 := by
    unfold xCoordinateReadout at hLx
    rw [SpaceTime.space_toCoord_symm] at hLx
    exact hLx
  have hRspace :
      setup.frameCoordinate .S (.explosion .R) (Sum.inr (0 : Fin 1)) = 300 := by
    unfold xCoordinateReadout at hRx
    rw [SpaceTime.space_toCoord_symm] at hRx
    exact hRx
  constructor
  · unfold peggyExplosionTimeMicroseconds timeCoordinateReadout
    rw [_lorentz.coordinateTransformation, SpaceTime.time_val_toCoord_symm,
      Lorentz.Vector.boost_time_eq, hLtime, hLspace, hβ, hc]
    unfold predictedPeggyExplosionTimeMagnitudeMicroseconds
    ring
  · unfold peggyExplosionTimeMicroseconds timeCoordinateReadout
    rw [_lorentz.coordinateTransformation, SpaceTime.time_val_toCoord_symm,
      Lorentz.Vector.boost_time_eq, hRtime, hRspace, hβ, hc]
    unfold predictedPeggyExplosionTimeMagnitudeMicroseconds
    ring

/-- Labels of the four microsecond-valued choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The negative microsecond time printed beside each answer label. -/
def displayedPeggyTimeMicroseconds : AnswerChoice → ℝ
  | .A => -113 / 100
  | .B => -133 / 100
  | .C => -153 / 100
  | .D => -173 / 100

/-- The answer label recorded by the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a time displayed to the nearest hundredth of a microsecond. -/
def RoundsToNearestHundredthMicrosecond
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-!
The negative choices compare to the right-hand explosion, the explosion that
occurs before the passing event in Peggy's frame.
-/
def MatchesAnswerChoice
    (setup : RailroadCarRelativitySetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthMicrosecond
    (peggyExplosionTimeMicroseconds setup .R)
    (displayedPeggyTimeMicroseconds choice)

/-- The selected label is the unique displayed choice matching Peggy's time. -/
def IsUniqueMatchingAnswerChoice
    (setup : RailroadCarRelativitySetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
According to Peggy, event `L` occurs about `+1.33 μs` and event `R` occurs
about `-1.33 μs` relative to the passing event.  The earlier/right event thus
uniquely matches answer B.

This formalizes `thm:physics:phyx_mini_0633:target`.
-/
theorem problem_phyx_mini_0633
    (setup : RailroadCarRelativitySetup)
    (h_units : UsesMeterMicrosecondCoordinates setup)
    (h_figure : MatchesSuppliedRailroadCarFigure setup)
    (h_data : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalRelativisticParameters setup)
    (h_light : SatisfiesVacuumLightPropagation setup)
    (h_lorentz : SatisfiesRyanToPeggyLorentzBoost setup) :
    peggyExplosionTimeMicroseconds setup .L =
        predictedPeggyExplosionTimeMagnitudeMicroseconds ∧
      peggyExplosionTimeMicroseconds setup .R =
        -predictedPeggyExplosionTimeMagnitudeMicroseconds ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  rcases peggy_explosion_times_exact setup h_units h_figure h_data h_lorentz with
    ⟨hL, hR⟩
  refine ⟨hL, hR, ?_⟩
  unfold IsUniqueMatchingAnswerChoice
  constructor
  · unfold MatchesAnswerChoice RoundsToNearestHundredthMicrosecond
    rw [hR]
    norm_num [recordedDatasetAnswer, displayedPeggyTimeMicroseconds,
      predictedPeggyExplosionTimeMagnitudeMicroseconds,
      vacuumSpeedOfLightInMetersPerMicrosecond,
      vacuumSpeedOfLightInMetersPerSecond, DimSpeed.speedOfLight_in_SI,
      LorentzGroup.γ, Real.sq_sqrt, abs_lt]
  · intro other hOther
    unfold MatchesAnswerChoice RoundsToNearestHundredthMicrosecond at hOther
    rw [hR] at hOther
    cases other with
    | A =>
        norm_num [displayedPeggyTimeMicroseconds,
          predictedPeggyExplosionTimeMagnitudeMicroseconds,
          vacuumSpeedOfLightInMetersPerMicrosecond,
          vacuumSpeedOfLightInMetersPerSecond, DimSpeed.speedOfLight_in_SI,
          LorentzGroup.γ, Real.sq_sqrt, abs_lt] at hOther
    | B => rfl
    | C =>
        norm_num [displayedPeggyTimeMicroseconds,
          predictedPeggyExplosionTimeMagnitudeMicroseconds,
          vacuumSpeedOfLightInMetersPerMicrosecond,
          vacuumSpeedOfLightInMetersPerSecond, DimSpeed.speedOfLight_in_SI,
          LorentzGroup.γ, Real.sq_sqrt, abs_lt] at hOther
    | D =>
        norm_num [displayedPeggyTimeMicroseconds,
          predictedPeggyExplosionTimeMagnitudeMicroseconds,
          vacuumSpeedOfLightInMetersPerMicrosecond,
          vacuumSpeedOfLightInMetersPerSecond, DimSpeed.speedOfLight_in_SI,
          LorentzGroup.γ, Real.sq_sqrt, abs_lt] at hOther

end PhyXMiniProblems.ProblemPhyXMini0633
