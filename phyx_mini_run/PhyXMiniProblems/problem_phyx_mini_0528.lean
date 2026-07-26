import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Relativity.Special.ProperTime
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0528

open Dimension

/-!
# Round-trip light time for a spacecraft approaching a mirror

In the inertial frame `S`, a spacecraft coasts toward a stationary mirror at
`0.650 c`.  At emission the mirror is `5.66 × 10^10 m` from the spacecraft.
A light pulse travels to the mirror, reflects, and returns to the spacecraft.
The requested duration is the proper time recorded in the spacecraft frame.

Physical lengths, durations, and speeds are represented by unit-independent
Physlib quantities.  The three emission/reflection/reception events use
Physlib's one-dimensional Minkowski spacetime.  Their temporal coordinate is
interpreted as `ct` in metres and their spatial coordinate as `x` in metres.
Real numbers below are therefore named unit readouts, spacetime coordinates,
dimensionless speed ratios, or the values printed in the answer list.

Assumption/target split:

* `MatchesCoastingSpacecraftMirrorScenario` records object and frame roles;
* `MatchesSuppliedSpacecraftMirrorFigure` records the primary-image labels,
  ordering, arrows, and colors;
* `MatchesProblemReadouts` records `d = 5.66 × 10^10 m` and `v/c = 0.650`;
* `SatisfiesReferenceFrameLightPropagation` states the inertial spacecraft and
  stationary-mirror worldlines, both null pulse legs, reflection, and duration
  accounting in `S`;
* `SatisfiesSpecialRelativisticProperTime` states the generic Minkowski
  proper-time and Lorentz time-dilation laws; and
* the exact duration formulas and agreement with `174 s` occur only as
  conclusions below.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical speed, used for the spacecraft speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a nonnegative physical speed in selected coherent units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read Physlib's real-valued vacuum speed of light in coherent units. -/
def vacuumLightSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metre readout of the initial spacecraft--mirror separation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout of a frame-measured physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Metres-per-second readout of the spacecraft's speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Physlib's exact vacuum light speed, read in metres per second. -/
def vacuumLightSpeedInMetersPerSecond : ℝ :=
  vacuumLightSpeedReadout LengthUnit.meters TimeUnit.seconds

/-! ## Frames, objects, events, and primary-figure vocabulary -/

/-- The mirror rest frame `S` and the coasting spacecraft rest frame. -/
inductive InertialFrameLabel where
  | S
  | spacecraftRest
  deriving DecidableEq, Repr

/-- The three physical objects whose worldlines enter the experiment. -/
inductive PhysicalObject where
  | spacecraft
  | mirror
  | lightPulse
  deriving DecidableEq, Fintype, Repr

/-- The three distinguished events of the round trip. -/
inductive EventLabel where
  | emission
  | reflection
  | reception
  deriving DecidableEq, Fintype, Repr

/-- The two directed legs of the light pulse. -/
inductive PulseLeg where
  | outbound
  | reflectedReturn
  deriving DecidableEq, Fintype, Repr

/-- Direction along the horizontal spacecraft--mirror axis. -/
inductive AxialDirection where
  | towardMirror
  | awayFromMirror
  deriving DecidableEq, Repr

/-- The spacecraft's stated free inertial motion. -/
inductive SpacecraftMotionModel where
  | inertialCoasting
  deriving DecidableEq, Repr

/-- The idealized reflecting object fixed in frame `S`. -/
inductive MirrorModel where
  | stationaryPlaneIdealReflector
  deriving DecidableEq, Repr

/-- The electromagnetic signal used by the experiment. -/
inductive SignalKind where
  | lightPulse
  deriving DecidableEq, Repr

/-- Coordinate lines visible in the supplied image. -/
inductive FigureAxis where
  | horizontalBaseline
  | verticalFrameAxis
  deriving DecidableEq, Fintype, Repr

/-- Semantic transcription of the literal labels visible in the image. -/
inductive FigureLabel where
  | frameS
  | originO
  | mirror
  | distanceD
  | velocityV
  deriving DecidableEq, Fintype, Repr

/-- The velocity, pulse, and separation arrows drawn in the image. -/
inductive FigureArrow where
  | spacecraftVelocity
  | outgoingPulse
  | separationDistance
  deriving DecidableEq, Fintype, Repr

/-- Whether a displayed arrow has one or two arrowheads. -/
inductive ArrowStyle where
  | singleHeaded
  | doubleHeaded
  deriving DecidableEq, Repr

/-- Coarse colors needed to transcribe the salient primary-image evidence. -/
inductive FigureColor where
  | red
  | blue
  | gray
  deriving DecidableEq, Repr

/-!
Qualitative content of the primary raster.  It contains no numerical time or
answer-choice value.
-/
structure SpacecraftMirrorFigure where
  objectShown : PhysicalObject → Bool
  axisShown : FigureAxis → Bool
  labelShown : FigureLabel → Bool
  axisLabel : FigureAxis → Option FigureLabel
  axisOriginLabel : FigureLabel
  objectLabel : PhysicalObject → Option FigureLabel
  spacecraftLeftOfMirror : Bool
  mirrorDrawnVertically : Bool
  distanceArrowLeftEndpoint : PhysicalObject
  distanceArrowRightEndpoint : PhysicalObject
  arrowDirection : FigureArrow → Option AxialDirection
  arrowStyle : FigureArrow → ArrowStyle
  arrowLabel : FigureArrow → Option FigureLabel
  objectColor : PhysicalObject → FigureColor
  arrowColor : FigureArrow → FigureColor

/-!
Independent physical quantities, coordinate worldlines, and events of the
experiment.  The two duration fields are observables in different inertial
frames and are not defined from a displayed answer or from the target formula.
-/
structure SpacecraftMirrorRoundTripSetup where
  figure : SpacecraftMirrorFigure
  referenceFrame : InertialFrameLabel
  spacecraftFrame : InertialFrameLabel
  spacecraftMotionModel : SpacecraftMotionModel
  mirrorModel : MirrorModel
  signalKind : SignalKind
  spacecraftDirectionInS : AxialDirection
  pulseDirection : PulseLeg → AxialDirection
  spacecraftSpeedRelativeToS : SpeedQuantity
  initialSeparationInS : LengthQuantity
  referenceFrameRoundTripDuration : DurationQuantity
  spacecraftMeasuredRoundTripDuration : DurationQuantity
  event : EventLabel → SpaceTime 1
  objectPositionInSMeters : PhysicalObject → ℝ → ℝ

/-! ## Spacetime-coordinate and relativity helpers -/

/-- The `ct` coordinate of an event, interpreted as a real number of metres. -/
def eventCtCoordinateMeters
    (setup : SpacecraftMirrorRoundTripSetup) (event : EventLabel) : ℝ :=
  SpaceTime.coord 0 (setup.event event)

/-- The horizontal `x` coordinate of an event, in metres in frame `S`. -/
def eventPositionInSMeters
    (setup : SpacecraftMirrorRoundTripSetup) (event : EventLabel) : ℝ :=
  SpaceTime.coord 1 (setup.event event)

/-- Frame-`S` coordinate time of an event, obtained from `ct / c`. -/
def eventTimeInSSeconds
    (setup : SpacecraftMirrorRoundTripSetup) (event : EventLabel) : ℝ :=
  eventCtCoordinateMeters setup event /
    vacuumLightSpeedInMetersPerSecond

/-- Dimensionless relative speed `β = v/c`. -/
def speedFractionOfLight (setup : SpacecraftMirrorRoundTripSetup) : ℝ :=
  speedInMetersPerSecond setup.spacecraftSpeedRelativeToS /
    vacuumLightSpeedInMetersPerSecond

/-- Physlib's Lorentz factor for the relative spacecraft speed. -/
def spacecraftLorentzFactor
    (setup : SpacecraftMirrorRoundTripSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-!
Minkowski proper time between emission and reception, converted from the
metre-valued spacetime convention to seconds.  This is a general observable
definition and contains no problem-specific numerical answer.
-/
def emissionToReceptionProperTimeSeconds
    (setup : SpacecraftMirrorRoundTripSetup) : ℝ :=
  SpaceTime.properTime (setup.event .emission) (setup.event .reception) /
    vacuumLightSpeedInMetersPerSecond

/-! ## Scenario, primary-image evidence, and stated data -/

/-- Object roles, frame roles, and directions stated in the prose. -/
structure MatchesCoastingSpacecraftMirrorScenario
    (setup : SpacecraftMirrorRoundTripSetup) : Prop where
  mirrorRestFrameIsS : setup.referenceFrame = .S
  observerFrameIsSpacecraftRest : setup.spacecraftFrame = .spacecraftRest
  spacecraftIsCoasting :
    setup.spacecraftMotionModel = .inertialCoasting
  mirrorIsStationaryIdealReflector :
    setup.mirrorModel = .stationaryPlaneIdealReflector
  signalIsLightPulse : setup.signalKind = .lightPulse
  spacecraftMovesTowardMirror :
    setup.spacecraftDirectionInS = .towardMirror
  outboundPulseMovesTowardMirror :
    setup.pulseDirection .outbound = .towardMirror
  returnPulseMovesAwayFromMirror :
    setup.pulseDirection .reflectedReturn = .awayFromMirror

/-!
Primary-image evidence: the spacecraft lies left of the vertical blue mirror;
the red velocity and pulse arrows point toward it; `d` is double-headed; and
the labels `S`, `O`, `Mirror`, `d`, and vector `v` are visible.
-/
structure MatchesSuppliedSpacecraftMirrorFigure
    (figure : SpacecraftMirrorFigure) : Prop where
  everyObjectShown : ∀ object, figure.objectShown object = true
  everyAxisShown : ∀ axis, figure.axisShown axis = true
  everyLabelShown : ∀ label, figure.labelShown label = true
  verticalAxisCarriesS :
    figure.axisLabel .verticalFrameAxis = some .frameS
  horizontalBaselineHasNoPrintedAxisLabel :
    figure.axisLabel .horizontalBaseline = none
  axisOriginCarriesO : figure.axisOriginLabel = .originO
  mirrorCarriesMirrorLabel : figure.objectLabel .mirror = some .mirror
  spacecraftHasNoPrintedObjectLabel :
    figure.objectLabel .spacecraft = none
  pulseHasNoPrintedObjectLabel : figure.objectLabel .lightPulse = none
  spacecraftAppearsLeftOfMirror : figure.spacecraftLeftOfMirror = true
  mirrorIsVertical : figure.mirrorDrawnVertically = true
  distanceArrowBeginsAtSpacecraft :
    figure.distanceArrowLeftEndpoint = .spacecraft
  distanceArrowEndsAtMirror : figure.distanceArrowRightEndpoint = .mirror
  velocityArrowPointsTowardMirror :
    figure.arrowDirection .spacecraftVelocity = some .towardMirror
  outgoingPulsePointsTowardMirror :
    figure.arrowDirection .outgoingPulse = some .towardMirror
  distanceArrowHasNoTravelDirection :
    figure.arrowDirection .separationDistance = none
  velocityArrowIsSingleHeaded :
    figure.arrowStyle .spacecraftVelocity = .singleHeaded
  pulseArrowIsSingleHeaded :
    figure.arrowStyle .outgoingPulse = .singleHeaded
  distanceArrowIsDoubleHeaded :
    figure.arrowStyle .separationDistance = .doubleHeaded
  velocityArrowCarriesV :
    figure.arrowLabel .spacecraftVelocity = some .velocityV
  distanceArrowCarriesD :
    figure.arrowLabel .separationDistance = some .distanceD
  pulseArrowHasNoText : figure.arrowLabel .outgoingPulse = none
  mirrorIsBlue : figure.objectColor .mirror = .blue
  spacecraftIsGray : figure.objectColor .spacecraft = .gray
  outgoingPulseIsRed : figure.objectColor .lightPulse = .red
  velocityArrowIsRed : figure.arrowColor .spacecraftVelocity = .red
  pulseArrowIsRed : figure.arrowColor .outgoingPulse = .red

/-!
The two numerical readouts supplied by the problem statement.  They determine
the initial separation and relative speed, not either round-trip duration.
-/
structure MatchesProblemReadouts
    (setup : SpacecraftMirrorRoundTripSetup) : Prop where
  initialSeparationMeters :
    lengthInMeters setup.initialSeparationInS = 56600000000
  speedIsPointSixFiveC : speedFractionOfLight setup = (13 / 20 : ℝ)

/-- Positivity, subluminality, and chronological ordering of the experiment. -/
structure HasPhysicalRoundTripParameters
    (setup : SpacecraftMirrorRoundTripSetup) : Prop where
  positiveInitialSeparation :
    0 < lengthInMeters setup.initialSeparationInS
  nonnegativeSpeedFraction : 0 ≤ speedFractionOfLight setup
  subluminalSpacecraft : speedFractionOfLight setup < 1
  positiveReferenceDuration :
    0 < durationInSeconds setup.referenceFrameRoundTripDuration
  positiveSpacecraftDuration :
    0 < durationInSeconds setup.spacecraftMeasuredRoundTripDuration
  emissionBeforeReflection :
    eventTimeInSSeconds setup .emission <
      eventTimeInSSeconds setup .reflection
  reflectionBeforeReception :
    eventTimeInSSeconds setup .reflection <
      eventTimeInSSeconds setup .reception

/-! ## Governing light-propagation and special-relativistic laws -/

/-!
Worldlines and coincidences in frame `S`.  The coordinate origin is chosen at
emission.  The mirror stays at `d`, the spacecraft coasts at `v`, the pulse
travels at `c` before and after ideal reflection, and the stored frame-`S`
duration is the emission-to-reception coordinate-time difference.
-/
structure SatisfiesReferenceFrameLightPropagation
    (setup : SpacecraftMirrorRoundTripSetup) : Prop where
  emissionTimeIsZero : eventTimeInSSeconds setup .emission = 0
  emissionPositionIsZero : eventPositionInSMeters setup .emission = 0
  mirrorWorldline : ∀ t : ℝ,
    setup.objectPositionInSMeters .mirror t =
      lengthInMeters setup.initialSeparationInS
  spacecraftWorldline : ∀ t : ℝ,
    setup.objectPositionInSMeters .spacecraft t =
      speedInMetersPerSecond setup.spacecraftSpeedRelativeToS * t
  emissionCoincidence :
    setup.objectPositionInSMeters .spacecraft
          (eventTimeInSSeconds setup .emission) =
        eventPositionInSMeters setup .emission ∧
      setup.objectPositionInSMeters .lightPulse
          (eventTimeInSSeconds setup .emission) =
        eventPositionInSMeters setup .emission
  reflectionCoincidence :
    setup.objectPositionInSMeters .mirror
          (eventTimeInSSeconds setup .reflection) =
        eventPositionInSMeters setup .reflection ∧
      setup.objectPositionInSMeters .lightPulse
          (eventTimeInSSeconds setup .reflection) =
        eventPositionInSMeters setup .reflection
  receptionCoincidence :
    setup.objectPositionInSMeters .spacecraft
          (eventTimeInSSeconds setup .reception) =
        eventPositionInSMeters setup .reception ∧
      setup.objectPositionInSMeters .lightPulse
          (eventTimeInSSeconds setup .reception) =
        eventPositionInSMeters setup .reception
  outboundLightWorldline : ∀ t : ℝ,
    eventTimeInSSeconds setup .emission ≤ t →
    t ≤ eventTimeInSSeconds setup .reflection →
    setup.objectPositionInSMeters .lightPulse t =
      eventPositionInSMeters setup .emission +
        vacuumLightSpeedInMetersPerSecond *
          (t - eventTimeInSSeconds setup .emission)
  reflectedLightWorldline : ∀ t : ℝ,
    eventTimeInSSeconds setup .reflection ≤ t →
    t ≤ eventTimeInSSeconds setup .reception →
    setup.objectPositionInSMeters .lightPulse t =
      eventPositionInSMeters setup .reflection -
        vacuumLightSpeedInMetersPerSecond *
          (t - eventTimeInSSeconds setup .reflection)
  referenceDurationAccounting :
    durationInSeconds setup.referenceFrameRoundTripDuration =
      eventTimeInSSeconds setup .reception -
        eventTimeInSSeconds setup .emission

/-!
The generic proper-time law for two events on an inertially coasting clock.
The first field connects the dimensionful spacecraft observable to Physlib's
Minkowski interval; the second is the equivalent Lorentz time-dilation law.
Neither field supplies the numerical duration requested in this problem.
-/
structure SatisfiesSpecialRelativisticProperTime
    (setup : SpacecraftMirrorRoundTripSetup) : Prop where
  spacecraftClockReadsMinkowskiProperTime :
    durationInSeconds setup.spacecraftMeasuredRoundTripDuration =
      emissionToReceptionProperTimeSeconds setup
  timeDilationLaw :
    durationInSeconds setup.referenceFrameRoundTripDuration =
      spacecraftLorentzFactor setup *
        durationInSeconds setup.spacecraftMeasuredRoundTripDuration

/-! ## Derived duration relations -/

/-!
Solving the two light worldlines and the spacecraft worldline in frame `S`
gives `Δt_S = 2d / (c + v)`.  This is a conclusion, not a propagation-law
field.
-/
lemma referenceFrameRoundTripDuration_formula
    (setup : SpacecraftMirrorRoundTripSetup)
    (hPhysical : HasPhysicalRoundTripParameters setup)
    (hPropagation : SatisfiesReferenceFrameLightPropagation setup) :
    durationInSeconds setup.referenceFrameRoundTripDuration =
      2 * lengthInMeters setup.initialSeparationInS /
        (vacuumLightSpeedInMetersPerSecond +
          speedInMetersPerSecond setup.spacecraftSpeedRelativeToS) := by
  have hReflectionPosition :
      eventPositionInSMeters setup .reflection =
        lengthInMeters setup.initialSeparationInS := by
    calc
      eventPositionInSMeters setup .reflection =
          setup.objectPositionInSMeters .mirror
            (eventTimeInSSeconds setup .reflection) :=
        hPropagation.reflectionCoincidence.1.symm
      _ = lengthInMeters setup.initialSeparationInS :=
        hPropagation.mirrorWorldline _
  have hOutboundAtReflection :
      eventPositionInSMeters setup .reflection =
        vacuumLightSpeedInMetersPerSecond *
          eventTimeInSSeconds setup .reflection := by
    calc
      eventPositionInSMeters setup .reflection =
          setup.objectPositionInSMeters .lightPulse
            (eventTimeInSSeconds setup .reflection) :=
        hPropagation.reflectionCoincidence.2.symm
      _ = eventPositionInSMeters setup .emission +
          vacuumLightSpeedInMetersPerSecond *
            (eventTimeInSSeconds setup .reflection -
              eventTimeInSSeconds setup .emission) :=
        hPropagation.outboundLightWorldline _
          (le_of_lt hPhysical.emissionBeforeReflection) le_rfl
      _ = vacuumLightSpeedInMetersPerSecond *
          eventTimeInSSeconds setup .reflection := by
        rw [hPropagation.emissionPositionIsZero,
          hPropagation.emissionTimeIsZero]
        ring
  have hSeparationAtReflection :
      lengthInMeters setup.initialSeparationInS =
        vacuumLightSpeedInMetersPerSecond *
          eventTimeInSSeconds setup .reflection := by
    rw [← hReflectionPosition, hOutboundAtReflection]
  have hSpacecraftAtReception :
      eventPositionInSMeters setup .reception =
        speedInMetersPerSecond setup.spacecraftSpeedRelativeToS *
          eventTimeInSSeconds setup .reception := by
    calc
      eventPositionInSMeters setup .reception =
          setup.objectPositionInSMeters .spacecraft
            (eventTimeInSSeconds setup .reception) :=
        hPropagation.receptionCoincidence.1.symm
      _ = speedInMetersPerSecond setup.spacecraftSpeedRelativeToS *
          eventTimeInSSeconds setup .reception :=
        hPropagation.spacecraftWorldline _
  have hReturnAtReception :
      eventPositionInSMeters setup .reception =
        eventPositionInSMeters setup .reflection -
          vacuumLightSpeedInMetersPerSecond *
            (eventTimeInSSeconds setup .reception -
              eventTimeInSSeconds setup .reflection) := by
    calc
      eventPositionInSMeters setup .reception =
          setup.objectPositionInSMeters .lightPulse
            (eventTimeInSSeconds setup .reception) :=
        hPropagation.receptionCoincidence.2.symm
      _ = eventPositionInSMeters setup .reflection -
          vacuumLightSpeedInMetersPerSecond *
            (eventTimeInSSeconds setup .reception -
              eventTimeInSSeconds setup .reflection) :=
        hPropagation.reflectedLightWorldline _
          (le_of_lt hPhysical.reflectionBeforeReception) le_rfl
  have hReceptionEquation :
      (vacuumLightSpeedInMetersPerSecond +
          speedInMetersPerSecond setup.spacecraftSpeedRelativeToS) *
          eventTimeInSSeconds setup .reception =
        2 * lengthInMeters setup.initialSeparationInS := by
    rw [hSpacecraftAtReception] at hReturnAtReception
    rw [hReflectionPosition] at hReturnAtReception
    nlinarith [hSeparationAtReflection]
  have hDenominator :
      vacuumLightSpeedInMetersPerSecond +
          speedInMetersPerSecond setup.spacecraftSpeedRelativeToS ≠ 0 := by
    intro hZero
    rw [hZero, zero_mul] at hReceptionEquation
    nlinarith [hPhysical.positiveInitialSeparation]
  rw [hPropagation.referenceDurationAccounting,
    hPropagation.emissionTimeIsZero, sub_zero]
  exact (eq_div_iff hDenominator).2 (by
    simpa [mul_comm] using hReceptionEquation)

/-!
The coasting spacecraft clock records the frame-`S` round-trip duration divided
by `γ(v/c)`.  Combining this with the light-worldline result yields the exact
proper-time formula used to evaluate the answer list.
-/
lemma spacecraftRoundTripDuration_formula
    (setup : SpacecraftMirrorRoundTripSetup)
    (hPhysical : HasPhysicalRoundTripParameters setup)
    (hPropagation : SatisfiesReferenceFrameLightPropagation setup)
    (hProperTime : SatisfiesSpecialRelativisticProperTime setup) :
    durationInSeconds setup.spacecraftMeasuredRoundTripDuration =
      (2 * lengthInMeters setup.initialSeparationInS /
          (vacuumLightSpeedInMetersPerSecond +
            speedInMetersPerSecond setup.spacecraftSpeedRelativeToS)) /
        spacecraftLorentzFactor setup := by
  have hReference :=
    referenceFrameRoundTripDuration_formula setup hPhysical hPropagation
  have hGammaNeZero : spacecraftLorentzFactor setup ≠ 0 := by
    intro hGammaZero
    have hTimeDilation := hProperTime.timeDilationLaw
    rw [hGammaZero, zero_mul] at hTimeDilation
    nlinarith [hPhysical.positiveReferenceDuration]
  apply (eq_div_iff hGammaNeZero).2
  calc
    durationInSeconds setup.spacecraftMeasuredRoundTripDuration *
          spacecraftLorentzFactor setup =
        spacecraftLorentzFactor setup *
          durationInSeconds setup.spacecraftMeasuredRoundTripDuration := by
      ring
    _ = durationInSeconds setup.referenceFrameRoundTripDuration :=
      hProperTime.timeDilationLaw.symm
    _ = _ := hReference

/-! ## Displayed answers and formalization target -/

/-- Labels of the four whole-second answers in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 77
  | .B => 136
  | .C => 89
  | .D => 174

/-- The answer label recorded by the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a whole-second displayed value.  The half-second tolerance is
the usual interval for rounding a real duration to the nearest second.
-/
def MatchesDisplayedTimeChoice
    (duration : DurationQuantity) (choice : AnswerChoice) : Prop :=
  |durationInSeconds duration - choice.seconds| ≤ (1 / 2 : ℝ)

/-- The chosen value is strictly closer than every alternative in the list. -/
def IsUniqueClosestTimeChoice
    (duration : DurationQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |durationInSeconds duration - choice.seconds| <
      |durationInSeconds duration - other.seconds|

/-!
Physics formalization target `thm:physics:phyx_mini_0528:target`.

For `d = 5.66 × 10^10 m` and `v = 0.650 c`, the coasting spacecraft records
approximately `173.91 s`.  This rounds to `174 s`, and recorded answer D is the
unique closest displayed option.
-/
theorem problem_phyx_mini_0528
    (setup : SpacecraftMirrorRoundTripSetup)
    (hScenario : MatchesCoastingSpacecraftMirrorScenario setup)
    (hFigure : MatchesSuppliedSpacecraftMirrorFigure setup.figure)
    (hData : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalRoundTripParameters setup)
    (hPropagation : SatisfiesReferenceFrameLightPropagation setup)
    (hProperTime : SatisfiesSpecialRelativisticProperTime setup) :
    MatchesDisplayedTimeChoice
        setup.spacecraftMeasuredRoundTripDuration recordedAnswerChoice ∧
      IsUniqueClosestTimeChoice
        setup.spacecraftMeasuredRoundTripDuration recordedAnswerChoice := by
  have hc : vacuumLightSpeedInMetersPerSecond = 299792458 := by
    change (DimSpeed.speedOfLight UnitChoices.SI).val = 299792458
    rw [DimSpeed.speedOfLight_in_SI]
  have hBeta := hData.speedIsPointSixFiveC
  rw [speedFractionOfLight, hc] at hBeta
  have hv :
      speedInMetersPerSecond setup.spacecraftSpeedRelativeToS =
        (13 / 20 : ℝ) * 299792458 :=
    (div_eq_iff (by norm_num : (299792458 : ℝ) ≠ 0)).mp hBeta
  have hDuration :=
    spacecraftRoundTripDuration_formula setup hPhysical hPropagation
      hProperTime
  rw [hData.initialSeparationMeters, hc, hv, spacecraftLorentzFactor,
    hData.speedIsPointSixFiveC, LorentzGroup.γ] at hDuration
  norm_num at hDuration
  have hsqrtPos : 0 < Real.sqrt (231 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hDuration' :
      durationInSeconds setup.spacecraftMeasuredRoundTripDuration =
        (56600000000 / 4946575557 : ℝ) * Real.sqrt 231 := by
    rw [hDuration]
    field_simp
    norm_num
  have hsqrtSq : (Real.sqrt (231 : ℝ)) ^ 2 = 231 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt (231 : ℝ) :=
    Real.sqrt_nonneg _
  have hsqrtLower : (1519 / 100 : ℝ) < Real.sqrt 231 := by
    nlinarith
  have hsqrtUpper : Real.sqrt 231 < (152 / 10 : ℝ) := by
    nlinarith
  have hTimeLower :
      (347 / 2 : ℝ) <
        durationInSeconds setup.spacecraftMeasuredRoundTripDuration := by
    rw [hDuration']
    nlinarith [hsqrtLower]
  have hTimeUpper :
      durationInSeconds setup.spacecraftMeasuredRoundTripDuration <
        (349 / 2 : ℝ) := by
    rw [hDuration']
    nlinarith [hsqrtUpper]
  constructor
  · change
      |durationInSeconds setup.spacecraftMeasuredRoundTripDuration - 174| ≤
        (1 / 2 : ℝ)
    rw [abs_le]
    constructor <;> nlinarith
  · change ∀ other, other ≠ AnswerChoice.D →
      |durationInSeconds setup.spacecraftMeasuredRoundTripDuration - 174| <
        |durationInSeconds setup.spacecraftMeasuredRoundTripDuration -
          other.seconds|
    intro other hOther
    have hChosenError :
        |durationInSeconds setup.spacecraftMeasuredRoundTripDuration - 174| <
          (1 / 2 : ℝ) := by
      rw [abs_lt]
      constructor <;> nlinarith
    cases other with
    | A =>
        have hAlternativeError :
            (1 / 2 : ℝ) <
              |durationInSeconds setup.spacecraftMeasuredRoundTripDuration -
                AnswerChoice.A.seconds| := by
          rw [AnswerChoice.seconds,
            abs_of_pos (by nlinarith [hTimeLower])]
          nlinarith [hTimeLower]
        exact lt_trans hChosenError hAlternativeError
    | B =>
        have hAlternativeError :
            (1 / 2 : ℝ) <
              |durationInSeconds setup.spacecraftMeasuredRoundTripDuration -
                AnswerChoice.B.seconds| := by
          rw [AnswerChoice.seconds,
            abs_of_pos (by nlinarith [hTimeLower])]
          nlinarith [hTimeLower]
        exact lt_trans hChosenError hAlternativeError
    | C =>
        have hAlternativeError :
            (1 / 2 : ℝ) <
              |durationInSeconds setup.spacecraftMeasuredRoundTripDuration -
                AnswerChoice.C.seconds| := by
          rw [AnswerChoice.seconds,
            abs_of_pos (by nlinarith [hTimeLower])]
          nlinarith [hTimeLower]
        exact lt_trans hChosenError hAlternativeError
    | D => exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0528
