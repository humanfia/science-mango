import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0552

open Dimension

/-!
# Time for a platform observer to traverse a relativistic rocket

In the platform frame `O`, a rocket moves left at `0.80 c`.  At one instant
its front and back are simultaneously aligned with the two ends of a `65 m`
platform, so `65 m` is the rocket's contracted length in `O`.  In the rocket
rest frame `O'`, the platform observer crosses the rocket's proper length.

Lengths, elapsed times, and speed magnitudes are dimensionful Physlib
quantities.  Real numbers are used only for explicit unit readouts,
dimensionless speed ratios, frame coordinates, and displayed answer values.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical elapsed time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Meter readout used by the `65 m` label. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical elapsed time in a selected time unit. -/
def timeReadout (unit : TimeUnit) (elapsed : TimeQuantity) : ℝ :=
  ((elapsed {UnitChoices.SI with time := unit}).val : ℝ)

/-- Second readout used for event-time coordinates. -/
def timeInSeconds (elapsed : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds elapsed

/-- Microsecond readout used by the answer choices. -/
def timeInMicroseconds (elapsed : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.microseconds elapsed

/-- Read a physical speed magnitude in SI meters per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in meters per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Frames, endpoints, directions, and primary-image vocabulary -/

/-- The two inertial-frame labels printed in the supplied image. -/
inductive InertialFrameLabel where
  | O
  | OPrime
  deriving DecidableEq, Repr

/-- The front (nose) and back (tail) endpoints of the left-moving rocket. -/
inductive RocketEndpoint where
  | front
  | back
  deriving DecidableEq, Repr

/-- The two ends of the horizontal station platform. -/
inductive PlatformEndpoint where
  | leftEnd
  | rightEnd
  deriving DecidableEq, Repr

/-- Direction along the common rocket/platform axis. -/
inductive AxisDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Relation of the rocket's motion axis to the platform edge. -/
inductive AxisRelation where
  | parallel
  | notParallel
  deriving DecidableEq, Repr

/-- Named features visible in the primary raster `552.png`. -/
inductive FigureFeature where
  | rocket
  | platform
  | frameO
  | frameOPrime
  | lengthBracket
  | length65Meters
  | velocityArrow
  | speed08c
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and printed evidence in the primary raster.  The scalar entries
are annotations only; the corresponding physical quantities are independent
fields of `RocketPlatformSetup` below.
-/
structure RocketPlatformFigure where
  shows : FigureFeature → Bool
  platformFrameLabel : InertialFrameLabel
  rocketFrameLabel : InertialFrameLabel
  velocityArrowDirection : AxisDirection
  lengthBracketLeftEndpoint : RocketEndpoint
  lengthBracketRightEndpoint : RocketEndpoint
  printedLengthMeters : ℝ
  printedSpeedFractionOfLight : ℝ

/-!
Independent physical quantities and frame-coordinate data for the scenario.

`rocketLengthInPlatformFrame` is the simultaneous endpoint separation in
frame `O`; `rocketProperLength` is the rocket's rest length in frame `O'`.
The traversal time is an independent observable, not an answer-choice value.
-/
structure RocketPlatformSetup where
  figure : RocketPlatformFigure
  platformObserverFrame : InertialFrameLabel
  rocketRestFrame : InertialFrameLabel
  relativeMotionDirectionInPlatformFrame : AxisDirection
  motionAxisRelationToPlatformEdge : AxisRelation
  platformLength : LengthQuantity
  rocketLengthInPlatformFrame : LengthQuantity
  rocketProperLength : LengthQuantity
  relativeSpeed : DimSpeed
  traversalTimeAccordingToRocket : TimeQuantity
  platformEndpointCoordinateMeters : PlatformEndpoint → ℝ
  rocketEndpointCoordinateInPlatformFrameMeters : RocketEndpoint → ℝ
  alignmentTimeInPlatformFrameSeconds : RocketEndpoint → ℝ
  observerCrossingTimeInRocketFrameSeconds : RocketEndpoint → ℝ

/-- The dimensionless relative-speed parameter `β = v/c`. -/
def speedFractionOfLight (setup : RocketPlatformSetup) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- Physlib's Lorentz factor for the relative speed. -/
def lorentzFactor (setup : RocketPlatformSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Scenario, figure/data readouts, and governing physics -/

/-- The frame assignments and qualitative relative motion in the prose. -/
structure MatchesPassingRocketScenario
    (setup : RocketPlatformSetup) : Prop where
  observerUsesPlatformFrame : setup.platformObserverFrame = .O
  rocketUsesRestFrame : setup.rocketRestFrame = .OPrime
  rocketMovesLeftInPlatformFrame :
    setup.relativeMotionDirectionInPlatformFrame = .leftward
  motionIsParallelToPlatformEdge :
    setup.motionAxisRelationToPlatformEdge = .parallel

/-!
Direct primary-image evidence: the rocket above the platform, both frame
labels, the `65 m` bracket spanning nose to tail, and a leftward `0.8 c`
velocity arrow.
-/
structure MatchesSuppliedRocketFigure
    (figure : RocketPlatformFigure) : Prop where
  everyNamedFeatureShown : ∀ feature, figure.shows feature = true
  platformFrameIsO : figure.platformFrameLabel = .O
  rocketFrameIsOPrime : figure.rocketFrameLabel = .OPrime
  velocityPointsLeft : figure.velocityArrowDirection = .leftward
  bracketStartsAtFront : figure.lengthBracketLeftEndpoint = .front
  bracketEndsAtBack : figure.lengthBracketRightEndpoint = .back
  lengthAnnotationMeters : figure.printedLengthMeters = 65
  speedAnnotationFractionOfLight :
    figure.printedSpeedFractionOfLight = (4 / 5 : ℝ)

/-!
The prose and image annotations are linked to the dimensionful setup.  The
rocket's platform-frame length is linked operationally through the endpoint
alignment predicate below, rather than being defined from the desired time.
-/
structure MatchesProblemReadouts (setup : RocketPlatformSetup) : Prop where
  platformLengthMatchesFigure :
    lengthInMeters setup.platformLength = setup.figure.printedLengthMeters
  relativeSpeedMatchesFigure :
    speedFractionOfLight setup = setup.figure.printedSpeedFractionOfLight

/-- Positivity, endpoint ordering, and the physical subluminal regime. -/
structure HasPhysicalRelativisticParameters
    (setup : RocketPlatformSetup) : Prop where
  positivePlatformLength : 0 < lengthInMeters setup.platformLength
  positiveRocketLengthInPlatformFrame :
    0 < lengthInMeters setup.rocketLengthInPlatformFrame
  positiveRocketProperLength : 0 < lengthInMeters setup.rocketProperLength
  positiveRelativeSpeed : 0 < speedInMetersPerSecond setup.relativeSpeed
  nonnegativeSpeedFraction : 0 ≤ speedFractionOfLight setup
  subluminalSpeedFraction : speedFractionOfLight setup < 1
  platformEndpointsOrdered :
    setup.platformEndpointCoordinateMeters .leftEnd <
      setup.platformEndpointCoordinateMeters .rightEnd
  rocketEndpointsOrderedInPlatformFrame :
    setup.rocketEndpointCoordinateInPlatformFrameMeters .front <
      setup.rocketEndpointCoordinateInPlatformFrameMeters .back
  observerCrossesFrontBeforeBackInRocketFrame :
    setup.observerCrossingTimeInRocketFrameSeconds .front <
      setup.observerCrossingTimeInRocketFrameSeconds .back

/-!
Operational form of the simultaneous alignment observed in frame `O`.
The rocket's nose is at the platform's left end and its tail at the right end
at the same `O`-frame time.  Both measured lengths are coordinate separations.
-/
structure SatisfiesSimultaneousEndpointAlignment
    (setup : RocketPlatformSetup) : Prop where
  frontAndBackAlignSimultaneously :
    setup.alignmentTimeInPlatformFrameSeconds .front =
      setup.alignmentTimeInPlatformFrameSeconds .back
  frontAtLeftPlatformEnd :
    setup.rocketEndpointCoordinateInPlatformFrameMeters .front =
      setup.platformEndpointCoordinateMeters .leftEnd
  backAtRightPlatformEnd :
    setup.rocketEndpointCoordinateInPlatformFrameMeters .back =
      setup.platformEndpointCoordinateMeters .rightEnd
  platformLengthIsEndpointSeparation :
    lengthInMeters setup.platformLength =
      setup.platformEndpointCoordinateMeters .rightEnd -
        setup.platformEndpointCoordinateMeters .leftEnd
  rocketLengthIsSimultaneousEndpointSeparation :
    lengthInMeters setup.rocketLengthInPlatformFrame =
      setup.rocketEndpointCoordinateInPlatformFrameMeters .back -
        setup.rocketEndpointCoordinateInPlatformFrameMeters .front

/-!
Operational meaning of the elapsed time asked for in frame `O'`: it is the
difference between the times when observer `O` passes the rocket's front and
back endpoints.
-/
structure SatisfiesRocketFrameTraversalMeasurement
    (setup : RocketPlatformSetup) : Prop where
  traversalDurationIsCrossingTimeDifference :
    timeInSeconds setup.traversalTimeAccordingToRocket =
      setup.observerCrossingTimeInRocketFrameSeconds .back -
        setup.observerCrossingTimeInRocketFrameSeconds .front

/-!
The two governing laws used by the solution:

* longitudinal length contraction, `L = L₀ / γ(β)`; and
* constant-speed traversal in the rocket frame, `t v = L₀`.

They are stated for arbitrary compatible unit choices and contain no
numerical traversal time or answer-choice label.
-/
structure SatisfiesRelativisticLengthAndTraversalLaws
    (setup : RocketPlatformSetup) : Prop where
  lengthContractionLaw : ∀ unit : LengthUnit,
    lengthReadout unit setup.rocketLengthInPlatformFrame =
      lengthReadout unit setup.rocketProperLength / lorentzFactor setup
  constantSpeedTraversalLaw : ∀ units : UnitChoices,
    ((setup.traversalTimeAccordingToRocket units).val : ℝ) *
        ((setup.relativeSpeed units).val : ℝ) =
      ((setup.rocketProperLength units).val : ℝ)

/-! ## Multiple-choice target -/

/-- Labels of the four microsecond-valued choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed traversal time in microseconds, represented exactly. -/
def displayedTimeMicroseconds : AnswerChoice → ℝ
  | .A => 9 / 25
  | .B => 27 / 100
  | .C => 27 / 50
  | .D => 9 / 20

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement with a two-decimal-place time display.  The half-step tolerance
`0.005 μs` accounts for rounding; the laws with Physlib's exact value of `c`
give approximately `0.4517 μs`, not exactly `0.45 μs`.
-/
def MatchesDisplayedTimeChoice
    (setup : RocketPlatformSetup) (choice : AnswerChoice) : Prop :=
  |timeInMicroseconds setup.traversalTimeAccordingToRocket -
      displayedTimeMicroseconds choice| ≤ (1 / 200 : ℝ)

/-!
The `65 m` simultaneous platform-frame length and `β = 0.80` imply a
rocket proper length of `γ · 65 m`.  Traversing that length at `0.80 c` takes
approximately `0.4517 μs` in `O'`, which is displayed as `0.45 μs`, choice D.

This formalizes `thm:physics:phyx_mini_0552:target`.
-/
theorem problem_phyx_mini_0552
    (setup : RocketPlatformSetup)
    (h_scenario : MatchesPassingRocketScenario setup)
    (h_figure : MatchesSuppliedRocketFigure setup.figure)
    (h_data : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalRelativisticParameters setup)
    (h_alignment : SatisfiesSimultaneousEndpointAlignment setup)
    (h_measurement : SatisfiesRocketFrameTraversalMeasurement setup)
    (h_laws : SatisfiesRelativisticLengthAndTraversalLaws setup) :
    MatchesDisplayedTimeChoice setup .D := by
  have hβ : speedFractionOfLight setup = (4 / 5 : ℝ) := by
    rw [h_data.relativeSpeedMatchesFigure,
      h_figure.speedAnnotationFractionOfLight]
  have hPlatformLength :
      lengthInMeters setup.platformLength = (65 : ℝ) := by
    rw [h_data.platformLengthMatchesFigure,
      h_figure.lengthAnnotationMeters]
  have hRocketLength :
      lengthInMeters setup.rocketLengthInPlatformFrame = (65 : ℝ) := by
    calc
      lengthInMeters setup.rocketLengthInPlatformFrame =
          setup.rocketEndpointCoordinateInPlatformFrameMeters .back -
            setup.rocketEndpointCoordinateInPlatformFrameMeters .front :=
        h_alignment.rocketLengthIsSimultaneousEndpointSeparation
      _ = setup.platformEndpointCoordinateMeters .rightEnd -
            setup.platformEndpointCoordinateMeters .leftEnd := by
        rw [h_alignment.frontAtLeftPlatformEnd,
          h_alignment.backAtRightPlatformEnd]
      _ = lengthInMeters setup.platformLength :=
        h_alignment.platformLengthIsEndpointSeparation.symm
      _ = 65 := hPlatformLength
  have hGamma : lorentzFactor setup = (5 / 3 : ℝ) := by
    rw [lorentzFactor, hβ]
    norm_num [LorentzGroup.γ]
  have hProperLength :
      lengthInMeters setup.rocketProperLength = (325 / 3 : ℝ) := by
    have hLengthLaw :=
      h_laws.lengthContractionLaw LengthUnit.meters
    change
      lengthInMeters setup.rocketLengthInPlatformFrame =
        lengthInMeters setup.rocketProperLength / lorentzFactor setup at hLengthLaw
    rw [hRocketLength, hGamma] at hLengthLaw
    norm_num at hLengthLaw ⊢
    linarith
  have hLightSpeed :
      vacuumSpeedOfLightInMetersPerSecond = (299792458 : ℝ) := by
    simp [vacuumSpeedOfLightInMetersPerSecond]
  have hSpeed :
      speedInMetersPerSecond setup.relativeSpeed =
        (1199169832 / 5 : ℝ) := by
    rw [speedFractionOfLight, hLightSpeed] at hβ
    norm_num at hβ ⊢
    linarith
  have hTraversalSeconds :
      timeInSeconds setup.traversalTimeAccordingToRocket =
        (1625 / 3597509496 : ℝ) := by
    have hTraversalLaw :=
      h_laws.constantSpeedTraversalLaw UnitChoices.SI
    change
      timeInSeconds setup.traversalTimeAccordingToRocket *
          speedInMetersPerSecond setup.relativeSpeed =
        lengthInMeters setup.rocketProperLength at hTraversalLaw
    rw [hSpeed, hProperLength] at hTraversalLaw
    norm_num at hTraversalLaw ⊢
    linarith
  have hMicroseconds :
      timeInMicroseconds setup.traversalTimeAccordingToRocket =
        1000000 * timeInSeconds setup.traversalTimeAccordingToRocket := by
    have hScale := setup.traversalTimeAccordingToRocket.2
      UnitChoices.SI {UnitChoices.SI with time := TimeUnit.microseconds}
    have hScaleVal :=
      congrArg (fun x => ((x.val : NNReal) : ℝ)) hScale
    norm_num [timeInMicroseconds, timeInSeconds, timeReadout,
      UnitChoices.dimScale, TimeUnit.microseconds, TimeUnit.scale,
      UnitChoices.SI, TimeUnit.div_eq_val] at hScaleVal ⊢
    rw [hScaleVal]
    congr 1
    change
      TimeUnit.seconds.val / (1 / 1000000 * TimeUnit.seconds.val) =
        (1000000 : ℝ)
    field_simp [ne_of_gt TimeUnit.seconds.val_pos]
  rw [MatchesDisplayedTimeChoice, displayedTimeMicroseconds,
    hMicroseconds, hTraversalSeconds]
  norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0552
