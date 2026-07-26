import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0509

open Dimension

/-!
# Relativistic contraction of a passing spaceship

A crew member measures the spaceship's proper length to be `400 m`.  The
spaceship passes Earth in the positive `x` direction at `0.990 c`.  Earth
observers `O₁` and `O₂` use synchronized clocks to record the rear and front
endpoint positions simultaneously, so their measured length is the endpoint
separation `x₂ - x₁`.

Lengths and speed magnitudes are unit-independent Physlib quantities.  Real
numbers occur only as named unit readouts, dimensionless speed ratios, clock
coordinates, endpoint coordinates, and displayed answer values.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Meter readout used by the figure and the answer choices. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical speed in meters per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in meters per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Frames, observers, endpoint labels, and primary-image vocabulary -/

/-- The two inertial-frame labels printed or implied by the figure. -/
inductive InertialFrameLabel where
  | S
  | O
  deriving DecidableEq, Repr

/-- The two Earth observers shown with clocks. -/
inductive EarthObserver where
  | O1
  | O2
  deriving DecidableEq, Repr

/-- The rear and front endpoints of the spaceship along its motion axis. -/
inductive SpacecraftEndpoint where
  | rear
  | front
  deriving DecidableEq, Repr

/-- Coordinate-position labels attached to the endpoint rays in the image. -/
inductive PositionLabel where
  | x1
  | x2
  deriving DecidableEq, Repr

/-- Length labels printed in the supplied image. -/
inductive FigureLengthLabel where
  | l0
  | l
  deriving DecidableEq, Repr

/-- Coordinate axes visible in the supplied schematic. -/
inductive CoordinateAxis where
  | x
  | y
  deriving DecidableEq, Repr

/-- Direction of the spaceship's velocity arrow. -/
inductive AxisDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-- Physical kind of the moving object in the scenario. -/
inductive MovingObjectKind where
  | spaceship
  deriving DecidableEq, Repr

/-- Named objects and annotations directly visible in the primary image. -/
inductive FigureFeature where
  | spaceship
  | telescopingBody
  | earthSurface
  | observerO1
  | observerO2
  | clockO1
  | clockO2
  | xAxis
  | yAxis
  | frameS
  | frameO
  | positionX1
  | positionX2
  | properLengthL0
  | contractedLengthL
  | velocityArrow
  | speed0990c
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and printed evidence from `phyx_data/test_image/509.png`.
Numerical annotations are scalar readouts; the corresponding dimensionful
quantities live in `SpaceshipLengthContractionSetup` below.
-/
structure SpaceshipLengthContractionFigure where
  shows : FigureFeature → Bool
  spacecraftFrameLabel : InertialFrameLabel
  earthFrameLabel : InertialFrameLabel
  horizontalAxis : CoordinateAxis
  verticalAxis : CoordinateAxis
  endpointPositionLabel : SpacecraftEndpoint → PositionLabel
  observerAtEndpoint : SpacecraftEndpoint → EarthObserver
  properLengthLabel : FigureLengthLabel
  contractedLengthLabel : FigureLengthLabel
  velocityArrowDirection : AxisDirection
  printedProperLengthMeters : ℝ
  printedSpeedFractionOfLight : ℝ

/-!
All independent physical quantities and coordinate readouts in the problem.

`crewMeasuredRestLength` is measured in the spaceship rest frame.  The
`earthMeasuredLength` field is an independent Earth-frame observable; it is
not defined from an answer choice or from the contraction formula.
-/
structure SpaceshipLengthContractionSetup where
  figure : SpaceshipLengthContractionFigure
  movingObjectKind : MovingObjectKind
  crewMeasurementFrame : InertialFrameLabel
  earthMeasurementFrame : InertialFrameLabel
  crewMeasuredRestLength : LengthQuantity
  earthMeasuredLength : LengthQuantity
  relativeSpeed : DimSpeed
  motionDirection : AxisDirection
  earthEndpointCoordinateMeters : SpacecraftEndpoint → ℝ
  earthClockReadingSeconds : EarthObserver → ℝ

/-- The dimensionless speed parameter `β = v/c`. -/
def speedFractionOfLight (setup : SpaceshipLengthContractionSetup) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- The Lorentz factor supplied by Physlib for the setup's `v/c`. -/
def lorentzFactor (setup : SpaceshipLengthContractionSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Scenario, figure/data readouts, and governing physics -/

/-- The crew and Earth observers use the two inertial frames in the figure. -/
structure MatchesPassingSpaceshipScenario
    (setup : SpaceshipLengthContractionSetup) : Prop where
  objectIsSpaceship : setup.movingObjectKind = .spaceship
  crewUsesSpaceshipFrame : setup.crewMeasurementFrame = .S
  earthObserversUseEarthFrame : setup.earthMeasurementFrame = .O
  travelsTowardPositiveX : setup.motionDirection = .positiveX

/-!
Primary-image evidence: the two observers and their clocks, both coordinate
axes, both frame labels, both endpoint-coordinate rays, both length labels,
the rightward velocity arrow, and the `400 m` and `0.990 c` annotations.
-/
structure MatchesSuppliedSpaceshipFigure
    (figure : SpaceshipLengthContractionFigure) : Prop where
  everyNamedFeatureShown : ∀ feature, figure.shows feature = true
  spacecraftFrameIsS : figure.spacecraftFrameLabel = .S
  earthFrameIsO : figure.earthFrameLabel = .O
  horizontalAxisIsX : figure.horizontalAxis = .x
  verticalAxisIsY : figure.verticalAxis = .y
  rearCoordinateIsX1 : figure.endpointPositionLabel .rear = .x1
  frontCoordinateIsX2 : figure.endpointPositionLabel .front = .x2
  observerO1AtRear : figure.observerAtEndpoint .rear = .O1
  observerO2AtFront : figure.observerAtEndpoint .front = .O2
  restLengthLabelIsL0 : figure.properLengthLabel = .l0
  earthLengthLabelIsL : figure.contractedLengthLabel = .l
  velocityPointsRight : figure.velocityArrowDirection = .positiveX
  properLengthAnnotationMeters : figure.printedProperLengthMeters = 400
  speedAnnotationFractionOfLight :
    figure.printedSpeedFractionOfLight = (99 / 100 : ℝ)

/-!
The problem data connect the dimensionful rest length and relative speed to
the two scalar annotations in the figure.  No Earth-frame answer occurs here.
-/
structure MatchesProblemReadouts
    (setup : SpaceshipLengthContractionSetup) : Prop where
  crewLengthMatchesFigure :
    lengthInMeters setup.crewMeasuredRestLength =
      setup.figure.printedProperLengthMeters
  relativeSpeedMatchesFigure :
    speedFractionOfLight setup = setup.figure.printedSpeedFractionOfLight

/-- Positivity, endpoint ordering, and the subluminal regime of the model. -/
structure HasPhysicalRelativisticParameters
    (setup : SpaceshipLengthContractionSetup) : Prop where
  positiveRestLength : 0 < lengthInMeters setup.crewMeasuredRestLength
  positiveEarthLength : 0 < lengthInMeters setup.earthMeasuredLength
  nonnegativeSpeedFraction : 0 ≤ speedFractionOfLight setup
  subluminalSpeedFraction : speedFractionOfLight setup < 1
  rearPrecedesFront :
    setup.earthEndpointCoordinateMeters .rear <
      setup.earthEndpointCoordinateMeters .front

/-!
Operational definition of an Earth-frame length measurement.  Observers
`O₁` and `O₂` read the rear and front positions simultaneously, and the
reported length is the coordinate separation `x₂ - x₁`.
-/
structure SatisfiesSimultaneousEarthEndpointMeasurement
    (setup : SpaceshipLengthContractionSetup) : Prop where
  synchronizedClockReadings :
    setup.earthClockReadingSeconds .O1 =
      setup.earthClockReadingSeconds .O2
  lengthIsEndpointSeparation :
    lengthInMeters setup.earthMeasuredLength =
      setup.earthEndpointCoordinateMeters .front -
        setup.earthEndpointCoordinateMeters .rear

/-!
The generic special-relativistic length-contraction law `L = L₀ / γ(β)`.
It is stated in every common length unit and contains neither a numerical
Earth-frame length nor an answer-choice label.
-/
structure SatisfiesSpecialRelativisticLengthContraction
    (setup : SpaceshipLengthContractionSetup) : Prop where
  contractionLaw : ∀ unit : LengthUnit,
    lengthReadout unit setup.earthMeasuredLength =
      lengthReadout unit setup.crewMeasuredRestLength /
        lorentzFactor setup

/-! ## Multiple-choice target -/

/-- Labels of the four meter-valued choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed answer length in meters, represented exactly as a rational. -/
def displayedLengthMeters : AnswerChoice → ℝ
  | .A => 351 / 10
  | .B => 277 / 10
  | .C => 321 / 10
  | .D => 282 / 5

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement with a one-decimal-place displayed answer.  A tolerance of
`0.05 m = 1/20 m` expresses rounding to the nearest tenth of a meter.
-/
def MatchesDisplayedLengthChoice
    (setup : SpaceshipLengthContractionSetup)
    (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.earthMeasuredLength -
      displayedLengthMeters choice| ≤ (1 / 20 : ℝ)

/-!
At `β = 0.990`, the Lorentz-contracted value of a `400 m` proper length is
approximately `56.4269 m`, which rounds to `56.4 m`, answer D.

This formalizes `thm:physics:phyx_mini_0509:target`.
-/
theorem problem_phyx_mini_0509
    (setup : SpaceshipLengthContractionSetup)
    (h_scenario : MatchesPassingSpaceshipScenario setup)
    (h_figure : MatchesSuppliedSpaceshipFigure setup.figure)
    (h_data : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalRelativisticParameters setup)
    (h_measurement : SatisfiesSimultaneousEarthEndpointMeasurement setup)
    (h_contraction : SatisfiesSpecialRelativisticLengthContraction setup) :
    MatchesDisplayedLengthChoice setup .D := by
  have h_rest_length :
      lengthInMeters setup.crewMeasuredRestLength = 400 := by
    calc
      lengthInMeters setup.crewMeasuredRestLength =
          setup.figure.printedProperLengthMeters :=
        h_data.crewLengthMatchesFigure
      _ = 400 := h_figure.properLengthAnnotationMeters
  have h_speed_fraction :
      speedFractionOfLight setup = (99 / 100 : ℝ) := by
    calc
      speedFractionOfLight setup =
          setup.figure.printedSpeedFractionOfLight :=
        h_data.relativeSpeedMatchesFigure
      _ = (99 / 100 : ℝ) := h_figure.speedAnnotationFractionOfLight
  have h_earth_length :
      lengthInMeters setup.earthMeasuredLength =
        400 / LorentzGroup.γ (99 / 100 : ℝ) := by
    calc
      lengthInMeters setup.earthMeasuredLength =
          lengthInMeters setup.crewMeasuredRestLength /
            lorentzFactor setup := by
        simpa [lengthInMeters] using
          h_contraction.contractionLaw LengthUnit.meters
      _ = 400 / LorentzGroup.γ (99 / 100 : ℝ) := by
        rw [h_rest_length]
        simp only [lorentzFactor, h_speed_fraction]
  have h_sqrt_ne : Real.sqrt (199 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h_contracted_value :
      (400 : ℝ) / LorentzGroup.γ (99 / 100 : ℝ) =
        4 * Real.sqrt 199 := by
    rw [LorentzGroup.γ]
    norm_num [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 199)]
    field_simp
    norm_num
  have h_sqrt_sq : (Real.sqrt (199 : ℝ)) ^ 2 = 199 :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (199 : ℝ) :=
    Real.sqrt_nonneg _
  have h_sqrt_lower :
      (1127 / 80 : ℝ) ≤ Real.sqrt 199 := by
    nlinarith
  have h_sqrt_upper :
      Real.sqrt 199 ≤ (1129 / 80 : ℝ) := by
    nlinarith
  rw [MatchesDisplayedLengthChoice, h_earth_length, h_contracted_value]
  norm_num [displayedLengthMeters, abs_le]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0509
