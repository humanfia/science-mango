import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0176

open Dimension

/-!
# Wave speed of a four-loop standing wave on a string

The primary image shows a transverse standing wave between two shaded fixed
supports. There are four antinodal loops between the endpoint nodes, and the
double-headed dimension arrow gives the support separation as `60 cm`. Thus
the picture contains four half-wavelength segments, rather than the three
complete wavelengths stated in the auxiliary machine-generated caption. The
oscillation frequency supplied by the prose is `100 Hz`.

Length, frequency, and propagation speed are represented by unit-independent
Physlib quantities. Real numbers below are used only for readouts in named
units and for the displayed multiple-choice values. In particular, wavelength
and wave speed are independent setup fields related to the measured data only
through the governing standing-wave and propagation laws.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimeter readout used by the dimension arrow in the primary image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of the string-wave propagation speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- The two shaded boundaries of the vibrating string segment. -/
inductive StringEndpoint where
  | left
  | right
  deriving DecidableEq, Repr

/-- Boundary conditions relevant to the endpoint nodes in the figure. -/
inductive StringBoundaryCondition where
  | fixed
  | free
  deriving DecidableEq, Repr

/-- The physical type of the blue disturbance drawn in the primary image. -/
inductive StringWaveKind where
  | transverseStandingWave
  | travelingWave
  deriving DecidableEq, Repr

/-- The material system on which the wave propagates. -/
inductive WaveMediumKind where
  | stretchedString
  deriving DecidableEq, Repr

/-!
Independent physical quantities and qualitative figure data for the standing
wave. `visibleAntinodalLoopCount` is the number of lobes between successive
nodes; each such lobe occupies one half-wavelength. Neither `wavelength` nor
`propagationSpeed` is assigned a numerical value here.
-/
structure StandingWaveOnStringSetup where
  mediumKind : WaveMediumKind
  waveKind : StringWaveKind
  boundaryCondition : StringEndpoint → StringBoundaryCondition
  endpointIsNode : StringEndpoint → Bool
  spanBetweenSupports : LengthQuantity
  wavelength : LengthQuantity
  oscillationFrequency : FrequencyQuantity
  propagationSpeed : SpeedQuantity
  visibleAntinodalLoopCount : ℕ

/-!
The prose and primary-image readouts. The image visibly contains four loops,
so it represents four half-wavelength intervals across the `60 cm` span.
-/
structure MatchesProblemAndFigureReadouts
    (setup : StandingWaveOnStringSetup) : Prop where
  mediumIsString : setup.mediumKind = .stretchedString
  waveIsStanding : setup.waveKind = .transverseStandingWave
  leftBoundaryFixed : setup.boundaryCondition .left = .fixed
  rightBoundaryFixed : setup.boundaryCondition .right = .fixed
  leftEndpointNode : setup.endpointIsNode .left = true
  rightEndpointNode : setup.endpointIsNode .right = true
  supportSeparationCentimeters :
    lengthInCentimeters setup.spanBetweenSupports = 60
  frequencyHertz : frequencyInHertz setup.oscillationFrequency = 100
  visibleLoopCount : setup.visibleAntinodalLoopCount = 4

/-- Positivity and nondegeneracy conditions for the pictured string mode. -/
structure HasPhysicalStandingWaveParameters
    (setup : StandingWaveOnStringSetup) : Prop where
  spanPositive : 0 < lengthInMeters setup.spanBetweenSupports
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  frequencyPositive : 0 < frequencyInHertz setup.oscillationFrequency
  propagationSpeedPositive :
    0 < speedInMetersPerSecond setup.propagationSpeed
  loopCountPositive : 0 < setup.visibleAntinodalLoopCount

/-!
Governing relations for this fixed-end string mode.

The first field expresses `2 L = n λ`, where `n` is the number of visible
antinodal loops (equivalently, half-wavelength segments). The second is the
standard kinematic relation `v = f λ`. These laws relate the independent
physical quantities but state neither the inferred wavelength nor the
requested numerical speed.
-/
structure SatisfiesStandingWaveLaws
    (setup : StandingWaveOnStringSetup) : Prop where
  fixedEndpointHarmonicGeometry :
    2 * lengthInMeters setup.spanBetweenSupports =
      (setup.visibleAntinodalLoopCount : ℝ) *
        lengthInMeters setup.wavelength
  waveSpeedFrequencyWavelengthRelation :
    speedInMetersPerSecond setup.propagationSpeed =
      frequencyInHertz setup.oscillationFrequency *
        lengthInMeters setup.wavelength

/-- The answer labels printed alongside the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed answer speeds, in meters per second. -/
def displayedAnswerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 15
  | .B => 60
  | .C => 50
  | .D => 30

/-- The answer recorded in the dataset metadata; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A physical setup's speed agrees with the displayed value of a choice. -/
def MatchesAnswerChoice
    (setup : StandingWaveOnStringSetup) (choice : AnswerChoice) : Prop :=
  speedInMetersPerSecond setup.propagationSpeed =
    displayedAnswerSpeedInMetersPerSecond choice

/-- General conversion between the two length readouts used in this problem. -/
lemma lengthInMeters_eq_lengthInCentimeters_div_hundred
    (length : LengthQuantity) :
    lengthInMeters length = lengthInCentimeters length / 100 := by
  change
    ((length UnitChoices.SI).val : ℝ) =
      ((length
        {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) / 100
  rw [length.2 UnitChoices.SI
    {UnitChoices.SI with length := LengthUnit.centimeters}]
  have hscale :
      UnitChoices.dimScale UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters}
        (dim (WithDim L𝓭 NNReal)) = 100 := by
    apply NNReal.eq
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    rfl
  rw [hscale]
  norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]

/-!
The four-loop fixed-end geometry and the `60 cm` span imply a wavelength of
`0.30 m`. This is an intermediate physical conclusion, not an input premise.
-/
lemma wavelength_is_three_tenths_meter
    (setup : StandingWaveOnStringSetup)
    (hfigure : MatchesProblemAndFigureReadouts setup)
    (hlaws : SatisfiesStandingWaveLaws setup) :
    lengthInMeters setup.wavelength = 3 / 10 := by
  have hspan :=
    lengthInMeters_eq_lengthInCentimeters_div_hundred
      setup.spanBetweenSupports
  rw [hfigure.supportSeparationCentimeters] at hspan
  have hgeometry := hlaws.fixedEndpointHarmonicGeometry
  rw [hfigure.visibleLoopCount, hspan] at hgeometry
  norm_num at hgeometry ⊢
  linarith

/-!
At `100 Hz`, the derived `0.30 m` wavelength gives a wave speed of `30 m/s`,
which is displayed answer choice D.
-/
theorem problem_phyx_mini_0176
    (setup : StandingWaveOnStringSetup)
    (hphysical : HasPhysicalStandingWaveParameters setup)
    (hfigure : MatchesProblemAndFigureReadouts setup)
    (hlaws : SatisfiesStandingWaveLaws setup) :
    speedInMetersPerSecond setup.propagationSpeed = 30 ∧
      MatchesAnswerChoice setup .D := by
  have hwavelength :=
    wavelength_is_three_tenths_meter setup hfigure hlaws
  have hspeed := hlaws.waveSpeedFrequencyWavelengthRelation
  rw [hfigure.frequencyHertz, hwavelength] at hspeed
  norm_num at hspeed
  constructor
  · exact hspeed
  · unfold MatchesAnswerChoice displayedAnswerSpeedInMetersPerSecond
    exact hspeed

end PhyXMiniProblems.ProblemPhyXMini0176
