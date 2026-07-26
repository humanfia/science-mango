import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0247

open Dimension

/-!
# Radio-interference runway landing aid

Two coherent radio transmitters stand on opposite sides of a runway, `50 m`
apart. Their initial phases differ by `pi`, so the equal-path centerline is a
nodal line. The design requires the first intensity maxima to be `60 m` to
either side of that centerline at a downrange distance of `3.0 km`.

The source problem uses the usual leading far-field relation
`delta r * L = d * y`. It is represented below with an explicit remainder
whose bound is controlled by the transverse-to-downrange ratios, rather than
as a globally exact paraxial identity. The drawn paths `r1` and `r2` remain
named physical lengths. Lengths, frequencies, wavelengths, and propagation
speed are unit-independent Physlib quantities. Real numbers occur only as
readouts in named units, phase angles in radians, approximation remainders,
and displayed answer values.
-/

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of a selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout used for path and far-field equations. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Kilometer readout used by the stated `3.0 km` downrange distance. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Megahertz readout of a physical frequency. -/
def frequencyInMegahertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 10 ^ 6

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Physlib's exact vacuum speed-of-light readout, in meters per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- The two radio sources, distinguished by their position in the figure. -/
inductive TransmitterLabel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The two sides of the runway's nodal centerline. -/
inductive RunwaySide where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The source-to-`P` path labels printed in the primary figure. -/
inductive FigurePathLabel where
  | r1
  | r2
  deriving DecidableEq, Repr

/-- Physical kind of each coherent emitter. -/
inductive EmitterKind where
  | radioTransmitter
  deriving DecidableEq, Repr

/-- Homogeneous propagation medium used by the landing-aid model. -/
inductive PropagationMedium where
  | ambientAir
  deriving DecidableEq, Repr

/-- Response of the airplane's radio receiver. -/
inductive ReceiverResponse where
  | silent
  | warningBeep
  deriving DecidableEq, Repr

/-- Operational regions distinguished by the guidance description. -/
inductive GuidanceRegion where
  | nodalCenterline
  | offCenterline
  deriving DecidableEq, Repr

/-- Approximation used to turn the source geometry into a path difference. -/
inductive PathDifferenceApproximation where
  | controlledFarFieldParaxial
  | exactEuclidean
  deriving DecidableEq, Repr

/-- Qualitative objects and annotations visible in the primary image. -/
inductive FigureFeature where
  | runway
  | upperTransmitter
  | lowerTransmitter
  | nodalLine
  | antinodalLines
  | pointP
  | pathR1
  | pathR2
  | separation50m
  | transverseOffset60m
  | downrange3000m
  | phaseDifferencePi
  deriving DecidableEq, Repr

/-!
Qualitative content of the supplied schematic. Numerical quantities are
fields of the physical setup rather than strings hidden in this figure record.
-/
structure RadioLandingFigure where
  shows : FigureFeature → Bool
  transmitterSide : TransmitterLabel → RunwaySide
  pathLabelToP : TransmitterLabel → FigurePathLabel
  pointPSide : RunwaySide
  runwayCenteredOnNodalLine : Bool
  nodalLineExtendsStraightFromRunway : Bool
  antinodalLinesAreSymmetric : Bool
  downrangeArrowStartsAtRunway : Bool

/-!
All independent physical quantities and observations in the design.

`intensityMaximumAtOffset side order` describes the antinodal branch at the
common offset magnitude, with `order = 0` denoting the first branch away from
the nodal line. It is related to phase and wavelength only by the governing
interference law below. In particular, no setup field assigns the requested
frequency or selects an answer choice.
-/
structure RadioLandingInterferenceSetup where
  figure : RadioLandingFigure
  emitterKind : TransmitterLabel → EmitterKind
  transmitterSeparation : LengthQuantity
  runwayWidth : LengthQuantity
  downrangeDistanceToP : LengthQuantity
  transverseOffsetMagnitude : LengthQuantity
  transmitterFrequency : TransmitterLabel → FrequencyQuantity
  transmitterWavelength : TransmitterLabel → LengthQuantity
  initialPhaseRadians : TransmitterLabel → ℝ
  propagationMedium : PropagationMedium
  propagationSpeed : SpeedQuantity
  pathLengthToP : TransmitterLabel → LengthQuantity
  pathDifferenceAtP : LengthQuantity
  approximation : PathDifferenceApproximation
  intensityMaximumAtOffset : RunwaySide → ℕ → Prop
  receiverResponse : GuidanceRegion → ReceiverResponse

/-!
The lower source is the longer-path source for the pictured upper point `P`.
This helper records its initial phase advance over the upper source.
-/
def initialPhaseAdvanceRadians
    (setup : RadioLandingInterferenceSetup) : ℝ :=
  setup.initialPhaseRadians .lower - setup.initialPhaseRadians .upper

/-!
Coherent-source description: both objects are radio transmitters with one
common frequency and wavelength. The specified phase offset is kept in the
separate numerical-readout predicate below.
-/
structure MatchesCoherentRadioSourceDescription
    (setup : RadioLandingInterferenceSetup) : Prop where
  bothAreRadioTransmitters :
    ∀ source, setup.emitterKind source = .radioTransmitter
  commonFrequency :
    setup.transmitterFrequency .upper = setup.transmitterFrequency .lower
  commonWavelength :
    setup.transmitterWavelength .upper = setup.transmitterWavelength .lower

/-!
Problem and figure readouts. The two sources and runway are `50 m` across,
`P` is `60 m` from the centerline and `3.0 km = 3000 m` downrange, and the
lower transmitter initially leads the upper by `pi` radians. The same offset
on both sides is stipulated to be the first intensity maximum. No frequency
value occurs here.
-/
structure MatchesProblemAndFigureReadouts
    (setup : RadioLandingInterferenceSetup) : Prop where
  transmitterSeparationMeters :
    lengthInMeters setup.transmitterSeparation = 50
  runwayWidthMeters : lengthInMeters setup.runwayWidth = 50
  downrangeDistanceKilometers :
    lengthInKilometers setup.downrangeDistanceToP = 3
  downrangeDistanceMeters :
    lengthInMeters setup.downrangeDistanceToP = 3000
  transverseOffsetMeters :
    lengthInMeters setup.transverseOffsetMagnitude = 60
  initialPhaseAdvance : initialPhaseAdvanceRadians setup = Real.pi
  upperFirstMaximum : setup.intensityMaximumAtOffset .upper 0
  lowerFirstMaximum : setup.intensityMaximumAtOffset .lower 0

/-!
Primary-image evidence: both sources, both path labels, the runway, `P`, and
the nodal/antinodal annotations are present. The upper source-to-`P` ray is
`r1`, the lower ray is `r2`, and `P` lies above the centerline.
-/
structure MatchesSuppliedRadioLandingFigure
    (setup : RadioLandingInterferenceSetup) : Prop where
  everyFeatureShown : ∀ feature, setup.figure.shows feature = true
  upperTransmitterAboveCenterline :
    setup.figure.transmitterSide .upper = .upper
  lowerTransmitterBelowCenterline :
    setup.figure.transmitterSide .lower = .lower
  upperPathIsR1 : setup.figure.pathLabelToP .upper = .r1
  lowerPathIsR2 : setup.figure.pathLabelToP .lower = .r2
  pointPAboveCenterline : setup.figure.pointPSide = .upper
  runwayOnCenterline : setup.figure.runwayCenteredOnNodalLine = true
  straightNodalExtension :
    setup.figure.nodalLineExtendsStraightFromRunway = true
  symmetricAntinodalLines : setup.figure.antinodalLinesAreSymmetric = true
  arrowStartsAtRunway : setup.figure.downrangeArrowStartsAtRunway = true
  runwayWidthEqualsSourceSeparation : ∀ unit : LengthUnit,
    lengthReadout unit setup.runwayWidth =
      lengthReadout unit setup.transmitterSeparation
  upperPathShorter :
    lengthInMeters (setup.pathLengthToP .upper) <
      lengthInMeters (setup.pathLengthToP .lower)

/-!
Operational interpretation of the interference pattern: the receiver is
silent on the central node and produces a warning away from that line.
-/
structure MatchesLandingGuidanceDescription
    (setup : RadioLandingInterferenceSetup) : Prop where
  silentOnNodalCenterline :
    setup.receiverResponse .nodalCenterline = .silent
  warningOffCenterline :
    setup.receiverResponse .offCenterline = .warningBeep

/-- Positivity and far-field nondegeneracy of the physical quantities. -/
structure HasPhysicalRadioInterferenceParameters
    (setup : RadioLandingInterferenceSetup) : Prop where
  separationPositive : 0 < lengthInMeters setup.transmitterSeparation
  runwayWidthPositive : 0 < lengthInMeters setup.runwayWidth
  downrangePositive : 0 < lengthInMeters setup.downrangeDistanceToP
  offsetPositive : 0 < lengthInMeters setup.transverseOffsetMagnitude
  pathLengthPositive :
    ∀ source, 0 < lengthInMeters (setup.pathLengthToP source)
  pathDifferencePositive : 0 < lengthInMeters setup.pathDifferenceAtP
  wavelengthPositive :
    ∀ source, 0 < lengthInMeters (setup.transmitterWavelength source)
  frequencyPositive :
    ∀ source, 0 < frequencyInHertz (setup.transmitterFrequency source)
  propagationSpeedPositive :
    0 < speedInMetersPerSecond setup.propagationSpeed
  separationSmallComparedWithDownrange :
    lengthInMeters setup.transmitterSeparation <
      lengthInMeters setup.downrangeDistanceToP

/-!
The physical path-difference magnitude at upper point `P` is `r2 - r1`.
The strict path ordering is recorded by the figure predicate and positivity
conditions, so no absolute-value convention is needed here.
-/
structure SatisfiesPathDifferenceDefinition
    (setup : RadioLandingInterferenceSetup) : Prop where
  pathDifferenceIsR2MinusR1 : ∀ unit : LengthUnit,
    lengthReadout unit setup.pathDifferenceAtP =
      lengthReadout unit (setup.pathLengthToP .lower) -
        lengthReadout unit (setup.pathLengthToP .upper)

/-!
Controlled far-field two-source geometry. In a common length unit, the
leading relation is `delta r * L = d * y`. The named squared-length remainder
is bounded by that leading product times the dimensionless squared transverse
ratios

`(d / (2 L))^2 + (y / L)^2`.

Thus the paraxial relation is local to the stated narrow-angle geometry and
is not asserted as a globally exact identity. Neither the remainder relation
nor its bound mentions the requested wavelength, frequency, or answer choice.
-/
structure SatisfiesControlledFarFieldPathDifferenceModel
    (setup : RadioLandingInterferenceSetup) : Prop where
  usesControlledFarFieldParaxialApproximation :
    setup.approximation = .controlledFarFieldParaxial
  pathDifferenceLawWithRemainder : ∀ unit : LengthUnit,
    ∃ remainderInSquaredUnit : ℝ,
      lengthReadout unit setup.pathDifferenceAtP *
            lengthReadout unit setup.downrangeDistanceToP =
          lengthReadout unit setup.transmitterSeparation *
              lengthReadout unit setup.transverseOffsetMagnitude +
            remainderInSquaredUnit ∧
        |remainderInSquaredUnit| ≤
          |lengthReadout unit setup.transmitterSeparation *
              lengthReadout unit setup.transverseOffsetMagnitude| *
            ((|lengthReadout unit setup.transmitterSeparation| /
                  (2 * |lengthReadout unit setup.downrangeDistanceToP|)) ^ 2 +
              (|lengthReadout unit setup.transverseOffsetMagnitude| /
                  |lengthReadout unit setup.downrangeDistanceToP|) ^ 2)

/-!
Constructive-interference criterion for the out-of-phase pair. With the
chosen orientation, propagation along the extra path cancels the longer-path
source's initial phase advance. Thus maximum order `n` satisfies
`2 pi delta-r / lambda = delta-phi-0 + 2 pi n`. The criterion is quantified
over both symmetric sides, every order, and every length unit; it contains no
answer frequency.
-/
structure SatisfiesOutOfPhaseInterferenceCriterion
    (setup : RadioLandingInterferenceSetup) : Prop where
  maximumIffPhaseCancellation :
    ∀ (side : RunwaySide) (order : ℕ),
      setup.intensityMaximumAtOffset side order ↔
        ∀ unit : LengthUnit,
          2 * Real.pi *
                lengthReadout unit setup.pathDifferenceAtP /
              lengthReadout unit (setup.transmitterWavelength .upper) =
            initialPhaseAdvanceRadians setup + 2 * Real.pi * order

/-!
Nondispersive electromagnetic-wave relation `v = lambda f`, for both
transmitters and every compatible choice of length and time units.
-/
structure SatisfiesRadioWaveSpeedLaw
    (setup : RadioLandingInterferenceSetup) : Prop where
  speedEqualsWavelengthTimesFrequency :
    ∀ (source : TransmitterLabel) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.propagationSpeed =
        lengthReadout lengthUnit (setup.transmitterWavelength source) *
          frequencyReadout timeUnit (setup.transmitterFrequency source)

/-!
Radio propagation through ambient air is approximated by vacuum propagation.
The calibration is Physlib's exact SI speed of light, not the rounded target
frequency and not an answer-choice readout.
-/
structure UsesAmbientAirVacuumPropagation
    (setup : RadioLandingInterferenceSetup) : Prop where
  mediumIsAmbientAir : setup.propagationMedium = .ambientAir
  propagationSpeedIsVacuumSpeed :
    speedInMetersPerSecond setup.propagationSpeed =
      vacuumSpeedOfLightInMetersPerSecond

/-- Labels of the four transmitter-frequency choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in megahertz displayed beside each answer label. -/
def displayedFrequencyMegahertz : AnswerChoice → ℝ
  | .A => 150
  | .B => 100
  | .C => 200
  | .D => 120

/-- Answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
A physical frequency rounds to a displayed whole-megahertz value when it is
strictly within half a megahertz. This accommodates use of Physlib's exact
`299792458 m/s` speed rather than silently replacing it by `3.00e8 m/s`.
-/
def RoundsToNearestMegahertz
    (frequency : FrequencyQuantity) (displayedMegahertz : ℝ) : Prop :=
  |frequencyInMegahertz frequency - displayedMegahertz| < (1 / 2 : ℝ)

/-- Both coherent transmitters agree with the frequency printed for a choice. -/
def MatchesAnswerChoice
    (setup : RadioLandingInterferenceSetup) (choice : AnswerChoice) : Prop :=
  ∀ source,
    RoundsToNearestMegahertz (setup.transmitterFrequency source)
      (displayedFrequencyMegahertz choice)

/-!
The selected answer is unique among the displayed frequencies. This generic
predicate does not build in any particular label or numerical frequency.
-/
def IsUniqueMatchingAnswerChoice
    (setup : RadioLandingInterferenceSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
The controlled far-field model places the path difference close to the
leading value `50 * 60 / 3000 = 1 m`. The out-of-phase first-maximum law then
places the wavelength close to `2 m`; with Physlib's exact vacuum speed of
light, both common transmitter frequencies lie strictly within half a
megahertz of `150 MHz`. No other displayed frequency does, so the uniquely
matching specification is the recorded answer A.

This formalizes `thm:physics:phyx_mini_0247:target`. Neither the rounding
predicate, `150 MHz`, nor choice A occurs in the source/readout, figure,
positivity, controlled-geometry, interference, propagation, or wave-law
assumptions.
-/
theorem problem_phyx_mini_0247
    (setup : RadioLandingInterferenceSetup)
    (hSources : MatchesCoherentRadioSourceDescription setup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hFigure : MatchesSuppliedRadioLandingFigure setup)
    (hGuidance : MatchesLandingGuidanceDescription setup)
    (hPhysical : HasPhysicalRadioInterferenceParameters setup)
    (hPathDifference : SatisfiesPathDifferenceDefinition setup)
    (hFarField : SatisfiesControlledFarFieldPathDifferenceModel setup)
    (hInterference : SatisfiesOutOfPhaseInterferenceCriterion setup)
    (hVacuum : UsesAmbientAirVacuumPropagation setup)
    (hWave : SatisfiesRadioWaveSpeedLaw setup) :
    IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  rcases hFarField.pathDifferenceLawWithRemainder LengthUnit.meters with
    ⟨remainder, hGeometry, hRemainder⟩
  change
    lengthInMeters setup.pathDifferenceAtP *
          lengthInMeters setup.downrangeDistanceToP =
        lengthInMeters setup.transmitterSeparation *
            lengthInMeters setup.transverseOffsetMagnitude +
          remainder
    at hGeometry
  change
    |remainder| ≤
      |lengthInMeters setup.transmitterSeparation *
          lengthInMeters setup.transverseOffsetMagnitude| *
        ((|lengthInMeters setup.transmitterSeparation| /
              (2 * |lengthInMeters setup.downrangeDistanceToP|)) ^ 2 +
          (|lengthInMeters setup.transverseOffsetMagnitude| /
              |lengthInMeters setup.downrangeDistanceToP|) ^ 2)
    at hRemainder
  rw [hReadouts.transmitterSeparationMeters,
    hReadouts.downrangeDistanceMeters, hReadouts.transverseOffsetMeters]
    at hGeometry hRemainder
  norm_num at hGeometry hRemainder
  have hRemainderLower : -(169 / 120 : ℝ) ≤ remainder :=
    (abs_le.mp hRemainder).1
  have hRemainderUpper : remainder ≤ (169 / 120 : ℝ) :=
    (abs_le.mp hRemainder).2
  have hPathDifferenceLower :
      (999 / 1000 : ℝ) < lengthInMeters setup.pathDifferenceAtP := by
    nlinarith [hGeometry, hRemainderLower]
  have hPathDifferenceUpper :
      lengthInMeters setup.pathDifferenceAtP < (1001 / 1000 : ℝ) := by
    nlinarith [hGeometry, hRemainderUpper]

  have hFirstMaximum :=
    (hInterference.maximumIffPhaseCancellation .upper 0).mp
      hReadouts.upperFirstMaximum LengthUnit.meters
  change
    2 * Real.pi * lengthInMeters setup.pathDifferenceAtP /
        lengthInMeters (setup.transmitterWavelength .upper) =
      initialPhaseAdvanceRadians setup + 2 * Real.pi * (0 : ℕ)
    at hFirstMaximum
  rw [hReadouts.initialPhaseAdvance] at hFirstMaximum
  norm_num at hFirstMaximum
  have hWavelengthPositive :
      0 < lengthInMeters (setup.transmitterWavelength .upper) :=
    hPhysical.wavelengthPositive .upper
  have hWavelengthNonzero :
      lengthInMeters (setup.transmitterWavelength .upper) ≠ 0 :=
    ne_of_gt hWavelengthPositive
  field_simp [hWavelengthNonzero] at hFirstMaximum
  have hWavelength :
      lengthInMeters (setup.transmitterWavelength .upper) =
        2 * lengthInMeters setup.pathDifferenceAtP := by
    nlinarith [hFirstMaximum, Real.pi_pos]
  have hWavelengthLower :
      (999 / 500 : ℝ) <
        lengthInMeters (setup.transmitterWavelength .upper) := by
    nlinarith [hPathDifferenceLower, hWavelength]
  have hWavelengthUpper :
      lengthInMeters (setup.transmitterWavelength .upper) <
        (1001 / 500 : ℝ) := by
    nlinarith [hPathDifferenceUpper, hWavelength]

  have hVacuumSpeed :
      vacuumSpeedOfLightInMetersPerSecond = 299792458 := by
    simp [vacuumSpeedOfLightInMetersPerSecond]
  have hWaveUpper :=
    hWave.speedEqualsWavelengthTimesFrequency .upper
      LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.propagationSpeed =
      lengthInMeters (setup.transmitterWavelength .upper) *
        frequencyInHertz (setup.transmitterFrequency .upper)
    at hWaveUpper
  rw [hVacuum.propagationSpeedIsVacuumSpeed, hVacuumSpeed] at hWaveUpper
  have hFrequencyPositive :
      0 < frequencyInHertz (setup.transmitterFrequency .upper) :=
    hPhysical.frequencyPositive .upper
  have hFrequencyLower :
      (149500000 : ℝ) <
        frequencyInHertz (setup.transmitterFrequency .upper) := by
    by_contra h
    have hFrequencyLe :
        frequencyInHertz (setup.transmitterFrequency .upper) ≤
          (149500000 : ℝ) :=
      le_of_not_gt h
    have hProductUpper :=
      mul_lt_mul_of_pos_right hWavelengthUpper hFrequencyPositive
    nlinarith [hWaveUpper, hProductUpper]
  have hFrequencyUpper :
      frequencyInHertz (setup.transmitterFrequency .upper) <
        (150500000 : ℝ) := by
    by_contra h
    have hFrequencyGe :
        (150500000 : ℝ) ≤
          frequencyInHertz (setup.transmitterFrequency .upper) :=
      le_of_not_gt h
    have hProductLower :=
      mul_lt_mul_of_pos_right hWavelengthLower hFrequencyPositive
    nlinarith [hWaveUpper, hProductLower]

  have hFrequencyEq :
      ∀ source,
        setup.transmitterFrequency source =
          setup.transmitterFrequency .upper := by
    intro source
    cases source with
    | upper => rfl
    | lower => exact hSources.commonFrequency.symm
  have hRoundsToA :
      RoundsToNearestMegahertz
        (setup.transmitterFrequency .upper)
        (displayedFrequencyMegahertz .A) := by
    change
      |frequencyInHertz (setup.transmitterFrequency .upper) / 10 ^ 6 - 150| <
        (1 / 2 : ℝ)
    rw [abs_lt]
    constructor <;> norm_num <;> nlinarith

  constructor
  · intro source
    rw [hFrequencyEq source]
    exact hRoundsToA
  · intro other hOther
    cases other with
    | A => rfl
    | B =>
        exfalso
        have hChoice := hOther .upper
        change
          |frequencyInHertz (setup.transmitterFrequency .upper) / 10 ^ 6 -
              100| < (1 / 2 : ℝ)
          at hChoice
        rw [abs_lt] at hChoice
        norm_num at hChoice
        nlinarith [hFrequencyLower]
    | C =>
        exfalso
        have hChoice := hOther .upper
        change
          |frequencyInHertz (setup.transmitterFrequency .upper) / 10 ^ 6 -
              200| < (1 / 2 : ℝ)
          at hChoice
        rw [abs_lt] at hChoice
        norm_num at hChoice
        nlinarith [hFrequencyUpper]
    | D =>
        exfalso
        have hChoice := hOther .upper
        change
          |frequencyInHertz (setup.transmitterFrequency .upper) / 10 ^ 6 -
              120| < (1 / 2 : ℝ)
          at hChoice
        rw [abs_lt] at hChoice
        norm_num at hChoice
        nlinarith [hFrequencyLower]

end PhyXMiniProblems.ProblemPhyXMini0247
