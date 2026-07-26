import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0296

open Dimension

/-!
# Transverse velocity in a sinusoidal standing wave

A transverse standing wave on a long string has an antinode at `x = 0` and
the adjacent node at `x = 0.10 m`.  The primary figure plots the displacement
of the particle at the antinode against time.  Its vertical scale is
`y_s = 4.0 cm`; the curve starts at equilibrium while descending, reaches a
trough at `0.5 s`, crosses equilibrium while rising at `1.0 s`, reaches a
crest at `1.5 s`, and returns to equilibrium at `2.0 s`.

The dimensional quantities below use Physlib's unit-independent
`Dimensionful` type.  Real scalars occur only as named-unit readouts,
dimensionless phases in radians, and displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and coherent unit readouts -/

/-- A nonnegative transverse-displacement amplitude. -/
abbrev AmplitudeQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative standing wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial coordinate or transverse displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed time coordinate relative to the graph origin. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative duration, used here for the oscillation period. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Angular frequency, with radians treated as dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Wave number, with radians treated as dimensionless. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A signed transverse-velocity component. -/
abbrev TransverseVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a nonnegative length in the selected length unit. -/
def nonnegativeLengthReadout
    (unit : LengthUnit)
    (length : Dimensionful (WithDim L𝓭 NNReal)) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed axial coordinate or displacement in the selected unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a signed time coordinate in the selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := unit}).val

/-- Read a nonnegative duration in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read wave number in radians per selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read transverse velocity in coherent selected length/time units. -/
def transverseVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : TransverseVelocityQuantity) : ℝ :=
  (velocity
    {UnitChoices.SI with length := lengthUnit, time := timeUnit}).val

/-! ## Standing-wave roles and primary-figure labels -/

/-- The kind of disturbance described in the problem. -/
inductive StringWaveKind where
  | transverseStanding
  deriving DecidableEq, Repr

/-- Distinguished axial locations named in the statement or query. -/
inductive SpatialLandmark where
  | graphAntinode
  | adjacentNode
  | requestedPoint
  deriving DecidableEq, Repr

/-- Standing-wave displacement roles attached to axial landmarks. -/
inductive StandingWaveRole where
  | antinode
  | node
  | notSpecified
  deriving DecidableEq, Repr

/-- The two axes of the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity printed beside each graph axis. -/
inductive AxisQuantity where
  | time_t
  | transverseDisplacement_y
  deriving DecidableEq, Repr

/-- Distinguished points of the plotted temporal sinusoid. -/
inductive DisplacementGraphLandmark where
  | originZero
  | firstTrough
  | middleZero
  | firstCrest
  | closingZero
  deriving DecidableEq, Repr

/-!
Labels, units, and marked time coordinates supplied by the primary graph.
The numerical readings are stated in `MatchesPrimaryDisplacementGraph`, not
built into this structure.
-/
structure DisplacementTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  horizontalTimeUnit : TimeUnit
  verticalLengthUnit : LengthUnit
  horizontalAxisShowsUnit : Bool
  verticalAxisShowsUnit : Bool
  verticalScaleYs : AmplitudeQuantity
  observationPosition : SignedLengthQuantity
  horizontalGridIntervalCount : ℕ
  sinusoidalCurveVisible : Bool
  landmarkTime : DisplacementGraphLandmark → TimeQuantity

/-!
Independent physical quantities and observables for the standing wave.
Displacement and transverse velocity remain separate dimensionful fields;
the governing-law premise below relates them to the wave parameters.
-/
structure StandingStringWaveSetup where
  waveKind : StringWaveKind
  graph : DisplacementTimeGraph
  spatialPosition : SpatialLandmark → SignedLengthQuantity
  spatialRole : SpatialLandmark → StandingWaveRole
  amplitudeYm : AmplitudeQuantity
  wavelength : WavelengthQuantity
  period : DurationQuantity
  waveNumber : WaveNumberQuantity
  angularFrequency : AngularFrequencyQuantity
  phaseOffsetRadians : ℝ
  requestedTime : TimeQuantity
  transverseDisplacement :
    SignedLengthQuantity → TimeQuantity → SignedLengthQuantity
  transverseVelocity :
    SignedLengthQuantity → TimeQuantity → TransverseVelocityQuantity

/-!
Problem-statement geometry and query data.  The graph observes the antinode
at `x = 0`; its adjacent node is at `0.10 m`; the requested event is
`x = 0.20 m`, `t = 1.0 s`.  No requested transverse-velocity value occurs in
these premises.
-/
structure MatchesStandingWaveProblemData
    (setup : StandingStringWaveSetup) : Prop where
  waveIsTransverseStanding : setup.waveKind = .transverseStanding
  graphLandmarkIsAntinode :
    setup.spatialRole .graphAntinode = .antinode
  adjacentLandmarkIsNode :
    setup.spatialRole .adjacentNode = .node
  graphObservesNamedAntinode :
    setup.graph.observationPosition =
      setup.spatialPosition .graphAntinode
  antinodeCoordinateMeters :
    signedLengthReadout LengthUnit.meters
      (setup.spatialPosition .graphAntinode) = 0
  adjacentNodeCoordinateMeters :
    signedLengthReadout LengthUnit.meters
      (setup.spatialPosition .adjacentNode) = 1 / 10
  requestedPositionMeters :
    signedLengthReadout LengthUnit.meters
      (setup.spatialPosition .requestedPoint) = 1 / 5
  requestedTimeSeconds :
    timeReadout TimeUnit.seconds setup.requestedTime = 1

/-!
Calibrated evidence from the supplied bitmap.  Four equal horizontal grid
intervals run from `0 s` to `2.0 s`.  The curve passes successively through
zero, `-y_s`, zero, `+y_s`, and zero, where `y_s = 4.0 cm`.  The slope signs
record the visible direction of motion without supplying the queried
velocity at `x = 0.20 m`.
-/
structure MatchesPrimaryDisplacementGraph
    (setup : StandingStringWaveSetup) : Prop where
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .transverseDisplacement_y
  horizontalUnitIsSeconds :
    setup.graph.horizontalTimeUnit = TimeUnit.seconds
  verticalUnitIsCentimeters :
    setup.graph.verticalLengthUnit = LengthUnit.centimeters
  horizontalUnitPrinted : setup.graph.horizontalAxisShowsUnit = true
  verticalUnitPrinted : setup.graph.verticalAxisShowsUnit = true
  sinusoidalCurveShown : setup.graph.sinusoidalCurveVisible = true
  fourHorizontalGridIntervals : setup.graph.horizontalGridIntervalCount = 4
  scaleYsCentimeters :
    nonnegativeLengthReadout LengthUnit.centimeters
      setup.graph.verticalScaleYs = 4
  amplitudeTouchesScale :
    nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm =
      nonnegativeLengthReadout LengthUnit.centimeters
        setup.graph.verticalScaleYs
  originTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .originZero) = 0
  troughTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .firstTrough) = 1 / 2
  middleZeroTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .middleZero) = 1
  crestTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .firstCrest) = 3 / 2
  closingZeroTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .closingZero) = 2
  requestedTimeIsMiddleZero :
    setup.requestedTime = setup.graph.landmarkTime .middleZero
  periodSeconds : durationReadout TimeUnit.seconds setup.period = 2
  displacementAtOriginZero :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.graph.observationPosition
          (setup.graph.landmarkTime .originZero)) = 0
  displacementAtFirstTrough :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.graph.observationPosition
          (setup.graph.landmarkTime .firstTrough)) =
      -(nonnegativeLengthReadout LengthUnit.centimeters
        setup.graph.verticalScaleYs)
  displacementAtMiddleZero :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.graph.observationPosition
          (setup.graph.landmarkTime .middleZero)) = 0
  displacementAtFirstCrest :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.graph.observationPosition
          (setup.graph.landmarkTime .firstCrest)) =
      nonnegativeLengthReadout LengthUnit.centimeters
        setup.graph.verticalScaleYs
  displacementAtClosingZero :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.graph.observationPosition
          (setup.graph.landmarkTime .closingZero)) = 0
  curveDescendsAtOrigin :
    transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
        (setup.transverseVelocity setup.graph.observationPosition
          (setup.graph.landmarkTime .originZero)) < 0
  curveRisesAtMiddleZero :
    0 < transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
      (setup.transverseVelocity setup.graph.observationPosition
        (setup.graph.landmarkTime .middleZero))

/-!
Positivity and a principal representative for phase.  The phase range does
not determine the phase; the graph and governing laws select it.
-/
structure HasPhysicalStandingWaveParameters
    (setup : StandingStringWaveSetup) : Prop where
  amplitudePositive :
    0 < nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm
  wavelengthPositive :
    0 < nonnegativeLengthReadout LengthUnit.meters setup.wavelength
  periodPositive : 0 < durationReadout TimeUnit.seconds setup.period
  waveNumberPositive :
    0 < waveNumberReadout LengthUnit.meters setup.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyReadout TimeUnit.seconds setup.angularFrequency
  phaseNonnegative : 0 ≤ setup.phaseOffsetRadians
  phaseBelowFullTurn : setup.phaseOffsetRadians < 2 * Real.pi

/-!
Generic laws for a sinusoidal standing wave with an antinode chosen as the
spatial origin of phase:

* `k lambda = 2 pi` and `omega T = 2 pi`;
* the distance from an antinode to its adjacent node is `lambda / 4`;
* `y(x,t) = y_m cos(k (x-x_A)) sin(omega t + phi)`;
* transverse particle velocity is the corresponding time derivative.

All equations use coherent named-unit readouts.  The velocity equation is
the dimensionful observable form of Mathlib's scalar sine chain rule.  None
of these laws mentions the requested event or any displayed answer value.
-/
structure SatisfiesSinusoidalStandingWaveLaws
    (setup : StandingStringWaveSetup) : Prop where
  waveNumberWavelengthRelation :
    ∀ unit : LengthUnit,
      waveNumberReadout unit setup.waveNumber *
          nonnegativeLengthReadout unit setup.wavelength =
        2 * Real.pi
  angularFrequencyPeriodRelation :
    ∀ unit : TimeUnit,
      angularFrequencyReadout unit setup.angularFrequency *
          durationReadout unit setup.period =
        2 * Real.pi
  adjacentNodeIsQuarterWavelength :
    ∀ unit : LengthUnit,
      4 *
          (signedLengthReadout unit
              (setup.spatialPosition .adjacentNode) -
            signedLengthReadout unit
              (setup.spatialPosition .graphAntinode)) =
        nonnegativeLengthReadout unit setup.wavelength
  sinusoidalDisplacementLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (position : SignedLengthQuantity) (time : TimeQuantity),
      signedLengthReadout lengthUnit
          (setup.transverseDisplacement position time) =
        nonnegativeLengthReadout lengthUnit setup.amplitudeYm *
          Real.cos
            (waveNumberReadout lengthUnit setup.waveNumber *
              (signedLengthReadout lengthUnit position -
                signedLengthReadout lengthUnit
                  (setup.spatialPosition .graphAntinode))) *
          Real.sin
            (angularFrequencyReadout timeUnit setup.angularFrequency *
                timeReadout timeUnit time +
              setup.phaseOffsetRadians)
  transverseVelocityLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (position : SignedLengthQuantity) (time : TimeQuantity),
      transverseVelocityReadout lengthUnit timeUnit
          (setup.transverseVelocity position time) =
        nonnegativeLengthReadout lengthUnit setup.amplitudeYm *
          angularFrequencyReadout timeUnit setup.angularFrequency *
          Real.cos
            (waveNumberReadout lengthUnit setup.waveNumber *
              (signedLengthReadout lengthUnit position -
                signedLengthReadout lengthUnit
                  (setup.spatialPosition .graphAntinode))) *
          Real.cos
            (angularFrequencyReadout timeUnit setup.angularFrequency *
                timeReadout timeUnit time +
              setup.phaseOffsetRadians)

/-! ## Derived parameters and displayed answers -/

/-- Labels of the four transverse-velocity choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed transverse velocity in metres per second. -/
def displayedVelocityInMetersPerSecond : AnswerChoice → ℝ
  | .A => 3 / 25
  | .B => -1 / 20
  | .C => -9 / 50
  | .D => -13 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a velocity displayed to the nearest `0.01 m/s`. -/
def MatchesDisplayedVelocity
    (velocityMetersPerSecond : ℝ) (choice : AnswerChoice) : Prop :=
  |velocityMetersPerSecond -
      displayedVelocityInMetersPerSecond choice| < 1 / 200

/-- The adjacent-node spacing gives a standing wavelength of `0.40 m`. -/
lemma wavelengthInMeters_eq_two_fifths
    (setup : StandingStringWaveSetup)
    (_data : MatchesStandingWaveProblemData setup)
    (_laws : SatisfiesSinusoidalStandingWaveLaws setup) :
    nonnegativeLengthReadout LengthUnit.meters setup.wavelength =
      2 / 5 := by
  have h :=
    _laws.adjacentNodeIsQuarterWavelength LengthUnit.meters
  rw [_data.adjacentNodeCoordinateMeters,
    _data.antinodeCoordinateMeters] at h
  norm_num at h ⊢
  exact h.symm

/-- The `0.40 m` wavelength gives `k = 5 pi rad/m`. -/
lemma waveNumberInRadiansPerMeter_eq_five_pi
    (setup : StandingStringWaveSetup)
    (_data : MatchesStandingWaveProblemData setup)
    (_laws : SatisfiesSinusoidalStandingWaveLaws setup) :
    waveNumberReadout LengthUnit.meters setup.waveNumber =
      5 * Real.pi := by
  have h :=
    _laws.waveNumberWavelengthRelation LengthUnit.meters
  rw [wavelengthInMeters_eq_two_fifths setup _data _laws] at h
  norm_num at h ⊢
  linarith

/-- The graph period `2.0 s` gives `omega = pi rad/s`. -/
lemma angularFrequencyInRadiansPerSecond_eq_pi
    (setup : StandingStringWaveSetup)
    (_figure : MatchesPrimaryDisplacementGraph setup)
    (_laws : SatisfiesSinusoidalStandingWaveLaws setup) :
    angularFrequencyReadout TimeUnit.seconds setup.angularFrequency =
      Real.pi := by
  have h :=
    _laws.angularFrequencyPeriodRelation TimeUnit.seconds
  rw [_figure.periodSeconds] at h
  linarith

/-!
At the graph origin the antinode displacement is zero and decreasing.  With
the principal sine-phase representative, this selects `phi = pi`.
-/
lemma phaseOffsetRadians_eq_pi
    (setup : StandingStringWaveSetup)
    (_data : MatchesStandingWaveProblemData setup)
    (_figure : MatchesPrimaryDisplacementGraph setup)
    (_physical : HasPhysicalStandingWaveParameters setup)
    (_laws : SatisfiesSinusoidalStandingWaveLaws setup) :
    setup.phaseOffsetRadians = Real.pi := by
  have hdisplacement :=
    _laws.sinusoidalDisplacementLaw
      LengthUnit.centimeters TimeUnit.seconds
      setup.graph.observationPosition
      (setup.graph.landmarkTime .originZero)
  rw [_figure.displacementAtOriginZero,
    _data.graphObservesNamedAntinode,
    _figure.originTimeSeconds] at hdisplacement
  simp only [sub_self, mul_zero, Real.cos_zero, mul_one, zero_add] at hdisplacement
  have hsin : Real.sin setup.phaseOffsetRadians = 0 :=
    (mul_eq_zero.mp hdisplacement.symm).resolve_left
      _physical.amplitudePositive.ne'
  have hvelocity :=
    _laws.transverseVelocityLaw
      LengthUnit.centimeters TimeUnit.seconds
      setup.graph.observationPosition
      (setup.graph.landmarkTime .originZero)
  rw [_data.graphObservesNamedAntinode,
    _figure.originTimeSeconds] at hvelocity
  simp only [sub_self, mul_zero, Real.cos_zero, mul_one, zero_add] at hvelocity
  have hvelocityNegative := _figure.curveDescendsAtOrigin
  rw [_data.graphObservesNamedAntinode] at hvelocityNegative
  rw [hvelocity] at hvelocityNegative
  have hamplitudeFrequencyPositive :
      0 <
        nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm *
          angularFrequencyReadout TimeUnit.seconds
            setup.angularFrequency :=
    mul_pos _physical.amplitudePositive
      _physical.angularFrequencyPositive
  have hcosNegative : Real.cos setup.phaseOffsetRadians < 0 :=
    neg_of_mul_neg_right hvelocityNegative
      hamplitudeFrequencyPositive.le
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hnNonnegativeReal : (0 : ℝ) ≤ n := by
    rw [← mul_nonneg_iff_of_pos_right Real.pi_pos, hn]
    exact _physical.phaseNonnegative
  have hnBelowTwoReal : (n : ℝ) < 2 := by
    have hMultiple :
        (n : ℝ) * Real.pi < 2 * Real.pi := by
      rw [hn]
      exact _physical.phaseBelowFullTurn
    exact lt_of_mul_lt_mul_right hMultiple Real.pi_nonneg
  have hnNonnegative : (0 : ℤ) ≤ n := by
    exact_mod_cast hnNonnegativeReal
  have hnBelowTwo : n < (2 : ℤ) := by
    exact_mod_cast hnBelowTwoReal
  have hnNonzero : n ≠ 0 := by
    intro hnZero
    subst n
    norm_num at hn
    rw [← hn] at hcosNegative
    norm_num at hcosNegative
  have hnOne : n = 1 := by omega
  rw [hnOne] at hn
  norm_num at hn
  exact hn.symm

/-!
The requested point is twice the antinode-to-adjacent-node distance, so its
spatial standing-wave phase relative to the graph antinode is `pi`.
-/
lemma requestedPointSpatialPhase_eq_pi
    (setup : StandingStringWaveSetup)
    (_data : MatchesStandingWaveProblemData setup)
    (_laws : SatisfiesSinusoidalStandingWaveLaws setup) :
    waveNumberReadout LengthUnit.meters setup.waveNumber *
        (signedLengthReadout LengthUnit.meters
            (setup.spatialPosition .requestedPoint) -
          signedLengthReadout LengthUnit.meters
            (setup.spatialPosition .graphAntinode)) =
      Real.pi := by
  rw [waveNumberInRadiansPerMeter_eq_five_pi setup _data _laws,
    _data.requestedPositionMeters,
    _data.antinodeCoordinateMeters]
  ring

/-!
At `x = 0.20 m`, the standing-wave spatial factor is the negative of that at
`x = 0`.  At `t = 1.0 s` the exact model velocity is therefore
`-0.04 pi m/s = -pi/25 m/s`.
-/
lemma transverseVelocityAtRequestedEvent_exact
    (setup : StandingStringWaveSetup)
    (_data : MatchesStandingWaveProblemData setup)
    (_figure : MatchesPrimaryDisplacementGraph setup)
    (_physical : HasPhysicalStandingWaveParameters setup)
    (_laws : SatisfiesSinusoidalStandingWaveLaws setup) :
    transverseVelocityReadout LengthUnit.meters TimeUnit.seconds
        (setup.transverseVelocity
          (setup.spatialPosition .requestedPoint) setup.requestedTime) =
      -(Real.pi / 25) := by
  have hAmplitudeCentimeters :
      nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm = 4 := by
    calc
      nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm =
          nonnegativeLengthReadout LengthUnit.centimeters
            setup.graph.verticalScaleYs :=
        _figure.amplitudeTouchesScale
      _ = 4 := _figure.scaleYsCentimeters
  have hAmplitudeConversion :
      nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm =
        100 *
          nonnegativeLengthReadout LengthUnit.meters setup.amplitudeYm := by
    have hUnits := setup.amplitudeYm.2
      UnitChoices.SI
      ({UnitChoices.SI with
        length := LengthUnit.centimeters} : UnitChoices)
    have hUnitsReal := congrArg
      (fun reading : WithDim L𝓭 NNReal => (reading.val : ℝ)) hUnits
    norm_num [nonnegativeLengthReadout, UnitChoices.dimScale,
      LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val] at hUnitsReal ⊢
    exact hUnitsReal
  have hAmplitudeMeters :
      nonnegativeLengthReadout LengthUnit.meters setup.amplitudeYm =
        1 / 25 := by
    rw [hAmplitudeConversion] at hAmplitudeCentimeters
    norm_num at hAmplitudeCentimeters ⊢
    linarith
  have hvelocity :=
    _laws.transverseVelocityLaw
      LengthUnit.meters TimeUnit.seconds
      (setup.spatialPosition .requestedPoint) setup.requestedTime
  rw [hAmplitudeMeters,
    angularFrequencyInRadiansPerSecond_eq_pi setup _figure _laws,
    requestedPointSpatialPhase_eq_pi setup _data _laws,
    _data.requestedTimeSeconds,
    phaseOffsetRadians_eq_pi setup _data _figure _physical _laws] at hvelocity
  norm_num [← two_mul] at hvelocity ⊢
  rw [hvelocity]
  ring

/-!
The exact transverse velocity `-pi/25 m/s` is approximately
`-0.1257 m/s`.  It rounds to `-0.13 m/s`, choice D, and is at least as close
to D as to every other displayed choice.

This formalizes `thm:physics:phyx_mini_0296:target`.
-/
theorem problem_phyx_mini_0296
    (setup : StandingStringWaveSetup)
    (_data : MatchesStandingWaveProblemData setup)
    (_figure : MatchesPrimaryDisplacementGraph setup)
    (_physical : HasPhysicalStandingWaveParameters setup)
    (_laws : SatisfiesSinusoidalStandingWaveLaws setup) :
    transverseVelocityReadout LengthUnit.meters TimeUnit.seconds
        (setup.transverseVelocity
          (setup.spatialPosition .requestedPoint) setup.requestedTime) =
        -(Real.pi / 25) ∧
      MatchesDisplayedVelocity
        (transverseVelocityReadout LengthUnit.meters TimeUnit.seconds
          (setup.transverseVelocity
            (setup.spatialPosition .requestedPoint) setup.requestedTime))
        recordedDatasetAnswer ∧
      ∀ choice : AnswerChoice,
        |transverseVelocityReadout LengthUnit.meters TimeUnit.seconds
              (setup.transverseVelocity
                (setup.spatialPosition .requestedPoint) setup.requestedTime) -
            displayedVelocityInMetersPerSecond recordedDatasetAnswer| ≤
          |transverseVelocityReadout LengthUnit.meters TimeUnit.seconds
              (setup.transverseVelocity
                (setup.spatialPosition .requestedPoint) setup.requestedTime) -
            displayedVelocityInMetersPerSecond choice| := by
  have hvelocity :=
    transverseVelocityAtRequestedEvent_exact
      setup _data _figure _physical _laws
  have hpiLower : (25 / 8 : ℝ) < Real.pi := by
    have hbaseBound :=
      Real.cos_bound
        (x := (25 / 256 : ℝ))
        (show |(25 / 256 : ℝ)| ≤ 1 by norm_num)
    have hbaseLower :
        (622 / 625 : ℝ) < Real.cos (25 / 256) := by
      have hlower := (abs_le.mp hbaseBound).1
      norm_num at hlower ⊢
      nlinarith
    have hdoubleLower :
        (24521 / 25000 : ℝ) < Real.cos (25 / 128) := by
      rw [show (25 / 128 : ℝ) = 2 * (25 / 256) by norm_num,
        Real.cos_two_mul]
      nlinarith
    have hquadrupleLower :
        (9239 / 10000 : ℝ) < Real.cos (25 / 64) := by
      rw [show (25 / 64 : ℝ) = 2 * (25 / 128) by norm_num,
        Real.cos_two_mul]
      nlinarith
    have hoctupleLower :
        (70711 / 100000 : ℝ) < Real.cos (25 / 32) := by
      rw [show (25 / 32 : ℝ) = 2 * (25 / 64) by norm_num,
        Real.cos_two_mul]
      nlinarith
    have hsixteenfoldPositive :
        0 < Real.cos (25 / 16) := by
      rw [show (25 / 16 : ℝ) = 2 * (25 / 32) by norm_num,
        Real.cos_two_mul]
      nlinarith
    by_contra hpi
    have hpiUpper : Real.pi ≤ (25 / 8 : ℝ) := le_of_not_gt hpi
    have hcosNonpositive : Real.cos (25 / 16) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le
        (by linarith)
        (by nlinarith [Real.two_le_pi])
    linarith
  have hpiUpper : Real.pi < (27 / 8 : ℝ) := by
    have hbaseBound :=
      Real.cos_bound
        (x := (27 / 256 : ℝ))
        (show |(27 / 256 : ℝ)| ≤ 1 by norm_num)
    have hbaseUpper :
        Real.cos (27 / 256) < (1989 / 2000 : ℝ) := by
      have hupper := (abs_le.mp hbaseBound).2
      norm_num at hupper ⊢
      nlinarith
    have hbasePositive : 0 < Real.cos (27 / 256) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hdoubleUpper :
        Real.cos (27 / 128) < (9781 / 10000 : ℝ) := by
      rw [show (27 / 128 : ℝ) = 2 * (27 / 256) by norm_num,
        Real.cos_two_mul]
      nlinarith
    have hdoublePositive : 0 < Real.cos (27 / 128) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hquadrupleUpper :
        Real.cos (27 / 64) < (4567 / 5000 : ℝ) := by
      rw [show (27 / 64 : ℝ) = 2 * (27 / 128) by norm_num,
        Real.cos_two_mul]
      nlinarith
    have hquadruplePositive : 0 < Real.cos (27 / 64) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hoctupleUpper :
        Real.cos (27 / 32) < (3343 / 5000 : ℝ) := by
      rw [show (27 / 32 : ℝ) = 2 * (27 / 64) by norm_num,
        Real.cos_two_mul]
      nlinarith
    have hoctuplePositive : 0 < Real.cos (27 / 32) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hsixteenfoldNegative :
        Real.cos (27 / 16) < 0 := by
      rw [show (27 / 16 : ℝ) = 2 * (27 / 32) by norm_num,
        Real.cos_two_mul]
      nlinarith
    by_contra hpi
    have hpiLower : (27 / 8 : ℝ) ≤ Real.pi := le_of_not_gt hpi
    have hcosNonnegative : 0 ≤ Real.cos (27 / 16) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos])
        (by linarith)
    linarith
  refine ⟨hvelocity, ?_, ?_⟩
  · rw [hvelocity]
    change |-(Real.pi / 25) - (-13 / 100 : ℝ)| < 1 / 200
    rw [abs_lt]
    constructor <;> nlinarith
  · intro choice
    rw [hvelocity]
    apply
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    cases choice <;>
      norm_num [recordedDatasetAnswer,
        displayedVelocityInMetersPerSecond] <;>
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0296
