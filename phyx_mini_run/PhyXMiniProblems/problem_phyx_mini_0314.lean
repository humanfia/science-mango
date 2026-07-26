import Mathlib
import Physlib.Units.WithDim.Pressure
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0314

open Dimension

/-!
# Two in-phase speakers and frequency-dependent interference

The primary figure places two vertically separated speakers on the left.  The
listener is horizontally aligned with the lower speaker.  The marked speaker
separation is `d₁ = 2.00 m`, and the lower-speaker-to-listener distance is
`d₂ = 3.75 m`.  Both sources are in phase and have approximately equal sound
pressure amplitudes at the listener.

The physical path lengths, path difference, wavelengths, frequencies, sound
speed, and received sound-pressure amplitudes are unit-independent Physlib
quantities.  Real numbers below occur only as readouts in named units,
dimensionless tolerances and interference orders, or displayed answer data.

For the geometry shown, the paths are `3.75 m` and `4.25 m`, so their
difference is `0.50 m`.  In-phase constructive interference obeys
`Δr = m λ`, while sound propagation obeys `v = λ f`.  Thus the positive
constructive frequencies are `m v / Δr`.  With the conventional calibration
`v = 343 m/s`, the third is `2058 Hz`, not the recorded option D (`1029 Hz`).
-/

/-! ## Dimensionful acoustic quantities and scalar readouts -/

/-- A nonnegative physical length, independent of the selected unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A physical sound-pressure amplitude at the listener. -/
abbrev SoundPressureAmplitude : Type := DimPressure

/-- Read a physical length as a real number in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in the selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout used for the figure geometry and interference condition. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Hertz readout used for the audible band and displayed answers. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of the acoustic propagation speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Pascal readout of a received sound-pressure amplitude. -/
def soundPressureInPascals (amplitude : SoundPressureAmplitude) : ℝ :=
  (amplitude UnitChoices.SI).val

/-! ## Physical apparatus and primary-figure labels -/

/-- The two loudspeakers distinguished by their vertical position. -/
inductive SpeakerLabel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The phase relation stipulated for the two coherent sources. -/
inductive SourcePhaseRelation where
  | inPhase
  | oppositePhase
  deriving DecidableEq, Repr

/-- Which speaker lies on the horizontal line through the listener's ear. -/
inductive ListenerAlignment where
  | directlyInFrontOfLowerSpeaker
  | directlyInFrontOfUpperSpeaker
  | onPerpendicularBisector
  deriving DecidableEq, Repr

/-- Labels attached to the two dimension arrows in the primary bitmap. -/
inductive FigureDistanceLabel where
  | d1SpeakerSeparation
  | d2LowerSpeakerToListener
  deriving DecidableEq, Repr

/-!
All independent physical quantities and qualitative data in the two-speaker
experiment.

`constructiveWavelength order` and `constructiveFrequency order` are indexed
by positive integer path-difference order.  They remain independent physical
quantities until constrained by `SatisfiesTwoSpeakerInterferenceLaws`.
`givesMaximumSignal` is the physical observation being characterized; it is
not defined to make any particular frequency a maximum.
-/
structure TwoSpeakerInterferenceSetup where
  sourcePhaseRelation : SourcePhaseRelation
  listenerAlignment : ListenerAlignment
  figureMarkedDistance : FigureDistanceLabel → LengthQuantity
  speakerSeparationD1 : LengthQuantity
  listenerDistanceD2 : LengthQuantity
  pathLengthToListener : SpeakerLabel → LengthQuantity
  pathDifference : LengthQuantity
  receivedSoundPressureAmplitude : SpeakerLabel → SoundPressureAmplitude
  amplitudeRelativeTolerance : ℝ
  soundSpeed : SpeedQuantity
  constructiveWavelength : ℕ → LengthQuantity
  constructiveFrequency : ℕ → FrequencyQuantity
  audibleLowerFrequency : FrequencyQuantity
  audibleUpperFrequency : FrequencyQuantity
  givesMaximumSignal : FrequencyQuantity → Prop

/-!
The source phrase "approximately the same" has no numerical tolerance.  This
predicate makes the approximation explicit: the Pascal-readout difference is
at most a dimensionless relative tolerance times the larger amplitude.
-/
def ReceivedAmplitudesApproximatelyEqual
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  |soundPressureInPascals
        (setup.receivedSoundPressureAmplitude .upper) -
      soundPressureInPascals
        (setup.receivedSoundPressureAmplitude .lower)| ≤
    setup.amplitudeRelativeTolerance *
      max
        (soundPressureInPascals
          (setup.receivedSoundPressureAmplitude .upper))
        (soundPressureInPascals
          (setup.receivedSoundPressureAmplitude .lower))

/-!
Problem-text and primary-bitmap readouts.  The lower speaker is on the
listener's horizontal line, `d₁ = 2.00 m`, `d₂ = 3.75 m`, the sources are in
phase, their received amplitudes are approximately equal, and the audible
range is `20 Hz` through `20 kHz`.

No path length, path difference, wavelength, constructive frequency, or
answer choice is assigned a derived value here.
-/
structure MatchesProblemStatementAndFigure
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  sourcesAreInPhase : setup.sourcePhaseRelation = .inPhase
  listenerIsInFrontOfLowerSpeaker :
    setup.listenerAlignment = .directlyInFrontOfLowerSpeaker
  d1ArrowRepresentsSpeakerSeparation :
    setup.figureMarkedDistance .d1SpeakerSeparation =
      setup.speakerSeparationD1
  d2ArrowRepresentsLowerSpeakerPath :
    setup.figureMarkedDistance .d2LowerSpeakerToListener =
      setup.listenerDistanceD2
  speakerSeparationMeters :
    lengthInMeters setup.speakerSeparationD1 = 2
  listenerDistanceMeters :
    lengthInMeters setup.listenerDistanceD2 = 15 / 4
  receivedAmplitudesApproximatelyEqual :
    ReceivedAmplitudesApproximatelyEqual setup
  audibleLowerBoundHertz :
    frequencyInHertz setup.audibleLowerFrequency = 20
  audibleUpperBoundHertz :
    frequencyInHertz setup.audibleUpperFrequency = 20000

/-!
Positivity and nondegeneracy of the physical setup.  The final field restricts
the unspecified relative-amplitude tolerance to a genuine fractional error.
These conditions supply no derived numerical frequency.
-/
structure HasPhysicalTwoSpeakerParameters
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  speakerSeparationPositive :
    0 < lengthInMeters setup.speakerSeparationD1
  listenerDistancePositive :
    0 < lengthInMeters setup.listenerDistanceD2
  pathLengthsPositive : ∀ speaker,
    0 < lengthInMeters (setup.pathLengthToListener speaker)
  pathDifferencePositive : 0 < lengthInMeters setup.pathDifference
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed
  constructiveQuantitiesPositive : ∀ order,
    0 < order →
      0 < lengthInMeters (setup.constructiveWavelength order) ∧
        0 < frequencyInHertz (setup.constructiveFrequency order)
  receivedAmplitudesPositive : ∀ speaker,
    0 < soundPressureInPascals
      (setup.receivedSoundPressureAmplitude speaker)
  audibleBoundsOrdered :
    0 < frequencyInHertz setup.audibleLowerFrequency ∧
      frequencyInHertz setup.audibleLowerFrequency <
        frequencyInHertz setup.audibleUpperFrequency
  amplitudeToleranceRange :
    0 ≤ setup.amplitudeRelativeTolerance ∧
      setup.amplitudeRelativeTolerance < 1

/-!
Euclidean path geometry read from the primary figure.

The lower path is the horizontal distance `d₂`; the upper path is the
hypotenuse with legs `d₁` and `d₂`; and the positive path difference is upper
minus lower.  The laws are stated in arbitrary length units and contain none
of the numerical consequences `4.25 m` or `0.50 m`.
-/
structure SatisfiesDepictedSpeakerGeometry
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  lowerPathIsHorizontalDistance : ∀ unit : LengthUnit,
    lengthReadout unit (setup.pathLengthToListener .lower) =
      lengthReadout unit setup.listenerDistanceD2
  upperPathPythagorean : ∀ unit : LengthUnit,
    lengthReadout unit (setup.pathLengthToListener .upper) ^ 2 =
      lengthReadout unit setup.speakerSeparationD1 ^ 2 +
        lengthReadout unit setup.listenerDistanceD2 ^ 2
  pathDifferenceIsUpperMinusLower : ∀ unit : LengthUnit,
    lengthReadout unit setup.pathDifference =
      lengthReadout unit (setup.pathLengthToListener .upper) -
        lengthReadout unit (setup.pathLengthToListener .lower)

/-!
Governing laws for nondispersive sound and two in-phase coherent sources.

For every positive order, `v = λ f` and `Δr = m λ`.  Under the source's
in-phase and approximately-equal-amplitude conditions, a positive frequency
gives maximum signal exactly when it is one of these positive constructive
orders.  This generic criterion neither singles out order three nor states a
numerical answer.
-/
structure SatisfiesTwoSpeakerInterferenceLaws
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  waveSpeedEqualsWavelengthTimesFrequency :
    ∀ (order : ℕ), 0 < order →
      ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
        speedReadout lengthUnit timeUnit setup.soundSpeed =
          lengthReadout lengthUnit (setup.constructiveWavelength order) *
            frequencyReadout timeUnit (setup.constructiveFrequency order)
  constructivePathDifference :
    ∀ (order : ℕ), 0 < order →
      ∀ unit : LengthUnit,
        lengthReadout unit setup.pathDifference =
          (order : ℝ) *
            lengthReadout unit (setup.constructiveWavelength order)
  maximumSignalCriterion :
    setup.sourcePhaseRelation = .inPhase →
      ReceivedAmplitudesApproximatelyEqual setup →
        ∀ frequency : FrequencyQuantity,
          setup.givesMaximumSignal frequency ↔
            ∃ order : ℕ, 0 < order ∧
              frequency = setup.constructiveFrequency order

/-!
The source omits a sound-speed readout.  This separate premise records the
conventional standard-air calibration needed for a numerical frequency.  It
does not mention a wavelength, interference order, target frequency, or
answer choice.
-/
structure HasStandardAirSoundSpeedCalibration
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeed = 343

/-! ## Audible maxima and displayed answers -/

/-- A physical frequency lies in the inclusive normal-hearing range. -/
def IsInAudibleRange
    (setup : TwoSpeakerInterferenceSetup)
    (frequency : FrequencyQuantity) : Prop :=
  frequencyInHertz setup.audibleLowerFrequency ≤
      frequencyInHertz frequency ∧
    frequencyInHertz frequency ≤
      frequencyInHertz setup.audibleUpperFrequency

/-!
`candidate` is the third-lowest audible maximum when it is an audible maximum
and exactly two distinct audible maximum-frequency readouts lie below it.
-/
def IsThirdLowestAudibleMaximum
    (setup : TwoSpeakerInterferenceSetup)
    (candidate : FrequencyQuantity) : Prop :=
  IsInAudibleRange setup candidate ∧
    setup.givesMaximumSignal candidate ∧
    ∃ first second : FrequencyQuantity,
      IsInAudibleRange setup first ∧
        setup.givesMaximumSignal first ∧
        IsInAudibleRange setup second ∧
        setup.givesMaximumSignal second ∧
        frequencyInHertz first < frequencyInHertz second ∧
        frequencyInHertz second < frequencyInHertz candidate ∧
        ∀ other : FrequencyQuantity,
          IsInAudibleRange setup other →
            setup.givesMaximumSignal other →
              frequencyInHertz other < frequencyInHertz candidate →
                frequencyInHertz other = frequencyInHertz first ∨
                  frequencyInHertz other = frequencyInHertz second

/-- The positive constructive order whose frequency is being requested. -/
def thirdConstructiveOrder : ℕ := 3

/-- Naming expansion for the order-three constructive frequency. -/
def thirdConstructiveFrequency
    (setup : TwoSpeakerInterferenceSetup) : FrequencyQuantity :=
  setup.constructiveFrequency thirdConstructiveOrder

/-- Labels of the four answers printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz displayed beside each answer label. -/
def displayedAnswerFrequencyInHertz : AnswerChoice → ℝ
  | .A => 956
  | .B => 986
  | .C => 1015
  | .D => 1029

/-- The answer label recorded by the supplied dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Exact agreement between a physical frequency and a displayed choice. -/
def MatchesAnswerChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  frequencyInHertz frequency = displayedAnswerFrequencyInHertz choice

/-! ## Derived geometry and frequency obligations -/

/-!
The Pythagorean path from the upper speaker has length `17/4 m = 4.25 m`.
-/
lemma upperPathLengthInMeters_eq_seventeenFourths
    (setup : TwoSpeakerInterferenceSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalTwoSpeakerParameters setup)
    (hGeometry : SatisfiesDepictedSpeakerGeometry setup) :
    lengthInMeters (setup.pathLengthToListener .upper) = 17 / 4 := by
  have hUpperSq :=
    hGeometry.upperPathPythagorean LengthUnit.meters
  change lengthInMeters (setup.pathLengthToListener .upper) ^ 2 =
    lengthInMeters setup.speakerSeparationD1 ^ 2 +
      lengthInMeters setup.listenerDistanceD2 ^ 2 at hUpperSq
  rw [hData.speakerSeparationMeters, hData.listenerDistanceMeters] at hUpperSq
  have hUpperPos :=
    hPhysical.pathLengthsPositive SpeakerLabel.upper
  norm_num at hUpperSq ⊢
  nlinarith

/-!
Subtracting the lower path `15/4 m` from the upper path `17/4 m` gives the
figure's physical path difference `1/2 m`.
-/
lemma pathDifferenceInMeters_eq_oneHalf
    (setup : TwoSpeakerInterferenceSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalTwoSpeakerParameters setup)
    (hGeometry : SatisfiesDepictedSpeakerGeometry setup) :
    lengthInMeters setup.pathDifference = 1 / 2 := by
  have hUpper :=
    upperPathLengthInMeters_eq_seventeenFourths
      setup hData hPhysical hGeometry
  have hLower :=
    hGeometry.lowerPathIsHorizontalDistance LengthUnit.meters
  change lengthInMeters (setup.pathLengthToListener .lower) =
    lengthInMeters setup.listenerDistanceD2 at hLower
  have hDiff :=
    hGeometry.pathDifferenceIsUpperMinusLower LengthUnit.meters
  change lengthInMeters setup.pathDifference =
    lengthInMeters (setup.pathLengthToListener .upper) -
      lengthInMeters (setup.pathLengthToListener .lower) at hDiff
  linarith [hUpper, hLower, hData.listenerDistanceMeters]

/-!
At constructive order three, `1/2 = 3 λ`, hence `λ = 1/6 m` and
`f = 6 v`.  This symbolic result does not assume a numerical speed or answer.
-/
lemma thirdConstructiveFrequency_eq_sixTimesSoundSpeed
    (setup : TwoSpeakerInterferenceSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalTwoSpeakerParameters setup)
    (hGeometry : SatisfiesDepictedSpeakerGeometry setup)
    (hInterference : SatisfiesTwoSpeakerInterferenceLaws setup) :
    frequencyInHertz (thirdConstructiveFrequency setup) =
      6 * speedInMetersPerSecond setup.soundSpeed := by
  have hDiff :=
    pathDifferenceInMeters_eq_oneHalf setup hData hPhysical hGeometry
  have hPath :=
    hInterference.constructivePathDifference
      3 (by norm_num) LengthUnit.meters
  change lengthInMeters setup.pathDifference =
    (3 : ℝ) * lengthInMeters (setup.constructiveWavelength 3) at hPath
  have hWavelength :
      lengthInMeters (setup.constructiveWavelength 3) = 1 / 6 := by
    linarith
  have hWave :=
    hInterference.waveSpeedEqualsWavelengthTimesFrequency
      3 (by norm_num) LengthUnit.meters TimeUnit.seconds
  change speedInMetersPerSecond setup.soundSpeed =
    lengthInMeters (setup.constructiveWavelength 3) *
      frequencyInHertz (setup.constructiveFrequency 3) at hWave
  rw [hWavelength] at hWave
  norm_num [thirdConstructiveFrequency, thirdConstructiveOrder] at hWave ⊢
  linarith

/-!
With the explicitly separate standard-air calibration `v = 343 m/s`, the
positive maxima are `686 m Hz`.  Orders one and two are the only audible
maxima below order three, and order three is `2058 Hz`.  None of the four
printed choices—including recorded choice D at `1029 Hz`—matches it.

This formalizes `thm:physics:phyx_mini_0314:target` while exposing the
inconsistency between the stated in-phase maximum problem and its answer data.
-/
theorem problem_phyx_mini_0314
    (setup : TwoSpeakerInterferenceSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalTwoSpeakerParameters setup)
    (hGeometry : SatisfiesDepictedSpeakerGeometry setup)
    (hInterference : SatisfiesTwoSpeakerInterferenceLaws setup)
    (hAir : HasStandardAirSoundSpeedCalibration setup) :
    frequencyInHertz (thirdConstructiveFrequency setup) = 2058 ∧
      IsThirdLowestAudibleMaximum setup
        (thirdConstructiveFrequency setup) ∧
      ∀ choice : AnswerChoice,
        ¬ MatchesAnswerChoice (thirdConstructiveFrequency setup) choice := by
  have hDiff :=
    pathDifferenceInMeters_eq_oneHalf setup hData hPhysical hGeometry
  have hFrequencyFormula : ∀ order : ℕ, 0 < order →
      frequencyInHertz (setup.constructiveFrequency order) =
        686 * (order : ℝ) := by
    intro order hOrder
    have hOrderReal : (0 : ℝ) < (order : ℝ) := by
      exact_mod_cast hOrder
    have hOrderNe : (order : ℝ) ≠ 0 := ne_of_gt hOrderReal
    have hPath :=
      hInterference.constructivePathDifference
        order hOrder LengthUnit.meters
    change lengthInMeters setup.pathDifference =
      (order : ℝ) *
        lengthInMeters (setup.constructiveWavelength order) at hPath
    have hWavelength :
        lengthInMeters (setup.constructiveWavelength order) =
          (1 / 2 : ℝ) / (order : ℝ) := by
      apply (eq_div_iff hOrderNe).2
      nlinarith [hDiff, hPath]
    have hWave :=
      hInterference.waveSpeedEqualsWavelengthTimesFrequency
        order hOrder LengthUnit.meters TimeUnit.seconds
    change speedInMetersPerSecond setup.soundSpeed =
      lengthInMeters (setup.constructiveWavelength order) *
        frequencyInHertz (setup.constructiveFrequency order) at hWave
    rw [hAir.soundSpeedMetersPerSecond, hWavelength] at hWave
    field_simp [hOrderNe] at hWave
    nlinarith
  have hFreq1 := hFrequencyFormula 1 (by norm_num)
  have hFreq2 := hFrequencyFormula 2 (by norm_num)
  have hFreq3 := hFrequencyFormula 3 (by norm_num)
  norm_num at hFreq1 hFreq2 hFreq3
  have hThird :
      frequencyInHertz (thirdConstructiveFrequency setup) = 2058 := by
    simpa [thirdConstructiveFrequency, thirdConstructiveOrder] using hFreq3
  have hMaximumCriterion :=
    hInterference.maximumSignalCriterion
      hData.sourcesAreInPhase hData.receivedAmplitudesApproximatelyEqual
  refine ⟨hThird, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · unfold IsInAudibleRange
      rw [hData.audibleLowerBoundHertz,
        hData.audibleUpperBoundHertz, hThird]
      norm_num
    · apply (hMaximumCriterion _).mpr
      refine ⟨3, by norm_num, ?_⟩
      simp [thirdConstructiveFrequency, thirdConstructiveOrder]
    · refine ⟨setup.constructiveFrequency 1,
        setup.constructiveFrequency 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold IsInAudibleRange
        rw [hData.audibleLowerBoundHertz,
          hData.audibleUpperBoundHertz, hFreq1]
        norm_num
      · apply (hMaximumCriterion _).mpr
        exact ⟨1, by norm_num, rfl⟩
      · unfold IsInAudibleRange
        rw [hData.audibleLowerBoundHertz,
          hData.audibleUpperBoundHertz, hFreq2]
        norm_num
      · apply (hMaximumCriterion _).mpr
        exact ⟨2, by norm_num, rfl⟩
      · rw [hFreq1, hFreq2]
        norm_num
      · rw [hFreq2, hThird]
        norm_num
      · intro other hOtherAudible hOtherMaximum hOtherBelow
        obtain ⟨order, hOrder, rfl⟩ :=
          (hMaximumCriterion other).mp hOtherMaximum
        have hOrderFrequency := hFrequencyFormula order hOrder
        rw [hOrderFrequency, hThird] at hOtherBelow
        have hOrderLtThree : order < 3 := by
          exact_mod_cast
            (show (order : ℝ) < 3 by nlinarith [hOtherBelow])
        have hOrderCases : order = 1 ∨ order = 2 := by
          omega
        rcases hOrderCases with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
  · intro choice
    cases choice <;>
      norm_num [MatchesAnswerChoice,
        displayedAnswerFrequencyInHertz, hThird]

end PhyXMiniProblems.ProblemPhyXMini0314
