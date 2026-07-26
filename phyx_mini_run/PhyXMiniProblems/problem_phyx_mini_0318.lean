import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0318

open Dimension

/-!
# Second in-band resonance of an open cylindrical pipe

The primary figure labels the loudspeaker `S` and the nearby cylindrical pipe
`D`.  The speaker is driven by an audio oscillator swept from `1000 Hz` to
`2000 Hz`.  Pipe `D` is open at both ends, has length `45.7 cm`, and contains
air in which sound travels at `344 m/s`.

Physical lengths, frequencies, and speeds are represented by unit-independent
Physlib quantities.  Real numbers occur only as explicitly named unit readouts,
mode indices coerced to scalars, and displayed whole-hertz answer values.  The
mode frequencies are independent fields of the setup and are constrained by a
general open-open-pipe resonance law; the requested second in-band frequency
is not assigned in the setup.  The resulting frequency is approximately
`1505.470 Hz`, so it rounds to `1505 Hz`.  None of the supplied choices displays
that value; the recorded dataset answer `D = 1506 Hz` is retained only as
source metadata.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative cyclic frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length as a real number in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Centimeter readout used for the stated pipe length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Meter readout used in the SI resonance calculation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of the speed of sound. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Figure labels and physical apparatus -/

/-- The two literal labels printed in the primary figure. -/
inductive FigureLabel where
  | S
  | D
  deriving DecidableEq, Repr

/-- Physical roles of the two drawn objects. -/
inductive ApparatusKind where
  | smallLoudspeaker
  | cylindricalPipe
  deriving DecidableEq, Repr

/-- The kind of oscillator driving loudspeaker `S`. -/
inductive SourceDriveKind where
  | variableFrequencyAudioOscillator
  | fixedFrequencySource
  deriving DecidableEq, Repr

/-- The material through which the longitudinal sound wave propagates. -/
inductive AcousticMedium where
  | air
  | otherGas
  deriving DecidableEq, Repr

/-- The two axial ends of pipe `D`. -/
inductive PipeEnd where
  | nearSpeaker
  | farFromSpeaker
  deriving DecidableEq, Repr

/-- Acoustic boundary behavior at an end of the pipe. -/
inductive AcousticBoundaryCondition where
  | openEnd
  | closedEnd
  deriving DecidableEq, Repr

/-- Qualitative relative placement visible in the supplied bitmap. -/
inductive SourcePipePlacement where
  | speakerFacingNearbyPipeEnd
  | notFacingPipe
  deriving DecidableEq, Repr

/-!
The physical setup.  `modeFrequency n` is the frequency assigned to harmonic
index `n`; only positive indices represent physical modes.  `isResonant` is an
independent physical predicate, later characterized by the governing laws.
-/
structure OpenPipeResonanceSetup where
  apparatusAtLabel : FigureLabel → ApparatusKind
  sourceDrive : SourceDriveKind
  sourcePipePlacement : SourcePipePlacement
  medium : AcousticMedium
  boundaryCondition : PipeEnd → AcousticBoundaryCondition
  pipeLength : LengthQuantity
  soundSpeed : SpeedQuantity
  sweepLowerFrequency : FrequencyQuantity
  sweepUpperFrequency : FrequencyQuantity
  modeFrequency : ℕ → FrequencyQuantity
  isResonant : FrequencyQuantity → Prop

/-!
Data read from the problem statement and primary figure.  The exact decimal
`45.7 cm` is represented by `457 / 10`, while the source sweep and sound speed
are recorded in their stated SI-derived units.  No mode index, resonant
frequency, or answer choice appears here.
-/
structure MatchesSuppliedOpenPipeProblem
    (setup : OpenPipeResonanceSetup) : Prop where
  labelSIsSpeaker : setup.apparatusAtLabel .S = .smallLoudspeaker
  labelDIsPipe : setup.apparatusAtLabel .D = .cylindricalPipe
  driveIsVariableAudioOscillator :
    setup.sourceDrive = .variableFrequencyAudioOscillator
  speakerFacesNearbyPipeEnd :
    setup.sourcePipePlacement = .speakerFacingNearbyPipeEnd
  pipeIsAirFilled : setup.medium = .air
  nearEndIsOpen : setup.boundaryCondition .nearSpeaker = .openEnd
  farEndIsOpen : setup.boundaryCondition .farFromSpeaker = .openEnd
  pipeLengthCentimeters :
    lengthInCentimeters setup.pipeLength = 457 / 10
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeed = 344
  sweepLowerHertz : frequencyInHertz setup.sweepLowerFrequency = 1000
  sweepUpperHertz : frequencyInHertz setup.sweepUpperFrequency = 2000

/-- Positivity and nondegeneracy conditions for the modeled apparatus. -/
structure HasPhysicalOpenPipeParameters
    (setup : OpenPipeResonanceSetup) : Prop where
  pipeLengthPositive : 0 < lengthInMeters setup.pipeLength
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed
  sweepLowerPositive : 0 < frequencyInHertz setup.sweepLowerFrequency
  sweepBoundsOrdered :
    frequencyInHertz setup.sweepLowerFrequency <
      frequencyInHertz setup.sweepUpperFrequency
  positiveModeFrequency :
    ∀ n : ℕ, 0 < n → 0 < frequencyInHertz (setup.modeFrequency n)

/-!
## Governing acoustic laws

For a pipe open at both ends, the positive resonant modes fit `n`
half-wavelengths into the doubled pipe length.  Combining this geometry with
`v = f lambda` gives the dimensionally compatible scalar identity

`2 * L * f_n = n * v`.

The second field states that these positive integer modes exhaust the physical
resonances.  Both statements describe the entire open-pipe spectrum; neither
selects the requested second resonance in the oscillator sweep.
-/
structure SatisfiesOpenOpenPipeResonanceLaws
    (setup : OpenPipeResonanceSetup) : Prop where
  harmonicBalance :
    ∀ (n : ℕ), 0 < n →
      ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
        2 * lengthReadout lengthUnit setup.pipeLength *
            frequencyReadout timeUnit (setup.modeFrequency n) =
          (n : ℝ) *
            speedReadout lengthUnit timeUnit setup.soundSpeed
  resonancesExactlyPositiveModes :
    ∀ frequency : FrequencyQuantity,
      setup.isResonant frequency ↔
        ∃ n : ℕ, 0 < n ∧ frequency = setup.modeFrequency n

/-! ## Sweep ordering and answer interpretation -/

/-- A physical frequency lies in the oscillator's inclusive sweep interval. -/
def IsInOscillatorSweep
    (setup : OpenPipeResonanceSetup) (frequency : FrequencyQuantity) : Prop :=
  frequencyInHertz setup.sweepLowerFrequency ≤ frequencyInHertz frequency ∧
    frequencyInHertz frequency ≤ frequencyInHertz setup.sweepUpperFrequency

/-- A physical resonance that can be reached during the stated sweep. -/
def IsResonanceInOscillatorSweep
    (setup : OpenPipeResonanceSetup) (frequency : FrequencyQuantity) : Prop :=
  setup.isResonant frequency ∧ IsInOscillatorSweep setup frequency

/-!
`frequency` is the second-lowest in-sweep resonance when it is resonant and
there is an in-sweep resonance below it such that every in-sweep resonance
below it has that same hertz readout.  This definition is generic: it contains
neither mode `4` nor any of the numerical answer values.
-/
def IsSecondLowestResonanceInSweep
    (setup : OpenPipeResonanceSetup) (frequency : FrequencyQuantity) : Prop :=
  IsResonanceInOscillatorSweep setup frequency ∧
    ∃ firstFrequency : FrequencyQuantity,
      IsResonanceInOscillatorSweep setup firstFrequency ∧
        frequencyInHertz firstFrequency < frequencyInHertz frequency ∧
        ∀ otherFrequency : FrequencyQuantity,
          IsResonanceInOscillatorSweep setup otherFrequency →
            frequencyInHertz otherFrequency < frequencyInHertz frequency →
            frequencyInHertz otherFrequency =
              frequencyInHertz firstFrequency

/-- Labels of the four frequency choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole-hertz number displayed beside each answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 1424
  | .B => 1468
  | .C => 1488
  | .D => 1506

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A physical frequency rounds to a displayed whole-hertz value. -/
def RoundsToWholeHertz
    (frequency : FrequencyQuantity) (wholeHertz : ℝ) : Prop :=
  |frequencyInHertz frequency - wholeHertz| < 1 / 2

/-- A displayed choice is the whole-hertz rounding of a physical frequency. -/
def AgreesWithDisplayedFrequencyChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToWholeHertz frequency choice.hertz

/-!
Converting the stated `45.7 cm` pipe length to meters gives `457/1000 m`.
This helper uses only the figure/problem readout and unit conversion, not a
resonance conclusion.
-/
lemma pipeLengthInMeters_eq_457_div_1000
    (setup : OpenPipeResonanceSetup)
    (h_problem : MatchesSuppliedOpenPipeProblem setup) :
    lengthInMeters setup.pipeLength = 457 / 1000 := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value : WithDim L𝓭 NNReal => (value.val : ℝ))
      (length.2
        ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
        ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices))
    change lengthInCentimeters length = _ at h
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.scale,
      LengthUnit.div_eq_val, LengthUnit.meters, NNReal.smul_def] at h ⊢
    exact h
  have h_length := h_problem.pipeLengthCentimeters
  rw [length_centimeters_eq] at h_length
  norm_num at h_length ⊢
  linarith

/-!
The general open-open harmonic law specialized to the fourth mode gives the
exact unrounded physical frequency `688000/457 Hz`.
-/
lemma fourthMode_frequencyInHertz
    (setup : OpenPipeResonanceSetup)
    (h_problem : MatchesSuppliedOpenPipeProblem setup)
    (h_physical : HasPhysicalOpenPipeParameters setup)
    (h_laws : SatisfiesOpenOpenPipeResonanceLaws setup) :
    frequencyInHertz (setup.modeFrequency 4) = 688000 / 457 := by
  have h_length :=
    pipeLengthInMeters_eq_457_div_1000 setup h_problem
  have h_balance :=
    h_laws.harmonicBalance 4 (by norm_num)
      LengthUnit.meters TimeUnit.seconds
  change
    2 * lengthInMeters setup.pipeLength *
        frequencyInHertz (setup.modeFrequency 4) =
      (4 : ℝ) * speedInMetersPerSecond setup.soundSpeed at h_balance
  have h_coefficient_ne :
      2 * lengthInMeters setup.pipeLength ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt h_physical.pipeLengthPositive)
  apply mul_left_cancel₀ h_coefficient_ne
  calc
    (2 * lengthInMeters setup.pipeLength) *
          frequencyInHertz (setup.modeFrequency 4) =
        (4 : ℝ) * speedInMetersPerSecond setup.soundSpeed := h_balance
    _ = (2 * lengthInMeters setup.pipeLength) * (688000 / 457) := by
      rw [h_length, h_problem.soundSpeedMetersPerSecond]
      norm_num

/-!
The positive open-open harmonics have spacing approximately `376.37 Hz`.
Within the inclusive `1000--2000 Hz` sweep, modes `3`, `4`, and `5` occur in
that order.  Thus mode `4`, whose exact value is `688000/457 Hz`, is the
second-lowest in-band resonance.  Its value is approximately `1505.470 Hz`,
which rounds to `1505 Hz`, not to the recorded choice `D = 1506 Hz`; in fact,
none of the four displayed choices agrees under nearest-whole-hertz rounding.

This formalizes `thm:physics:phyx_mini_0318:target`.
-/
theorem problem_phyx_mini_0318
    (setup : OpenPipeResonanceSetup)
    (h_problem : MatchesSuppliedOpenPipeProblem setup)
    (h_physical : HasPhysicalOpenPipeParameters setup)
    (h_laws : SatisfiesOpenOpenPipeResonanceLaws setup) :
    frequencyInHertz (setup.modeFrequency 4) = 688000 / 457 ∧
      IsSecondLowestResonanceInSweep setup (setup.modeFrequency 4) ∧
      RoundsToWholeHertz (setup.modeFrequency 4) 1505 ∧
      ¬ AgreesWithDisplayedFrequencyChoice
        (setup.modeFrequency 4) recordedDatasetAnswer ∧
      ¬ ∃ choice : AnswerChoice,
        AgreesWithDisplayedFrequencyChoice (setup.modeFrequency 4) choice := by
  have h_length :=
    pipeLengthInMeters_eq_457_div_1000 setup h_problem
  have h_mode_frequency (n : ℕ) (hn : 0 < n) :
      frequencyInHertz (setup.modeFrequency n) =
        (n : ℝ) * 172000 / 457 := by
    have h_balance :=
      h_laws.harmonicBalance n hn LengthUnit.meters TimeUnit.seconds
    change
      2 * lengthInMeters setup.pipeLength *
          frequencyInHertz (setup.modeFrequency n) =
        (n : ℝ) * speedInMetersPerSecond setup.soundSpeed at h_balance
    rw [h_length, h_problem.soundSpeedMetersPerSecond] at h_balance
    norm_num at h_balance ⊢
    linarith
  have h_mode3 := h_mode_frequency 3 (by norm_num)
  have h_mode4 :=
    fourthMode_frequencyInHertz setup h_problem h_physical h_laws
  have h_resonant3 : setup.isResonant (setup.modeFrequency 3) :=
    (h_laws.resonancesExactlyPositiveModes (setup.modeFrequency 3)).2
      ⟨3, by norm_num, rfl⟩
  have h_resonant4 : setup.isResonant (setup.modeFrequency 4) :=
    (h_laws.resonancesExactlyPositiveModes (setup.modeFrequency 4)).2
      ⟨4, by norm_num, rfl⟩
  have h_in_sweep3 :
      IsResonanceInOscillatorSweep setup (setup.modeFrequency 3) := by
    refine ⟨h_resonant3, ?_, ?_⟩
    · rw [h_problem.sweepLowerHertz, h_mode3]
      norm_num
    · rw [h_problem.sweepUpperHertz, h_mode3]
      norm_num
  have h_in_sweep4 :
      IsResonanceInOscillatorSweep setup (setup.modeFrequency 4) := by
    refine ⟨h_resonant4, ?_, ?_⟩
    · rw [h_problem.sweepLowerHertz, h_mode4]
      norm_num
    · rw [h_problem.sweepUpperHertz, h_mode4]
      norm_num
  refine ⟨h_mode4, ?_, ?_, ?_, ?_⟩
  · refine ⟨h_in_sweep4, setup.modeFrequency 3, h_in_sweep3, ?_, ?_⟩
    · rw [h_mode3, h_mode4]
      norm_num
    · intro otherFrequency h_other h_below
      rcases
          (h_laws.resonancesExactlyPositiveModes otherFrequency).1 h_other.1 with
        ⟨n, hn, rfl⟩
      have h_lower := h_other.2.1
      rw [h_problem.sweepLowerHertz, h_mode_frequency n hn] at h_lower
      rw [h_mode_frequency n hn, h_mode4] at h_below
      have hn_ge : 3 ≤ n := by
        by_contra h_not
        have hn_le : n ≤ 2 := by omega
        have h_cast : (n : ℝ) ≤ 2 := by exact_mod_cast hn_le
        nlinarith
      have hn_le : n ≤ 3 := by
        by_contra h_not
        have hn_ge_four : 4 ≤ n := by omega
        have h_cast : (4 : ℝ) ≤ n := by exact_mod_cast hn_ge_four
        norm_num at h_below
        nlinarith
      have hn_eq : n = 3 := by omega
      subst n
      rfl
  · rw [RoundsToWholeHertz, h_mode4]
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  · intro h_agree
    rw [AgreesWithDisplayedFrequencyChoice, recordedDatasetAnswer,
      AnswerChoice.hertz, RoundsToWholeHertz, h_mode4] at h_agree
    rw [abs_of_nonpos (by norm_num)] at h_agree
    norm_num at h_agree
  · rintro ⟨choice, h_choice⟩
    cases choice <;>
      norm_num [AgreesWithDisplayedFrequencyChoice, RoundsToWholeHertz,
        AnswerChoice.hertz, h_mode4, abs_of_nonneg, abs_of_nonpos] at h_choice

end PhyXMiniProblems.ProblemPhyXMini0318
