import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0177

open Dimension

/-!
# Frequency of the fifth harmonic on a fixed string

The primary image shows a standing wave on a `2.0 m` string fixed at both
ends. There are five loops (five antinodes) and six nodes when the two fixed
endpoints are included. The propagation speed along the tightened string is
`40 m/s`.

Lengths, frequency, and speed below are genuine dimensionful Physlib
quantities. Real numbers are used only for readouts in named units and for
the values printed beside the multiple-choice labels. In particular, neither
the setup nor either governing-law interface assumes the requested `50 Hz`
conclusion.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical wave-propagation speed. -/
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

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- The two endpoints visible against the gray supports in the figure. -/
inductive StringEndpoint where
  | left
  | right
  deriving DecidableEq, Repr

/-- Boundary condition specified at either endpoint of the string. -/
inductive EndpointBoundaryCondition where
  | fixed
  deriving DecidableEq, Repr

/-- Mechanical state of the string described in the problem. -/
inductive StringMechanicalState where
  | tightened
  deriving DecidableEq, Repr

/-- Kind of transverse wave depicted by the blue curves. -/
inductive TransverseWaveKind where
  | standing
  deriving DecidableEq, Repr

/-!
Discrete information read from the supplied standing-wave diagram. Nodes
include both endpoints. An antinode count is equivalently the number of
loops of a fixed-fixed normal mode.
-/
structure StandingWaveFigure where
  showsEndpoint : StringEndpoint → Bool
  showsEquilibriumAxis : Bool
  nodeCountIncludingEndpoints : ℕ
  antinodeCount : ℕ

/-!
The physical string and the particular normal mode shown in the problem.
The wavelength and oscillation frequency are unknown dimensionful quantities;
they are constrained only by the governing-law hypotheses below.
-/
structure FixedStringStandingWaveSetup where
  stringLength : LengthQuantity
  propagationSpeed : SpeedQuantity
  wavelength : LengthQuantity
  oscillationFrequency : FrequencyQuantity
  harmonicIndex : ℕ
  endpointBoundary : StringEndpoint → EndpointBoundaryCondition
  mechanicalState : StringMechanicalState
  waveKind : TransverseWaveKind
  figure : StandingWaveFigure

/-!
Qualitative information from the prose: the string is tightened, the wave is
standing, and both ends are fixed. This predicate contains no wavelength or
frequency value.
-/
def MatchesFixedStringScenario
    (setup : FixedStringStandingWaveSetup) : Prop :=
  setup.mechanicalState = .tightened ∧
    setup.waveKind = .standing ∧
    ∀ endpoint, setup.endpointBoundary endpoint = .fixed

/-!
Numerical quantities stated in the prose. They are read in SI units but
remain stored as unit-independent physical quantities.
-/
def MatchesProblemReadouts
    (setup : FixedStringStandingWaveSetup) : Prop :=
  lengthInMeters setup.stringLength = 2 ∧
    speedInMetersPerSecond setup.propagationSpeed = 40

/-!
Primary-image evidence: both supported endpoints and the equilibrium axis are
shown, and the blue pattern has five loops and six nodes including the ends.
No frequency or wavelength readout is present in the bitmap.
-/
def MatchesSuppliedStandingWaveFigure
    (setup : FixedStringStandingWaveSetup) : Prop :=
  (∀ endpoint, setup.figure.showsEndpoint endpoint = true) ∧
    setup.figure.showsEquilibriumAxis = true ∧
    setup.figure.nodeCountIncludingEndpoints = 6 ∧
    setup.figure.antinodeCount = 5

/-- Positivity and nondegeneracy conditions for the physical normal mode. -/
def HasPhysicalStandingWaveParameters
    (setup : FixedStringStandingWaveSetup) : Prop :=
  0 < lengthInMeters setup.stringLength ∧
    0 < speedInMetersPerSecond setup.propagationSpeed ∧
    0 < lengthInMeters setup.wavelength ∧
    0 < frequencyInHertz setup.oscillationFrequency ∧
    0 < setup.harmonicIndex

/-!
For a string fixed at both ends, normal mode `n` contains `n` antinodes and
`n + 1` nodes, while its length contains `n` half-wavelengths. The last
equation is stated in every length unit and does not single out the pictured
mode or its numerical wavelength.
-/
structure SatisfiesFixedEndStandingWaveModeLaw
    (setup : FixedStringStandingWaveSetup) : Prop where
  harmonicIndexEqualsAntinodeCount :
    setup.harmonicIndex = setup.figure.antinodeCount
  nodeCountEqualsHarmonicIndexPlusOne :
    setup.figure.nodeCountIncludingEndpoints = setup.harmonicIndex + 1
  twiceLengthEqualsHarmonicWavelength :
    ∀ unit : LengthUnit,
      2 * lengthReadout unit setup.stringLength =
        (setup.harmonicIndex : ℝ) * lengthReadout unit setup.wavelength

/-!
The nondispersive wave relation `v = lambda f`, expressed in every compatible
choice of length and time units. It is a general governing law, not the
requested numerical frequency.
-/
structure SatisfiesStringWaveSpeedLaw
    (setup : FixedStringStandingWaveSetup) : Prop where
  speedEqualsWavelengthTimesFrequency :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.propagationSpeed =
        lengthReadout lengthUnit setup.wavelength *
          frequencyReadout timeUnit setup.oscillationFrequency

/-- Labels of the four frequency choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Hertz value displayed beside each answer label. -/
def displayedFrequencyInHertz : AnswerChoice → ℝ
  | .A => 25
  | .B => 100
  | .C => 20
  | .D => 50

/-- Answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A choice matches the physical frequency exactly when its Hertz readout does. -/
def IsExactFrequencyChoice
    (setup : FixedStringStandingWaveSetup) (choice : AnswerChoice) : Prop :=
  frequencyInHertz setup.oscillationFrequency =
    displayedFrequencyInHertz choice

/-!
The five loops in the supplied image identify the fifth fixed-fixed normal
mode. This is a consequence of figure evidence and the general mode-count
law, rather than a field initialized to the answer.
-/
lemma harmonicIndex_eq_five
    (setup : FixedStringStandingWaveSetup)
    (h_figure : MatchesSuppliedStandingWaveFigure setup)
    (h_mode : SatisfiesFixedEndStandingWaveModeLaw setup) :
    setup.harmonicIndex = 5 := by
  calc
    setup.harmonicIndex = setup.figure.antinodeCount :=
      h_mode.harmonicIndexEqualsAntinodeCount
    _ = 5 := h_figure.2.2.2

/-!
For a two-meter string in its fifth mode, the fixed-end wavelength relation
gives `lambda = 4/5 m`.
-/
lemma wavelength_in_meters_eq_four_fifths
    (setup : FixedStringStandingWaveSetup)
    (h_scenario : MatchesFixedStringScenario setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedStandingWaveFigure setup)
    (h_physical : HasPhysicalStandingWaveParameters setup)
    (h_mode : SatisfiesFixedEndStandingWaveModeLaw setup) :
    lengthInMeters setup.wavelength = 4 / 5 := by
  have h_mode_meters :=
    h_mode.twiceLengthEqualsHarmonicWavelength LengthUnit.meters
  change
    2 * lengthInMeters setup.stringLength =
      (setup.harmonicIndex : ℝ) * lengthInMeters setup.wavelength
    at h_mode_meters
  rw [h_readouts.1, harmonicIndex_eq_five setup h_figure h_mode] at h_mode_meters
  norm_num at h_mode_meters ⊢
  linarith

/-!
Combining the derived `4/5 m` wavelength with the stated `40 m/s` speed in
`v = lambda f` yields the exact frequency `50 Hz`.
-/
lemma frequency_in_hertz_eq_fifty
    (setup : FixedStringStandingWaveSetup)
    (h_scenario : MatchesFixedStringScenario setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedStandingWaveFigure setup)
    (h_physical : HasPhysicalStandingWaveParameters setup)
    (h_mode : SatisfiesFixedEndStandingWaveModeLaw setup)
    (h_wave : SatisfiesStringWaveSpeedLaw setup) :
    frequencyInHertz setup.oscillationFrequency = 50 := by
  have h_wave_si :=
    h_wave.speedEqualsWavelengthTimesFrequency
      LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.propagationSpeed =
      lengthInMeters setup.wavelength *
        frequencyInHertz setup.oscillationFrequency
    at h_wave_si
  rw [h_readouts.2,
    wavelength_in_meters_eq_four_fifths setup h_scenario h_readouts h_figure
      h_physical h_mode] at h_wave_si
  norm_num at h_wave_si ⊢
  linarith

/-!
The pictured five-loop mode therefore has frequency `50 Hz`, which is the
value displayed by choice D and agrees with the dataset's recorded label.

This formalizes `thm:physics:phyx_mini_0177:target`.
-/
theorem problem_phyx_mini_0177
    (setup : FixedStringStandingWaveSetup)
    (h_scenario : MatchesFixedStringScenario setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedStandingWaveFigure setup)
    (h_physical : HasPhysicalStandingWaveParameters setup)
    (h_mode : SatisfiesFixedEndStandingWaveModeLaw setup)
    (h_wave : SatisfiesStringWaveSpeedLaw setup) :
    frequencyInHertz setup.oscillationFrequency = 50 ∧
      IsExactFrequencyChoice setup .D ∧
      IsExactFrequencyChoice setup recordedDatasetAnswer := by
  have h_frequency :=
    frequency_in_hertz_eq_fifty setup h_scenario h_readouts h_figure
      h_physical h_mode h_wave
  exact ⟨h_frequency,
    by simpa [IsExactFrequencyChoice, displayedFrequencyInHertz] using h_frequency,
    by
      simpa [IsExactFrequencyChoice, recordedDatasetAnswer,
        displayedFrequencyInHertz] using h_frequency⟩

end PhyXMiniProblems.ProblemPhyXMini0177
