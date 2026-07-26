import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# One-loop standing wave on a string loaded over a pulley

This file models problem `phyx_mini_0204`. A small-amplitude mechanical
oscillator drives the horizontal part of a string. The string passes over a
pulley and supports a hanging mass. The requested operating state has one
standing-wave loop between the oscillator and the pulley.

All physical magnitudes are represented by unit-independent Physlib
`Dimensionful` quantities. Real numbers below are only coherent SI readouts,
dimensionless loop counts, and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0204

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A physical mass per unit length. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A physical propagation speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A physical force, used for the two string-tension magnitudes. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a dimension-tagged nonnegative physical quantity in chosen units. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout UnitChoices.SI length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  quantityReadout UnitChoices.SI frequency

/-- Kilograms-per-metre readout of a linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout UnitChoices.SI speed

/-- Newton readout of a force in coherent SI base units. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  quantityReadout UnitChoices.SI force

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantityReadout UnitChoices.SI acceleration

/-! ## Apparatus, primary-figure labels, and requested mode -/

/-- Individually visible components of the supplied apparatus figure. -/
inductive FigureComponent where
  | oscillator
  | horizontalString
  | pulley
  | verticalString
  | hangingMassM
  deriving DecidableEq, Repr

/-- The two ends of the horizontally vibrating string span. -/
inductive HorizontalSpanEndpoint where
  | oscillatorEnd
  | pulleyContact
  deriving DecidableEq, Repr

/-- The route of the string visible in the primary figure. -/
inductive StringRoute where
  | horizontalToPulleyThenVerticallyDown
  deriving DecidableEq, Repr

/-- The stated operating regime of the oscillator. -/
inductive OscillatorRegime where
  | smallAmplitudeMechanical
  deriving DecidableEq, Repr

/--
The physical quantities and categorical data of the oscillator--string--pulley
apparatus. `loopCount`, wavelength, speed, both tensions, and hanging mass are
unknown state variables; this structure assigns none of them the requested
answer value.
-/
structure StringPulleySetup where
  figureShows : FigureComponent → Prop
  stringRoute : StringRoute
  oscillatorRegime : OscillatorRegime
  nodeAt : HorizontalSpanEndpoint → Prop
  /-- Frequency of the mechanical driving oscillator. -/
  oscillatorFrequency : FrequencyQuantity
  /-- Mass per unit length of the uniform string. -/
  stringLinearMassDensity : LinearMassDensityQuantity
  /-- Labelled horizontal distance `ℓ` from oscillator to pulley. -/
  horizontalSpanLength : LengthQuantity
  /-- Wavelength of the standing transverse wave on the horizontal span. -/
  wavelength : LengthQuantity
  /-- Transverse wave speed on the taut horizontal string. -/
  transverseWaveSpeed : SpeedQuantity
  /-- Tension acting on the horizontal vibrating span. -/
  horizontalTension : ForceQuantity
  /-- Tension acting on the vertical segment above the suspended mass. -/
  verticalTension : ForceQuantity
  /-- Suspended mass labelled `m` in the figure. -/
  hangingMass : MassQuantity
  /-- Local gravitational acceleration magnitude. -/
  gravitationalAcceleration : AccelerationQuantity
  /-- Number of half-wavelength loops on the horizontal span. -/
  loopCount : ℕ

/--
The categorical and numerical data printed in the problem and primary figure:
a small-amplitude mechanical oscillator, the shown string route, `60.0 Hz`,
`3.5 × 10⁻⁴ kg/m`, and the labelled `1.50 m` horizontal span.

No wavelength, speed, tension, loop count, or hanging-mass value occurs here.
-/
def MatchesProblemAndPrimaryFigure (setup : StringPulleySetup) : Prop :=
  setup.figureShows .oscillator ∧
    setup.figureShows .horizontalString ∧
    setup.figureShows .pulley ∧
    setup.figureShows .verticalString ∧
    setup.figureShows .hangingMassM ∧
    setup.stringRoute = .horizontalToPulleyThenVerticallyDown ∧
    setup.oscillatorRegime = .smallAmplitudeMechanical ∧
    frequencyInHertz setup.oscillatorFrequency = 60 ∧
    linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity =
      7 / 20000 ∧
    lengthInMeters setup.horizontalSpanLength = 3 / 2

/--
Boundary-node idealization for the vibrating horizontal span. The oscillator
node is explicitly stipulated in the source; the pulley contact constrains the
other end of the idealized node-to-node span.
-/
def HasNodeBoundaryConditions (setup : StringPulleySetup) : Prop :=
  setup.nodeAt .oscillatorEnd ∧ setup.nodeAt .pulleyContact

/-- The operating state requested by the question: exactly one loop. -/
def IsRequestedOneLoopState (setup : StringPulleySetup) : Prop :=
  setup.loopCount = 1

/--
The standard classroom calibration `g = 9.8 m/s²`. It is auxiliary physical
data, kept separate from the values printed in the source and figure.
-/
def UsesStandardGravity (setup : StringPulleySetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 49 / 5

/-- Positivity conditions for a taut string carrying a nonzero load. -/
def HasPositivePhysicalParameters (setup : StringPulleySetup) : Prop :=
  0 < frequencyInHertz setup.oscillatorFrequency ∧
    0 < linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity ∧
    0 < lengthInMeters setup.horizontalSpanLength ∧
    0 < lengthInMeters setup.wavelength ∧
    0 < speedInMetersPerSecond setup.transverseWaveSpeed ∧
    0 < forceInNewtons setup.horizontalTension ∧
    0 < forceInNewtons setup.verticalTension ∧
    0 < massInKilograms setup.hangingMass ∧
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration ∧
    0 < setup.loopCount

/-! ## Governing standing-wave and mechanical laws -/

/--
Node-to-node standing-wave geometry: a mode with `n` loops satisfies
`n λ = 2 ℓ`. This is stated generically in the loop count rather than baking
the requested one-loop answer into the law.
-/
structure SatisfiesNodeToNodeStandingWaveLaw
    (setup : StringPulleySetup) : Prop where
  loop_geometry :
    HasNodeBoundaryConditions setup →
      (setup.loopCount : ℝ) * lengthInMeters setup.wavelength =
        2 * lengthInMeters setup.horizontalSpanLength

/-- The nondispersive wave relation `v = f λ` on the horizontal string. -/
structure SatisfiesWaveSpeedLaw (setup : StringPulleySetup) : Prop where
  wave_speed :
    speedInMetersPerSecond setup.transverseWaveSpeed =
      frequencyInHertz setup.oscillatorFrequency *
        lengthInMeters setup.wavelength

/--
The transverse-wave law for a uniform taut string, written as
`T = μ v²` in coherent SI readouts.
-/
structure SatisfiesTautStringTensionLaw (setup : StringPulleySetup) : Prop where
  horizontal_tension :
    forceInNewtons setup.horizontalTension =
      linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity *
        speedInMetersPerSecond setup.transverseWaveSpeed ^ 2

/--
Ideal frictionless-pulley transmission together with static force balance of
the suspended mass: the horizontal and vertical tensions agree and the latter
equals the weight `m g`.
-/
structure SatisfiesIdealPulleyAndStaticLoadLaw
    (setup : StringPulleySetup) : Prop where
  pulley_transmits_tension :
    forceInNewtons setup.horizontalTension =
      forceInNewtons setup.verticalTension
  hanging_mass_balance :
    forceInNewtons setup.verticalTension =
      massInKilograms setup.hangingMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-! ## Derived mass and displayed answer -/

/--
The governing laws give the unrounded suspended mass `81/70 kg`, approximately
`1.157 kg`, before comparison with the displayed one-decimal choices.
-/
lemma hangingMassInKilograms_eq_exact
    (setup : StringPulleySetup)
    (h_problem : MatchesProblemAndPrimaryFigure setup)
    (h_nodes : HasNodeBoundaryConditions setup)
    (h_oneLoop : IsRequestedOneLoopState setup)
    (h_gravity : UsesStandardGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_standingWave : SatisfiesNodeToNodeStandingWaveLaw setup)
    (h_waveSpeed : SatisfiesWaveSpeedLaw setup)
    (h_stringTension : SatisfiesTautStringTensionLaw setup)
    (h_pulley : SatisfiesIdealPulleyAndStaticLoadLaw setup) :
    massInKilograms setup.hangingMass = 81 / 70 := by
  rcases h_problem with
    ⟨_, _, _, _, _, _, _, h_frequency, h_density, h_length⟩
  have h_wavelength := h_standingWave.loop_geometry h_nodes
  have h_speed := h_waveSpeed.wave_speed
  have h_horizontal_tension := h_stringTension.horizontal_tension
  have h_transmitted := h_pulley.pulley_transmits_tension
  have h_balance := h_pulley.hanging_mass_balance
  change setup.loopCount = 1 at h_oneLoop
  change accelerationInMetersPerSecondSquared
    setup.gravitationalAcceleration = 49 / 5 at h_gravity
  norm_num [h_oneLoop, h_length] at h_wavelength
  norm_num [h_frequency, h_wavelength] at h_speed
  norm_num [h_density, h_speed] at h_horizontal_tension
  norm_num [h_gravity] at h_balance
  linarith

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Mass in kilograms printed beside each answer label. -/
def AnswerChoice.kilograms : AnswerChoice → ℝ
  | .A => 9 / 5
  | .B => 8 / 5
  | .C => 7 / 5
  | .D => 6 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Agreement with a displayed one-decimal kilogram answer. A `0.05 kg` tolerance
models rounding to the nearest tenth rather than identifying the exact physical
mass with the printed decimal.
-/
def MatchesAnswerChoice (mass : MassQuantity) (choice : AnswerChoice) : Prop :=
  |massInKilograms mass - choice.kilograms| ≤ 1 / 20

/--
Under the problem data, one-loop boundary condition, string-wave laws, and
ideal pulley equilibrium, the required hanging mass agrees with recorded
answer D (`1.2 kg`) to the displayed precision.

This formalizes `thm:physics:phyx_mini_0204:target`.
-/
theorem hangingMass_matches_recordedAnswerD
    (setup : StringPulleySetup)
    (h_problem : MatchesProblemAndPrimaryFigure setup)
    (h_nodes : HasNodeBoundaryConditions setup)
    (h_oneLoop : IsRequestedOneLoopState setup)
    (h_gravity : UsesStandardGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_standingWave : SatisfiesNodeToNodeStandingWaveLaw setup)
    (h_waveSpeed : SatisfiesWaveSpeedLaw setup)
    (h_stringTension : SatisfiesTautStringTensionLaw setup)
    (h_pulley : SatisfiesIdealPulleyAndStaticLoadLaw setup) :
    MatchesAnswerChoice setup.hangingMass recordedAnswerChoice := by
  unfold MatchesAnswerChoice
  rw [hangingMassInKilograms_eq_exact setup h_problem h_nodes h_oneLoop
    h_gravity h_positive h_standingWave h_waveSpeed h_stringTension h_pulley]
  norm_num [recordedAnswerChoice, AnswerChoice.kilograms, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0204
