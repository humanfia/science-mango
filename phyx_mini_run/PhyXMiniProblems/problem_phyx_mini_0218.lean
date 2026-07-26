import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0218

open Dimension

/-!
# Position of the first fret of a guitar

The primary figure labels the bridge-to-nut string length by `ℓ = 75.0 cm`
and the nut-to-first-fret distance by `x`.  Pressing the string at that fret
changes the vibrating segment from bridge-to-nut to bridge-to-first-fret.
The tension and linear mass density remain unchanged, while the fundamental
frequency rises by one equal-tempered semitone.

Lengths, frequencies, tensions, and linear mass densities below are Physlib
dimensionful quantities.  Real numbers are used only for explicitly named SI
or centimetre readouts, dimensionless frequency ratios, and displayed answer
values.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- A nonnegative physical length, used for `ℓ`, `x`, and vibrating lengths. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative ordinary frequency, with inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative string tension, carrying the physical dimension of force. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative mass per unit length of guitar string. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- Metre readout of a physical length in coherent SI units. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout derived from the coherent SI metre readout. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Newton readout of a physical string tension. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  ((tension UnitChoices.SI).val : ℝ)

/-- Kilogram-per-metre readout of a physical linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-! ## Guitar states and labels from the primary figure -/

/-- The two string configurations compared in the problem. -/
inductive StringConfiguration where
  | unfingered
  | firstFretFingered
  deriving DecidableEq, Repr

/-- Ordered landmarks along the string in the primary figure. -/
inductive StringLandmark where
  | bridge
  | firstFret
  | nut
  deriving DecidableEq, Repr

/-- The two endpoints of the portion of string that is free to vibrate. -/
inductive VibratingSegmentEnd where
  | bridgeSide
  | nutSide
  deriving DecidableEq, Repr

/-- The horizontal orientation in which the guitar is drawn. -/
inductive GuitarOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-!
Independent physical quantities and geometric labels for the guitar string.

`firstFretPositionFromNut` is the quantity labeled `x` in the figure.  It is
left unconstrained here: in particular, neither `4.2 cm` nor the exact
equal-temperament expression is built into this setup.
-/
structure GuitarStringSetup where
  unfingeredLength : LengthQuantity
  firstFretPositionFromNut : LengthQuantity
  vibratingLength : StringConfiguration → LengthQuantity
  fundamentalFrequency : StringConfiguration → FrequencyQuantity
  tension : StringConfiguration → TensionQuantity
  linearMassDensity : StringConfiguration → LinearMassDensityQuantity
  vibratingEndpoint :
    StringConfiguration → VibratingSegmentEnd → StringLandmark
  fingerContact : StringConfiguration → Option StringLandmark
  orientation : GuitarOrientation

/-!
The numerical and geometric information stated in the problem and read from
the primary figure.  The first-fret distance `x` plus the remaining vibrating
length equals the original bridge-to-nut length `ℓ`.

The unchanged-tension and unchanged-density fields are stated data, not the
requested fret-position conclusion.
-/
structure MatchesProblemAndPrimaryFigure (setup : GuitarStringSetup) : Prop where
  unfingeredLengthCentimeters :
    lengthInCentimeters setup.unfingeredLength = 75
  unfingeredVibratingLength :
    setup.vibratingLength .unfingered = setup.unfingeredLength
  firstFretGeometry :
    lengthInCentimeters (setup.vibratingLength .firstFretFingered) +
        lengthInCentimeters setup.firstFretPositionFromNut =
      lengthInCentimeters setup.unfingeredLength
  unfingeredBridgeEndpoint :
    setup.vibratingEndpoint .unfingered .bridgeSide = .bridge
  unfingeredNutEndpoint :
    setup.vibratingEndpoint .unfingered .nutSide = .nut
  fingeredBridgeEndpoint :
    setup.vibratingEndpoint .firstFretFingered .bridgeSide = .bridge
  fingeredFretEndpoint :
    setup.vibratingEndpoint .firstFretFingered .nutSide = .firstFret
  noFingerContactWhenUnfingered : setup.fingerContact .unfingered = none
  fingerPressesFirstFret :
    setup.fingerContact .firstFretFingered = some .firstFret
  figureOrientation : setup.orientation = .horizontal
  tensionRemainsUnchanged :
    setup.tension .firstFretFingered = setup.tension .unfingered
  linearMassDensityRemainsUnchanged :
    setup.linearMassDensity .firstFretFingered =
      setup.linearMassDensity .unfingered

/-- Positivity and nondegeneracy conditions for an ordinary taut string. -/
structure HasPhysicalStringParameters (setup : GuitarStringSetup) : Prop where
  unfingeredLengthPositive : 0 < lengthInMeters setup.unfingeredLength
  fretDistancePositive :
    0 < lengthInMeters setup.firstFretPositionFromNut
  vibratingLengthsPositive :
    ∀ configuration, 0 < lengthInMeters (setup.vibratingLength configuration)
  frequenciesPositive :
    ∀ configuration,
      0 < frequencyInHertz (setup.fundamentalFrequency configuration)
  tensionsPositive :
    ∀ configuration, 0 < tensionInNewtons (setup.tension configuration)
  linearMassDensitiesPositive :
    ∀ configuration,
      0 < linearMassDensityInKilogramsPerMeter
        (setup.linearMassDensity configuration)

/-!
The fixed-end fundamental-mode law for each configuration,

`f₁ = (1 / (2 L)) sqrt(T / μ)`.

This is a governing law relating the independent physical quantities.  It
does not mention the value or formula requested for the fret position.
-/
structure SatisfiesStretchedStringFundamentalLaw
    (setup : GuitarStringSetup) : Prop where
  fundamentalFrequencyLaw :
    ∀ configuration,
      frequencyInHertz (setup.fundamentalFrequency configuration) =
        1 / (2 * lengthInMeters (setup.vibratingLength configuration)) *
          Real.sqrt
            (tensionInNewtons (setup.tension configuration) /
              linearMassDensityInKilogramsPerMeter
                (setup.linearMassDensity configuration))

/-- The dimensionless ratio between neighboring equal-tempered notes. -/
def equalTemperedSemitoneRatio : ℝ :=
  Real.rpow 2 ((1 : ℝ) / 12)

/-!
The stated musical relation: fingering the first fret raises the fundamental
by one equal-tempered semitone.  This gives a frequency ratio, not the unknown
geometric position `x`.
-/
structure RaisesPitchByOneEqualTemperedSemitone
    (setup : GuitarStringSetup) : Prop where
  adjacentNoteFrequencyRelation :
    frequencyInHertz (setup.fundamentalFrequency .firstFretFingered) =
      equalTemperedSemitoneRatio *
        frequencyInHertz (setup.fundamentalFrequency .unfingered)

/-!
For fixed tension and linear density, the stretched-string law and the given
semitone ratio imply that the fingered vibrating length is the unfingered
length divided by `2^(1/12)`.  This lemma remains a derived conclusion.
-/
lemma fingeredVibratingLength_ratio
    (setup : GuitarStringSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalStringParameters setup)
    (_stringLaw : SatisfiesStretchedStringFundamentalLaw setup)
    (_semitone : RaisesPitchByOneEqualTemperedSemitone setup) :
    lengthInMeters (setup.vibratingLength .firstFretFingered) =
      lengthInMeters (setup.vibratingLength .unfingered) /
        equalTemperedSemitoneRatio := by
  have hL₀ : 0 < lengthInMeters (setup.vibratingLength .unfingered) :=
    _physical.vibratingLengthsPositive .unfingered
  have hL₁ :
      0 < lengthInMeters (setup.vibratingLength .firstFretFingered) :=
    _physical.vibratingLengthsPositive .firstFretFingered
  have hT : 0 < tensionInNewtons (setup.tension .unfingered) :=
    _physical.tensionsPositive .unfingered
  have hμ :
      0 < linearMassDensityInKilogramsPerMeter
        (setup.linearMassDensity .unfingered) :=
    _physical.linearMassDensitiesPositive .unfingered
  have hsqrt :
      0 < Real.sqrt
        (tensionInNewtons (setup.tension .unfingered) /
          linearMassDensityInKilogramsPerMeter
            (setup.linearMassDensity .unfingered)) :=
    Real.sqrt_pos.2 (div_pos hT hμ)
  have hr : 0 < equalTemperedSemitoneRatio := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hf₀ := _stringLaw.fundamentalFrequencyLaw .unfingered
  have hf₁ := _stringLaw.fundamentalFrequencyLaw .firstFretFingered
  rw [_problem.tensionRemainsUnchanged,
    _problem.linearMassDensityRemainsUnchanged] at hf₁
  have hratio := _semitone.adjacentNoteFrequencyRelation
  rw [hf₁, hf₀] at hratio
  field_simp at hratio ⊢
  nlinarith

/-!
The corresponding exact formula for the figure's nut-to-first-fret distance.
It is stated before rounding to any displayed answer.
-/
lemma firstFretPosition_exactFormula
    (setup : GuitarStringSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalStringParameters setup)
    (_stringLaw : SatisfiesStretchedStringFundamentalLaw setup)
    (_semitone : RaisesPitchByOneEqualTemperedSemitone setup) :
    lengthInCentimeters setup.firstFretPositionFromNut =
      75 * (1 - 1 / equalTemperedSemitoneRatio) := by
  have hratio :=
    fingeredVibratingLength_ratio
      setup _problem _physical _stringLaw _semitone
  rw [_problem.unfingeredVibratingLength] at hratio
  have hgeometry := _problem.firstFretGeometry
  have hopen := _problem.unfingeredLengthCentimeters
  have hr : 0 < equalTemperedSemitoneRatio :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold lengthInCentimeters at hgeometry hopen ⊢
  field_simp at hratio ⊢
  nlinarith

/-! ## Displayed answers and current target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Centimetre value printed beside each answer label. -/
def AnswerChoice.centimeters : AnswerChoice → ℝ
  | .A => 82 / 10
  | .B => 62 / 10
  | .C => 52 / 10
  | .D => 42 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
A physical fret position agrees with a displayed tenth-centimetre answer when
its centimetre readout lies within half of `0.1 cm` of that displayed value.
-/
def MatchesAnswerChoice
    (position : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters position - choice.centimeters| ≤ 1 / 20

/-!
The first fret lies at the exact equal-temperament position
`75 (1 - 1 / 2^(1/12)) cm`, which rounds to `4.2 cm`, recorded answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0218:target`.
-/
theorem firstFretPosition_matches_recordedAnswerD
    (setup : GuitarStringSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalStringParameters setup)
    (_stringLaw : SatisfiesStretchedStringFundamentalLaw setup)
    (_semitone : RaisesPitchByOneEqualTemperedSemitone setup) :
    lengthInCentimeters setup.firstFretPositionFromNut =
        75 * (1 - 1 / equalTemperedSemitoneRatio) ∧
      MatchesAnswerChoice setup.firstFretPositionFromNut
        recordedAnswerChoice := by
  have hexact :=
    firstFretPosition_exactFormula
      setup _problem _physical _stringLaw _semitone
  refine ⟨hexact, ?_⟩
  simp only [MatchesAnswerChoice, recordedAnswerChoice,
    AnswerChoice.centimeters]
  rw [hexact]
  have hr_pos : 0 < equalTemperedSemitoneRatio :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr_pow : equalTemperedSemitoneRatio ^ 12 = 2 := by
    unfold equalTemperedSemitoneRatio
    calc
      (Real.rpow 2 ((1 : ℝ) / 12)) ^ 12 =
          Real.rpow (Real.rpow 2 ((1 : ℝ) / 12)) (12 : ℝ) :=
        (Real.rpow_natCast _ 12).symm
      _ = Real.rpow 2 (((1 : ℝ) / 12) * 12) :=
        (Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)
          ((1 : ℝ) / 12) (12 : ℝ)).symm
      _ = 2 := by norm_num
  have hlow :
      (1500 / 1417 : ℝ) < equalTemperedSemitoneRatio := by
    apply (pow_lt_pow_iff_left₀
      (by norm_num : (0 : ℝ) ≤ 1500 / 1417)
      (le_of_lt hr_pos) (by norm_num : (12 : ℕ) ≠ 0)).mp
    rw [hr_pow]
    norm_num
  have hupp :
      equalTemperedSemitoneRatio < (300 / 283 : ℝ) := by
    apply (pow_lt_pow_iff_left₀ (le_of_lt hr_pos)
      (by norm_num : (0 : ℝ) ≤ 300 / 283)
      (by norm_num : (12 : ℕ) ≠ 0)).mp
    rw [hr_pow]
    norm_num
  have hrecip_upp := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 1500 / 1417) hlow
  have hrecip_low :=
    one_div_lt_one_div_of_lt hr_pos hupp
  norm_num at hrecip_upp hrecip_low
  rw [abs_le]
  constructor <;> simp only [one_div] <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0218
