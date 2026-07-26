import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0217

open Dimension

/-!
# Frequency estimated from a seashell cavity

The source asks for the frequency heard with an ear very near a
`15 cm`-diameter conch shell.  The primary image shows the conch held at the
listener's ear in a beach scene, but contains no printed labels.  The usual
estimate treats the air cavity as an open--closed quarter-wave resonator whose
effective length is the shell diameter.  With the conventional elementary
value `340 m/s` for sound in ambient air, this gives about `567 Hz`, so the
closest displayed estimate is `570 Hz`.

Lengths, frequencies, and speeds below are unit-independent Physlib
quantities.  Real numbers occur only as readouts in named units and as the
displayed multiple-choice data.  In particular, the resonant wavelength and
frequency are independent fields related to the setup only through explicit
modeling assumptions and governing acoustic laws.
-/

/-! ## Dimensionful acoustic quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the chosen unit readout. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev AcousticFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical sound speed, carrying length-per-time dimension. -/
abbrev AcousticSpeed : Type := DimSpeed

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : AcousticSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Centimeter readout used for the shell diameter in the problem statement. -/
def lengthInCentimeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Meter readout used in the acoustic-wave calculation. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of the sound propagation speed. -/
def speedInMetersPerSecond (speed : AcousticSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-image evidence -/

/-- The shell type visible in the supplied beach image. -/
inductive SeashellKind where
  | conch
  deriving DecidableEq, Repr

/-- The acoustic medium occupying the resonating shell cavity. -/
inductive AcousticMedium where
  | ambientAirInsideShell
  deriving DecidableEq, Repr

/-- The two ends of the one-dimensional idealized shell cavity. -/
inductive ResonatorEnd where
  | mouth
  | innerCavityEnd
  deriving DecidableEq, Repr

/-- Boundary behavior used by the longitudinal quarter-wave model. -/
inductive AcousticBoundaryCondition where
  | openEnd
  | effectivelyClosedEnd
  deriving DecidableEq, Repr

/-- The resonant mode retained in this order-of-magnitude estimate. -/
inductive ResonanceMode where
  | fundamental
  | higherOddMode (modeNumber : ℕ)
  deriving DecidableEq, Repr

/-- The broadband excitation responsible for the familiar shell sound. -/
inductive AcousticExcitation where
  | ambientBackgroundNoise
  deriving DecidableEq, Repr

/-- Physical interpretation of the sound heard by the listener. -/
inductive PerceivedSoundMechanism where
  | shellCavityResonance
  deriving DecidableEq, Repr

/-- Salient objects visible in the primary bitmap; the image has no text labels. -/
inductive FigureObject where
  | listener
  | listenerEar
  | conchShell
  | ocean
  | sandyBeach
  | sky
  deriving DecidableEq, Repr

/-- Categorical evidence extracted from the supplied primary image. -/
structure SeashellFigure where
  showsObject : FigureObject → Bool
  shellHeldAtListenerEar : Bool
  showsPrintedText : Bool

/-!
Independent physical quantities in the seashell estimate.  Neither the
resonant wavelength nor the resonant frequency is assigned a numerical value
in this setup structure.
-/
structure SeashellResonanceSetup where
  figure : SeashellFigure
  shellKind : SeashellKind
  medium : AcousticMedium
  boundaryCondition : ResonatorEnd → AcousticBoundaryCondition
  resonanceMode : ResonanceMode
  excitation : AcousticExcitation
  perceivedSoundMechanism : PerceivedSoundMechanism
  shellDiameter : AcousticLength
  effectiveCavityLength : AcousticLength
  resonantWavelength : AcousticLength
  resonantFrequency : AcousticFrequency
  soundSpeed : AcousticSpeed

/-!
The primary image shows a conch held next to the listener's ear, with ocean,
beach, and sky in the background.  It has no printed dimension or frequency
label.  This predicate contains no wavelength or frequency value.
-/
structure MatchesPrimaryFigure (setup : SeashellResonanceSetup) : Prop where
  shellIsConch : setup.shellKind = .conch
  showsListener : setup.figure.showsObject .listener = true
  showsListenerEar : setup.figure.showsObject .listenerEar = true
  showsConch : setup.figure.showsObject .conchShell = true
  showsOcean : setup.figure.showsObject .ocean = true
  showsBeach : setup.figure.showsObject .sandyBeach = true
  showsSky : setup.figure.showsObject .sky = true
  shellHeldAtEar : setup.figure.shellHeldAtListenerEar = true
  noPrintedText : setup.figure.showsPrintedText = false

/-!
The sole numerical measurement stated in the prose is the shell's `15 cm`
diameter.  No resonant wavelength or frequency is included here.
-/
structure MatchesProblemStatement (setup : SeashellResonanceSetup) : Prop where
  shellDiameterCentimeters :
    lengthInCentimeters setup.shellDiameter = 15

/-! Positivity and nondegeneracy conditions for the physical acoustic model. -/
structure HasPhysicalAcousticParameters
    (setup : SeashellResonanceSetup) : Prop where
  shellDiameterPositive : 0 < lengthInMeters setup.shellDiameter
  effectiveCavityLengthPositive :
    0 < lengthInMeters setup.effectiveCavityLength
  resonantWavelengthPositive :
    0 < lengthInMeters setup.resonantWavelength
  resonantFrequencyPositive :
    0 < frequencyInHertz setup.resonantFrequency
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed

/-!
The conventional elementary estimate for sound in ambient air, kept separate
from both the supplied diameter and the governing resonance laws because the
problem itself does not state a temperature or propagation speed.
-/
structure UsesStandardAmbientAirSoundSpeed
    (setup : SeashellResonanceSetup) : Prop where
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeed = 340

/-!
The geometric idealization needed to turn the given diameter into a cavity
scale: the conch contains ambient air, its mouth is open, its deep end is
effectively closed, and only the fundamental response is retained.  The
effective resonator length is approximated by the stated shell diameter in
every length unit.  This model contains no frequency value or answer choice.
-/
structure UsesFundamentalClosedOpenDiameterApproximation
    (setup : SeashellResonanceSetup) : Prop where
  mediumIsAmbientAir : setup.medium = .ambientAirInsideShell
  mouthIsOpen : setup.boundaryCondition .mouth = .openEnd
  innerEndIsEffectivelyClosed :
    setup.boundaryCondition .innerCavityEnd = .effectivelyClosedEnd
  fundamentalMode : setup.resonanceMode = .fundamental
  excitationIsAmbientNoise : setup.excitation = .ambientBackgroundNoise
  perceivedSoundIsCavityResonance :
    setup.perceivedSoundMechanism = .shellCavityResonance
  effectiveLengthEqualsDiameter :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.effectiveCavityLength =
        lengthReadout unit setup.shellDiameter

/-!
Governing laws for the idealized fundamental open--closed acoustic resonance:
the cavity occupies one quarter of a wavelength, and the nondispersive wave
relation is `v = f lambda`.  These laws are stated in compatible selected
units and contain neither the derived frequency nor a displayed answer.
-/
structure SatisfiesQuarterWaveAcousticLaws
    (setup : SeashellResonanceSetup) : Prop where
  fundamentalQuarterWaveGeometry :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.resonantWavelength =
        4 * lengthReadout unit setup.effectiveCavityLength
  speedEqualsFrequencyTimesWavelength :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeed =
        frequencyReadout timeUnit setup.resonantFrequency *
          lengthReadout lengthUnit setup.resonantWavelength

/-! ## Derived values and displayed estimate -/

/-! Converting the stated `15 cm` diameter gives `3/20 m`. -/
lemma shellDiameterInMeters_eq_threeTwentieths
    (setup : SeashellResonanceSetup)
    (_statement : MatchesProblemStatement setup) :
    lengthInMeters setup.shellDiameter = (3 / 20 : ℝ) := by
  let centimeterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hdim : centimeterUnits.dimScale UnitChoices.SI L𝓭 =
      (⟨1 / 100, by norm_num⟩ : NNReal) := by
    apply NNReal.eq
    norm_num [centimeterUnits, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
  have hscale :=
    setup.shellDiameter.property centimeterUnits UnitChoices.SI
  rw [show dim (WithDim L𝓭 NNReal) = L𝓭 by rfl, hdim] at hscale
  have hval :=
    congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) hscale
  have hstatement :
      ((setup.shellDiameter centimeterUnits).val : ℝ) = 15 := by
    simpa [lengthInCentimeters, lengthReadout, centimeterUnits] using
      _statement.shellDiameterCentimeters
  change ((setup.shellDiameter UnitChoices.SI).val : ℝ) = _
  change ((setup.shellDiameter UnitChoices.SI).val : ℝ) =
    (1 / 100 : ℝ) * ((setup.shellDiameter centimeterUnits).val : ℝ) at hval
  calc
    ((setup.shellDiameter UnitChoices.SI).val : ℝ) =
        (1 / 100 : ℝ) *
          ((setup.shellDiameter centimeterUnits).val : ℝ) := hval
    _ = 3 / 20 := by
      rw [hstatement]
      norm_num

/-!
Under the diameter-scale quarter-wave model, the resonant wavelength is
`4 * 0.15 m = 0.60 m`.
-/
lemma resonantWavelengthInMeters_eq_threeFifths
    (setup : SeashellResonanceSetup)
    (_statement : MatchesProblemStatement setup)
    (_model : UsesFundamentalClosedOpenDiameterApproximation setup)
    (_laws : SatisfiesQuarterWaveAcousticLaws setup) :
    lengthInMeters setup.resonantWavelength = (3 / 5 : ℝ) := by
  calc
    lengthInMeters setup.resonantWavelength =
        4 * lengthInMeters setup.effectiveCavityLength :=
      _laws.fundamentalQuarterWaveGeometry LengthUnit.meters
    _ = 4 * lengthInMeters setup.shellDiameter := by
      unfold lengthInMeters
      rw [_model.effectiveLengthEqualsDiameter LengthUnit.meters]
    _ = 3 / 5 := by
      rw [shellDiameterInMeters_eq_threeTwentieths setup _statement]
      norm_num

/-!
At `340 m/s`, the idealized `0.60 m` wavelength gives the exact model value
`1700/3 Hz`, approximately `566.7 Hz`.
-/
lemma resonantFrequencyInHertz_eq_seventeenHundredThirds
    (setup : SeashellResonanceSetup)
    (_statement : MatchesProblemStatement setup)
    (_air : UsesStandardAmbientAirSoundSpeed setup)
    (_model : UsesFundamentalClosedOpenDiameterApproximation setup)
    (_laws : SatisfiesQuarterWaveAcousticLaws setup) :
    frequencyInHertz setup.resonantFrequency = (1700 / 3 : ℝ) := by
  have hwavelength := resonantWavelengthInMeters_eq_threeFifths
    setup _statement _model _laws
  have hspeed := _air.soundSpeedMetersPerSecond
  have hwave := _laws.speedEqualsFrequencyTimesWavelength
    LengthUnit.meters TimeUnit.seconds
  unfold frequencyInHertz speedInMetersPerSecond lengthInMeters at *
  norm_num at hwavelength hspeed ⊢
  nlinarith

/-- Labels of the four frequency estimates printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Hertz value printed beside each displayed answer label. -/
def displayedAnswerFrequencyHertz : AnswerChoice → ℝ
  | .A => 510
  | .B => 530
  | .C => 550
  | .D => 570

/-- The answer label recorded in the supplied dataset; this is never a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Absolute discrepancy between the modeled resonance and a displayed estimate. -/
def displayedAnswerErrorHertz
    (setup : SeashellResonanceSetup) (choice : AnswerChoice) : ℝ :=
  |frequencyInHertz setup.resonantFrequency -
    displayedAnswerFrequencyHertz choice|

/-- A displayed estimate is strictly closer than every other displayed value. -/
def IsClosestDisplayedFrequencyChoice
    (setup : SeashellResonanceSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    displayedAnswerErrorHertz setup choice <
      displayedAnswerErrorHertz setup other

/-!
The `15 cm` conch, modeled as a fundamental open--closed cavity with sound
speed `340 m/s`, has idealized resonance frequency `1700/3 Hz`, about
`566.7 Hz`.  Among the four supplied estimates this is uniquely closest to
`570 Hz`, choice D.

This theorem formalizes `thm:physics:phyx_mini_0217:target`.
-/
theorem problem_phyx_mini_0217
    (setup : SeashellResonanceSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_statement : MatchesProblemStatement setup)
    (_physical : HasPhysicalAcousticParameters setup)
    (_air : UsesStandardAmbientAirSoundSpeed setup)
    (_model : UsesFundamentalClosedOpenDiameterApproximation setup)
    (_laws : SatisfiesQuarterWaveAcousticLaws setup) :
    frequencyInHertz setup.resonantFrequency = (1700 / 3 : ℝ) ∧
      IsClosestDisplayedFrequencyChoice setup recordedDatasetAnswer := by
  have hfrequency := resonantFrequencyInHertz_eq_seventeenHundredThirds
    setup _statement _air _model _laws
  refine ⟨hfrequency, ?_⟩
  intro other hother
  simp only [displayedAnswerErrorHertz]
  rw [hfrequency]
  cases other with
  | A => norm_num [recordedDatasetAnswer, displayedAnswerFrequencyHertz]
  | B => norm_num [recordedDatasetAnswer, displayedAnswerFrequencyHertz]
  | C => norm_num [recordedDatasetAnswer, displayedAnswerFrequencyHertz]
  | D => exact (hother (by rfl)).elim

end PhyXMiniProblems.ProblemPhyXMini0217
