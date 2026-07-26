import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0172

open Dimension

/-!
# Beat frequency of two loaded supporting wires

A uniform horizontal bar is suspended from two vertical wires labelled `A`
and `B`.  A lead cube rests three-fourths of the way from `A` to `B`.  Static
force and moment balance determine different tensions in the two wires.  The
fundamental stretched-string law then determines their individual frequencies,
and their simultaneous sound has beat frequency equal to the absolute
difference of those frequencies.

Physical lengths, masses, forces, times, and frequencies are represented by
unit-independent `Dimensionful` Physlib quantities.  Real numbers below occur
only as readouts in named units, normalized positions along the bar, or
dimensionless mode and answer data.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- The physical dimension of force, `mass * length / time^2`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A unit-independent physical force, used for weights and wire tensions. -/
abbrev ForceQuantity : Type := Dimensionful (WithDim forceDimension ℝ)

/-- A unit-independent physical time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A unit-independent physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Read a dimension-tagged physical quantity in a selected system of units. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- Length readout in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout UnitChoices.SI length

/-- Length readout in centimetres, the unit used for each wire in the source. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  quantityReadout
    ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
    length

/-- Mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- Mass readout in grams, the unit used for each wire in the source. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  quantityReadout
    ({ UnitChoices.SI with mass := MassUnit.grams } : UnitChoices)
    mass

/-- Force readout in SI newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  quantityReadout UnitChoices.SI force

/-- Time readout in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  quantityReadout UnitChoices.SI time

/-- Frequency readout in SI hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  quantityReadout UnitChoices.SI frequency

/-! ## Apparatus, source labels, and primary-figure information -/

/-- The two supporting wires labelled in the supplied figure. -/
inductive WireLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The two downward loads on the support system. -/
inductive LoadLabel where
  | bar
  | leadCube
  deriving DecidableEq, Repr

/-- The endpoint of the bar at which a supporting wire is attached. -/
inductive BarEndpoint where
  | left
  | right
  deriving DecidableEq, Repr

/-- Qualitative orientations visible in the primary figure. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The stated mass distribution of the bar. -/
inductive BarMassDistribution where
  | uniform
  deriving DecidableEq, Repr

/-- The vibration mode specified in the question. -/
inductive VibrationMode where
  | fundamental
  | higherHarmonic (number : ℕ)
  deriving DecidableEq, Repr

/-- Individually visible, labelled features of the supplied diagram. -/
inductive FigureFeature where
  | ceiling
  | wireA
  | wireB
  | bar
  | cube
  deriving DecidableEq, Repr

/-- Categorical evidence stored from the primary image. -/
structure SuspensionFigure where
  showsFeature : FigureFeature → Bool
  wireAttachmentEnd : WireLabel → BarEndpoint
  cubeRestsOnBar : Bool
  barIsBelowCeiling : Bool

/-!
All physical quantities in the experiment.  Positions are fractions of the
bar span measured rightward from support `A`: hence `A` has coordinate `0`
and `B` coordinate `1`.  Neither `beatFrequency` nor either wire tension is
assigned a numerical answer in this structure.
-/
structure SuspendedBarWireSetup where
  figure : SuspensionFigure
  barOrientation : Orientation
  wireOrientation : WireLabel → Orientation
  barMassDistribution : BarMassDistribution
  barSpan : LengthQuantity
  loadWeight : LoadLabel → ForceQuantity
  loadPositionFraction : LoadLabel → ℝ
  supportPositionFraction : WireLabel → ℝ
  wireLength : WireLabel → LengthQuantity
  wireMass : WireLabel → MassQuantity
  wireTension : WireLabel → ForceQuantity
  pluckPositionFraction : WireLabel → ℝ
  pluckTime : WireLabel → TimeQuantity
  vibrationMode : WireLabel → VibrationMode
  fundamentalFrequency : WireLabel → FrequencyQuantity
  beatFrequency : FrequencyQuantity

/-! ## Figure evidence and stated data -/

/-!
The primary image shows both labelled vertical wires descending from a
ceiling to opposite ends of the horizontal bar, with the cube resting on the
bar.  This predicate contains no force, frequency, or answer-choice value.
-/
def MatchesPrimaryFigure (setup : SuspendedBarWireSetup) : Prop :=
  (setup.figure.showsFeature .ceiling = true) ∧
    (setup.figure.showsFeature .wireA = true) ∧
    (setup.figure.showsFeature .wireB = true) ∧
    (setup.figure.showsFeature .bar = true) ∧
    (setup.figure.showsFeature .cube = true) ∧
    setup.figure.wireAttachmentEnd .A = .left ∧
    setup.figure.wireAttachmentEnd .B = .right ∧
    setup.figure.cubeRestsOnBar = true ∧
    setup.figure.barIsBelowCeiling = true

/-!
Qualitative geometry and normalized load locations.  Uniformity puts the
bar's weight at its midpoint; the lead cube is at the stated three-quarter
point from `A` to `B`.
-/
def MatchesBarAndSupportGeometry (setup : SuspendedBarWireSetup) : Prop :=
  setup.barOrientation = .horizontal ∧
    setup.wireOrientation .A = .vertical ∧
    setup.wireOrientation .B = .vertical ∧
    setup.barMassDistribution = .uniform ∧
    setup.supportPositionFraction .A = 0 ∧
    setup.supportPositionFraction .B = 1 ∧
    setup.loadPositionFraction .bar = 1 / 2 ∧
    setup.loadPositionFraction .leadCube = 3 / 4

/-!
The numerical measurements printed in the problem: bar weight `165 N`, cube
weight `185 N`, and, for each identical wire, length `75.0 cm` and mass
`5.50 g`.  No tension or frequency appears here.
-/
def MatchesStatedMeasurements (setup : SuspendedBarWireSetup) : Prop :=
  forceInNewtons (setup.loadWeight .bar) = 165 ∧
    forceInNewtons (setup.loadWeight .leadCube) = 185 ∧
    ∀ wire : WireLabel,
      lengthInCentimeters (setup.wireLength wire) = 75 ∧
        massInGrams (setup.wireMass wire) = 11 / 2

/-!
Both wires are plucked at their centers at the same time and are considered
in their fundamental modes.  This records the excitation requested by the
question, without asserting the resulting beat frequency.
-/
def MatchesSimultaneousFundamentalPluck
    (setup : SuspendedBarWireSetup) : Prop :=
  setup.pluckPositionFraction .A = 1 / 2 ∧
    setup.pluckPositionFraction .B = 1 / 2 ∧
    setup.pluckTime .A = setup.pluckTime .B ∧
    setup.vibrationMode .A = .fundamental ∧
    setup.vibrationMode .B = .fundamental

/-!
Positivity and in-span conditions for the mechanical model.  These are
physical admissibility assumptions and do not identify an answer choice.
-/
def HasPhysicalParameters (setup : SuspendedBarWireSetup) : Prop :=
  0 < lengthInMeters setup.barSpan ∧
    (∀ load : LoadLabel, 0 < forceInNewtons (setup.loadWeight load)) ∧
    (∀ wire : WireLabel,
      0 < lengthInMeters (setup.wireLength wire) ∧
        0 < massInKilograms (setup.wireMass wire) ∧
        0 < forceInNewtons (setup.wireTension wire) ∧
        0 < frequencyInHertz (setup.fundamentalFrequency wire)) ∧
    0 ≤ frequencyInHertz setup.beatFrequency ∧
    (∀ load : LoadLabel,
      setup.loadPositionFraction load ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ wire : WireLabel,
      setup.supportPositionFraction wire ∈ Set.Icc (0 : ℝ) 1

/-! ## Governing mechanical and wave laws -/

/-!
Vertical force balance and moment balance about the left end of the bar.
The second equality uses actual metre lever arms: the bar span multiplied by
each normalized position.  It is a general static-equilibrium law, not the
numerical tension sought as an intermediate calculation.
-/
structure SatisfiesStaticEquilibrium
    (setup : SuspendedBarWireSetup) : Prop where
  verticalForceBalance :
    forceInNewtons (setup.wireTension .A) +
        forceInNewtons (setup.wireTension .B) =
      forceInNewtons (setup.loadWeight .bar) +
        forceInNewtons (setup.loadWeight .leadCube)
  momentBalanceAboutLeftEnd :
    forceInNewtons (setup.wireTension .A) *
          (lengthInMeters setup.barSpan * setup.supportPositionFraction .A) +
        forceInNewtons (setup.wireTension .B) *
          (lengthInMeters setup.barSpan * setup.supportPositionFraction .B) =
      forceInNewtons (setup.loadWeight .bar) *
          (lengthInMeters setup.barSpan * setup.loadPositionFraction .bar) +
        forceInNewtons (setup.loadWeight .leadCube) *
          (lengthInMeters setup.barSpan * setup.loadPositionFraction .leadCube)

/-!
The fundamental frequency in hertz of a stretched uniform wire with SI
length `lengthMeters`, mass `massKilograms`, and tension `tensionNewtons`:
`f = (1 / (2 L)) * sqrt(T / (m / L))`.
-/
def stretchedStringFundamentalHertz
    (lengthMeters massKilograms tensionNewtons : ℝ) : ℝ :=
  1 / (2 * lengthMeters) *
    Real.sqrt (tensionNewtons / (massKilograms / lengthMeters))

/-!
Each supporting wire obeys the fundamental stretched-string law with its own
static tension and its measured length and mass.  The law is uniform over
both labels and contains no beat-frequency answer.
-/
structure SatisfiesStretchedStringFundamentalLaw
    (setup : SuspendedBarWireSetup) : Prop where
  frequencyLaw :
    ∀ wire : WireLabel,
      frequencyInHertz (setup.fundamentalFrequency wire) =
        stretchedStringFundamentalHertz
          (lengthInMeters (setup.wireLength wire))
          (massInKilograms (setup.wireMass wire))
          (forceInNewtons (setup.wireTension wire))

/-!
For two pure tones, the beat frequency is the absolute difference of their
frequencies.  This governing acoustics law relates the unknown observable to
the two component frequencies but supplies no numerical result.
-/
structure SatisfiesBeatFrequencyLaw
    (setup : SuspendedBarWireSetup) : Prop where
  beatFrequencyLaw :
    frequencyInHertz setup.beatFrequency =
      |frequencyInHertz (setup.fundamentalFrequency .A) -
        frequencyInHertz (setup.fundamentalFrequency .B)|

/-! ## Derived intermediates and multiple-choice target -/

/-- Labels of the four frequency choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The hertz value displayed beside each answer label. -/
def AnswerChoice.frequencyHertz : AnswerChoice → ℝ
  | .A => 273 / 10
  | .B => 38
  | .C => 448 / 5
  | .D => 77 / 2

/-- Dataset metadata: the recorded answer is A; this is never a premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- A displayed answer is uniquely closest to the model's beat frequency. -/
def IsClosestAnswerChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |frequencyInHertz frequency - choice.frequencyHertz| <
      |frequencyInHertz frequency - other.frequencyHertz|

/-!
The original `75.0 cm` and `5.50 g` data have SI readouts `3/4 m` and
`11/2000 kg`.  This is a unit-conversion intermediate, not a frequency
conclusion.
-/
lemma statedWireMeasurementsInSI
    (setup : SuspendedBarWireSetup)
    (hMeasurements : MatchesStatedMeasurements setup) :
    ∀ wire : WireLabel,
      lengthInMeters (setup.wireLength wire) = 3 / 4 ∧
        massInKilograms (setup.wireMass wire) = 11 / 2000 := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value ↦ value.val)
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [lengthInCentimeters, lengthInMeters, quantityReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have mass_grams_eq (mass : MassQuantity) :
      massInGrams mass = 1000 * massInKilograms mass := by
    have h := congrArg (fun value ↦ value.val)
      (mass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, quantityReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  intro wire
  have hLengthConversion := length_centimeters_eq (setup.wireLength wire)
  have hMassConversion := mass_grams_eq (setup.wireMass wire)
  have hWireMeasurements := hMeasurements.2.2 wire
  constructor
  · rw [hWireMeasurements.1] at hLengthConversion
    norm_num at hLengthConversion ⊢
    linarith
  · rw [hWireMeasurements.2] at hMassConversion
    norm_num at hMassConversion ⊢
    linarith

/-!
Static equilibrium gives `128.75 N` in wire `A` and `221.25 N` in wire `B`.
These are derived intermediate tensions; neither is the requested beat
frequency.
-/
lemma supportTensionsInNewtons
    (setup : SuspendedBarWireSetup)
    (hGeometry : MatchesBarAndSupportGeometry setup)
    (hMeasurements : MatchesStatedMeasurements setup)
    (hPhysical : HasPhysicalParameters setup)
    (hStatics : SatisfiesStaticEquilibrium setup) :
    forceInNewtons (setup.wireTension .A) = 515 / 4 ∧
      forceInNewtons (setup.wireTension .B) = 885 / 4 := by
  have hForce := hStatics.verticalForceBalance
  have hMoment := hStatics.momentBalanceAboutLeftEnd
  have hSpanPositive := hPhysical.1
  rcases hGeometry with
    ⟨_, _, _, _, hSupportA, hSupportB, hBarPosition, hCubePosition⟩
  rcases hMeasurements with ⟨hBarWeight, hCubeWeight, _⟩
  rw [hBarWeight, hCubeWeight] at hForce
  rw [hSupportA, hSupportB, hBarPosition, hCubePosition,
    hBarWeight, hCubeWeight] at hMoment
  norm_num at hForce hMoment ⊢
  constructor <;> nlinarith

/-!
Combining the static support tensions, the stretched-string fundamental law,
and the two-tone beat law gives the exact analytical beat frequency below.
It lies strictly between `27 Hz` and `28 Hz` and is uniquely closest to choice
A, whose displayed value is `27.3 Hz`.

The analytical value is approximately `27.463 Hz`; therefore the conclusion
selects the multiple-choice display rather than incorrectly treating
`27.3 Hz` as an exact equality.

Blueprint label: `thm:physics:phyx_mini_0172:target`.
-/
theorem problem_phyx_mini_0172
    (setup : SuspendedBarWireSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hGeometry : MatchesBarAndSupportGeometry setup)
    (hMeasurements : MatchesStatedMeasurements setup)
    (hPluck : MatchesSimultaneousFundamentalPluck setup)
    (hPhysical : HasPhysicalParameters setup)
    (hStatics : SatisfiesStaticEquilibrium setup)
    (hString : SatisfiesStretchedStringFundamentalLaw setup)
    (hBeat : SatisfiesBeatFrequencyLaw setup) :
    frequencyInHertz setup.beatFrequency =
        |stretchedStringFundamentalHertz (3 / 4) (11 / 2000) (515 / 4) -
          stretchedStringFundamentalHertz (3 / 4) (11 / 2000) (885 / 4)| ∧
      27 < frequencyInHertz setup.beatFrequency ∧
      frequencyInHertz setup.beatFrequency < 28 ∧
      IsClosestAnswerChoice setup.beatFrequency .A := by
  have hSI := statedWireMeasurementsInSI setup hMeasurements
  rcases supportTensionsInNewtons setup hGeometry hMeasurements hPhysical hStatics with
    ⟨hTensionA, hTensionB⟩
  have hFrequencyA := hString.frequencyLaw .A
  have hFrequencyB := hString.frequencyLaw .B
  rw [(hSI .A).1, (hSI .A).2, hTensionA] at hFrequencyA
  rw [(hSI .B).1, (hSI .B).2, hTensionB] at hFrequencyB
  have hExact := hBeat.beatFrequencyLaw
  rw [hFrequencyA, hFrequencyB] at hExact
  let frequencyA : ℝ :=
    stretchedStringFundamentalHertz (3 / 4) (11 / 2000) (515 / 4)
  let frequencyB : ℝ :=
    stretchedStringFundamentalHertz (3 / 4) (11 / 2000) (885 / 4)
  have hExact' :
      frequencyInHertz setup.beatFrequency = |frequencyA - frequencyB| := by
    simpa [frequencyA, frequencyB] using hExact
  have hFrequencyANonnegative : 0 ≤ frequencyA := by
    dsimp [frequencyA, stretchedStringFundamentalHertz]
    positivity
  have hFrequencyBNonnegative : 0 ≤ frequencyB := by
    dsimp [frequencyB, stretchedStringFundamentalHertz]
    positivity
  have hFrequencyASquare : frequencyA ^ 2 = 257500 / 33 := by
    dsimp [frequencyA]
    rw [stretchedStringFundamentalHertz, mul_pow,
      Real.sq_sqrt
        (by norm_num :
          (0 : ℝ) ≤ (515 / 4) / ((11 / 2000) / (3 / 4)))]
    norm_num
  have hFrequencyBSquare : frequencyB ^ 2 = 147500 / 11 := by
    dsimp [frequencyB]
    rw [stretchedStringFundamentalHertz, mul_pow,
      Real.sq_sqrt
        (by norm_num :
          (0 : ℝ) ≤ (885 / 4) / ((11 / 2000) / (3 / 4)))]
    norm_num
  have hFrequencyALower : 88 < frequencyA := by
    nlinarith [sq_nonneg (frequencyA - 88)]
  have hFrequencyAUpper : frequencyA < 177 / 2 := by
    nlinarith [sq_nonneg (frequencyA - 177 / 2)]
  have hFrequencyBLower : 231 / 2 < frequencyB := by
    nlinarith [sq_nonneg (frequencyB - 231 / 2)]
  have hFrequencyBUpper : frequencyB < 116 := by
    nlinarith [sq_nonneg (frequencyB - 116)]
  have hDifferenceNonpositive : frequencyA - frequencyB ≤ 0 := by
    linarith
  have hBeatLower : 27 < frequencyInHertz setup.beatFrequency := by
    rw [hExact', abs_of_nonpos hDifferenceNonpositive]
    linarith
  have hBeatUpper : frequencyInHertz setup.beatFrequency < 28 := by
    rw [hExact', abs_of_nonpos hDifferenceNonpositive]
    linarith
  refine ⟨hExact, hBeatLower, hBeatUpper, ?_⟩
  unfold IsClosestAnswerChoice
  intro other hOther
  cases other with
  | A => exact (hOther rfl).elim
  | B =>
      simp only [AnswerChoice.frequencyHertz]
      rw [abs_of_nonpos (by linarith :
        frequencyInHertz setup.beatFrequency - 38 ≤ 0), abs_lt]
      constructor <;> linarith
  | C =>
      simp only [AnswerChoice.frequencyHertz]
      rw [abs_of_nonpos (by linarith :
        frequencyInHertz setup.beatFrequency - 448 / 5 ≤ 0), abs_lt]
      constructor <;> linarith
  | D =>
      simp only [AnswerChoice.frequencyHertz]
      rw [abs_of_nonpos (by linarith :
        frequencyInHertz setup.beatFrequency - 77 / 2 ≤ 0), abs_lt]
      constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0172
