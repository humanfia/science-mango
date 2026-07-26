import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Speed of sound in oxygen from a Kundt-tube pattern

This file models problem `phyx_mini_0183`. A vibrating piston drives pure
oxygen in a glass tube closed at the far end. Finely ground cork accumulates
at displacement nodes of the standing sound wave. The primary figure shows
six ordered cork piles and marks `123 cm` from the second pile to the fifth,
which is a span of three adjacent-node intervals. The piston frequency is
`400 Hz`.

Lengths, frequency, and speed are unit-independent Physlib quantities. Real
numbers occur only as readouts in explicitly selected units and as the
displayed multiple-choice values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0183

open Dimension

/-! ## Dimensionful acoustic quantities and unit readouts -/

/-- A nonnegative physical length, independent of the selected length unit. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency { UnitChoices.SI with time := unit }).val : ℝ)

/-- Read a physical speed in the selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (speed : DimSpeed) : ℝ :=
  ((speed { UnitChoices.SI with
      length := lengthUnit, time := timeUnit }).val : ℝ)

/-- Metre readout used for wavelengths and apparatus lengths. -/
def metersValue (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the `123 cm` arrow in the figure. -/
def centimetersValue (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Hertz readout of the piston driving frequency. -/
def hertzValue (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Metres-per-second readout used by the displayed answer choices. -/
def metersPerSecondValue (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Apparatus and primary-figure labels -/

/-- Gas sample named by the problem. -/
inductive TubeGas where
  | pureOxygen
  deriving DecidableEq, Repr

/-- Material of the long tube shown in the figure. -/
inductive TubeMaterial where
  | glass
  deriving DecidableEq, Repr

/-- Material whose fine particles reveal the standing-wave nodes. -/
inductive TracerParticleMaterial where
  | finelyGroundCork
  deriving DecidableEq, Repr

/-- Boundary conditions at the two ends of the resonant gas column. -/
inductive TubeBoundaryCondition where
  | vibratingPiston
  | rigidClosedEnd
  deriving DecidableEq, Repr

/-- The six cork piles visible from left to right in the primary figure. -/
inductive CorkPileLabel where
  | pile0
  | pile1
  | pile2
  | pile3
  | pile4
  | pile5
  deriving DecidableEq, Repr

/-- Consecutive cork piles in the left-to-right order drawn in the figure. -/
inductive AdjacentCorkPiles : CorkPileLabel → CorkPileLabel → Prop where
  | pile0_pile1 : AdjacentCorkPiles .pile0 .pile1
  | pile1_pile2 : AdjacentCorkPiles .pile1 .pile2
  | pile2_pile3 : AdjacentCorkPiles .pile2 .pile3
  | pile3_pile4 : AdjacentCorkPiles .pile3 .pile4
  | pile4_pile5 : AdjacentCorkPiles .pile4 .pile5

/--
Physical quantities and labels for the resonant Kundt-tube configuration.

`tubeInternalLength` records the long glass tube, while
`resonantGasColumnLength` records the piston-to-closed-end oxygen column at
the depicted resonant piston position. The marked span and wavelength remain
unknown physical lengths; in particular, no field assigns the requested
sound speed a numerical value.
-/
structure KundtTubeSetup where
  gas : TubeGas
  tubeMaterial : TubeMaterial
  tracerMaterial : TracerParticleMaterial
  leftBoundary : TubeBoundaryCondition
  rightBoundary : TubeBoundaryCondition
  tubeInternalLength : AcousticLength
  resonantGasColumnLength : AcousticLength
  drivingFrequency : AcousticFrequency
  soundSpeedInOxygen : DimSpeed
  standingWavelengthInOxygen : AcousticLength
  corkPileAxialPosition : CorkPileLabel → AcousticLength
  isDisplacementNodeAt : AcousticLength → Prop
  markedSpanStartPile : CorkPileLabel
  markedSpanEndPile : CorkPileLabel
  markedSpanLength : AcousticLength

/-- The six depicted cork piles occur in strict left-to-right axial order. -/
def CorkPilesAreStrictlyOrdered (setup : KundtTubeSetup) : Prop :=
  metersValue (setup.corkPileAxialPosition .pile0) <
      metersValue (setup.corkPileAxialPosition .pile1) ∧
    metersValue (setup.corkPileAxialPosition .pile1) <
      metersValue (setup.corkPileAxialPosition .pile2) ∧
    metersValue (setup.corkPileAxialPosition .pile2) <
      metersValue (setup.corkPileAxialPosition .pile3) ∧
    metersValue (setup.corkPileAxialPosition .pile3) <
      metersValue (setup.corkPileAxialPosition .pile4) ∧
    metersValue (setup.corkPileAxialPosition .pile4) <
      metersValue (setup.corkPileAxialPosition .pile5)

/--
Qualitative apparatus information and geometry read from the primary figure.

The `123 cm` arrow begins at `pile1` and ends at `pile4`; its metric readout
is recorded separately. No wavelength or sound-speed answer is included.
-/
structure MatchesKundtTubeScenarioAndFigure (setup : KundtTubeSetup) : Prop where
  gas_is_pure_oxygen : setup.gas = .pureOxygen
  tube_is_glass : setup.tubeMaterial = .glass
  tracer_is_finely_ground_cork : setup.tracerMaterial = .finelyGroundCork
  left_end_is_vibrating_piston : setup.leftBoundary = .vibratingPiston
  right_end_is_closed : setup.rightBoundary = .rigidClosedEnd
  six_piles_are_ordered : CorkPilesAreStrictlyOrdered setup
  all_piles_lie_in_resonant_column : ∀ pile,
    metersValue (setup.corkPileAxialPosition pile) ≤
      metersValue setup.resonantGasColumnLength
  marked_span_starts_at_second_pile : setup.markedSpanStartPile = .pile1
  marked_span_ends_at_fifth_pile : setup.markedSpanEndPile = .pile4
  marked_span_is_endpoint_separation : ∀ unit : LengthUnit,
    lengthReadout unit setup.markedSpanLength =
      lengthReadout unit
          (setup.corkPileAxialPosition setup.markedSpanEndPile) -
        lengthReadout unit
          (setup.corkPileAxialPosition setup.markedSpanStartPile)

/-- The two numerical readouts printed in the primary figure. -/
structure MatchesKundtTubeNumericalReadouts (setup : KundtTubeSetup) : Prop where
  piston_frequency_hertz : hertzValue setup.drivingFrequency = 400
  marked_span_centimeters : centimetersValue setup.markedSpanLength = 123

/-- Positivity and containment conditions for the physical apparatus. -/
def HasPhysicalKundtTubeParameters (setup : KundtTubeSetup) : Prop :=
  0 < metersValue setup.tubeInternalLength ∧
    0 < metersValue setup.resonantGasColumnLength ∧
    metersValue setup.resonantGasColumnLength ≤
      metersValue setup.tubeInternalLength ∧
    0 < hertzValue setup.drivingFrequency ∧
    0 < metersPerSecondValue setup.soundSpeedInOxygen ∧
    0 < metersValue setup.standingWavelengthInOxygen ∧
    0 < metersValue setup.markedSpanLength

/-! ## Governing standing-wave and propagation laws -/

/--
Kundt's cork-dust observation law for the depicted standing wave.

The cork piles mark displacement nodes. Consecutive displacement nodes are
separated by one half-wavelength, expressed here as twice each pile spacing
equaling the wavelength. This is a general physical law, not the requested
numerical wavelength or sound-speed conclusion.
-/
structure SatisfiesKundtStandingWaveLaw (setup : KundtTubeSetup) : Prop where
  cork_piles_are_displacement_nodes : ∀ pile,
    setup.isDisplacementNodeAt (setup.corkPileAxialPosition pile)
  adjacent_node_separation :
    ∀ (unit : LengthUnit) {left right : CorkPileLabel},
      AdjacentCorkPiles left right →
        2 *
            (lengthReadout unit (setup.corkPileAxialPosition right) -
              lengthReadout unit (setup.corkPileAxialPosition left)) =
          lengthReadout unit setup.standingWavelengthInOxygen

/--
Nondispersive acoustic propagation law `v = λ f` for the driven oxygen wave,
required in every compatible selection of length and time units.
-/
structure SatisfiesAcousticWaveSpeedLaw (setup : KundtTubeSetup) : Prop where
  speed_equals_wavelength_times_frequency :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeedInOxygen =
        lengthReadout lengthUnit setup.standingWavelengthInOxygen *
          frequencyReadout timeUnit setup.drivingFrequency

/-! ## Derived wavelength, sound speed, and displayed answer -/

/--
Because the marked arrow runs from `pile1` to `pile4`, it covers three
successive half-wavelength intervals.
-/
lemma markedSpan_is_three_halfWavelengths
    (setup : KundtTubeSetup)
    (h_figure : MatchesKundtTubeScenarioAndFigure setup)
    (h_standing : SatisfiesKundtStandingWaveLaw setup) :
    2 * metersValue setup.markedSpanLength =
      3 * metersValue setup.standingWavelengthInOxygen := by
  simp only [metersValue]
  rw [h_figure.marked_span_is_endpoint_separation LengthUnit.meters,
    h_figure.marked_span_starts_at_second_pile,
    h_figure.marked_span_ends_at_fifth_pile]
  have h₁₂ := h_standing.adjacent_node_separation LengthUnit.meters
    AdjacentCorkPiles.pile1_pile2
  have h₂₃ := h_standing.adjacent_node_separation LengthUnit.meters
    AdjacentCorkPiles.pile2_pile3
  have h₃₄ := h_standing.adjacent_node_separation LengthUnit.meters
    AdjacentCorkPiles.pile3_pile4
  linarith

/-- The `123 cm` three-interval span determines an oxygen wavelength of `0.82 m`. -/
lemma standingWavelengthInOxygen_meters_eq
    (setup : KundtTubeSetup)
    (h_figure : MatchesKundtTubeScenarioAndFigure setup)
    (h_readouts : MatchesKundtTubeNumericalReadouts setup)
    (h_physical : HasPhysicalKundtTubeParameters setup)
    (h_standing : SatisfiesKundtStandingWaveLaw setup) :
    metersValue setup.standingWavelengthInOxygen = (41 / 50 : ℝ) := by
  have h_conversion : centimetersValue setup.markedSpanLength =
      100 * metersValue setup.markedSpanLength := by
    have h_units := setup.markedSpanLength.property
      UnitChoices.SI
      { UnitChoices.SI with length := LengthUnit.centimeters }
    have h_units_real :=
      congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h_units
    norm_num [centimetersValue, metersValue, lengthReadout, UnitChoices.dimScale,
      LengthUnit.centimeters, LengthUnit.scale, LengthUnit.div_eq_val,
      LengthUnit.meters, WithDim.smul_val] at h_units_real ⊢
    exact h_units_real
  have h_span :=
    markedSpan_is_three_halfWavelengths setup h_figure h_standing
  linarith [h_conversion, h_readouts.marked_span_centimeters, h_span]

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metres-per-second value displayed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 400
  | .B => 164
  | .C => 246
  | .D => 328

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Exact agreement of a physical speed with a displayed answer value. -/
def MatchesAnswerChoice (speed : DimSpeed) (choice : AnswerChoice) : Prop :=
  metersPerSecondValue speed = choice.metersPerSecond

/--
At `400 Hz`, the `0.82 m` wavelength gives an oxygen sound speed of
`328 m/s`, which is the recorded answer D.

This formalizes `thm:physics:phyx_mini_0183:target`.
-/
theorem speedOfSoundInOxygen_is_328_metersPerSecond
    (setup : KundtTubeSetup)
    (h_figure : MatchesKundtTubeScenarioAndFigure setup)
    (h_readouts : MatchesKundtTubeNumericalReadouts setup)
    (h_physical : HasPhysicalKundtTubeParameters setup)
    (h_standing : SatisfiesKundtStandingWaveLaw setup)
    (h_wave : SatisfiesAcousticWaveSpeedLaw setup) :
    metersPerSecondValue setup.soundSpeedInOxygen = 328 ∧
      MatchesAnswerChoice setup.soundSpeedInOxygen recordedAnswerChoice := by
  have h_lambda := standingWavelengthInOxygen_meters_eq setup h_figure h_readouts
    h_physical h_standing
  have h_speed := h_wave.speed_equals_wavelength_times_frequency
    LengthUnit.meters TimeUnit.seconds
  change metersPerSecondValue setup.soundSpeedInOxygen =
    metersValue setup.standingWavelengthInOxygen *
      hertzValue setup.drivingFrequency at h_speed
  have h_frequency := h_readouts.piston_frequency_hertz
  have h_result : metersPerSecondValue setup.soundSpeedInOxygen = 328 := by
    rw [h_speed, h_lambda, h_frequency]
    norm_num
  exact ⟨h_result, by
    simpa [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.metersPerSecond]
      using h_result⟩

end PhyXMiniProblems.ProblemPhyXMini0183
