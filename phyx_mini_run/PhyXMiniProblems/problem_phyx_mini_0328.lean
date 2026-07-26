import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Sound speed from cork ridges in a resonant gas tube

This file models problem `phyx_mini_0328`.  A rod `R`, clamped at its
center, oscillates longitudinally and drives a disk `D` projecting into a
glass tube.  An adjustable plunger `P` selects a standing sound wave in the
enclosed gas.  Cork filings collect into ridges at displacement nodes, and
the primary figure labels the separation of two adjacent central ridges by
`d`.

Lengths, frequency, and speed are unit-independent Physlib quantities.  Real
numbers occur only as readouts in explicitly selected units and as the
displayed numerical answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0328

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

/-- Metre readout used for the standing wavelength and tube geometry. -/
def metersValue (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used for the stated ridge separation. -/
def centimetersValue (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Hertz readout of the rod's cyclic driving frequency. -/
def hertzValue (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Metres-per-second readout used by the requested answer. -/
def metersPerSecondValue (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Apparatus, figure labels, and geometry -/

/-- Literal labels printed in the primary figure. -/
inductive FigureLabel where
  | R
  | D
  | P
  | d
  deriving DecidableEq, Repr

/-- Physical or geometric object denoted by each printed figure label. -/
inductive FigureComponent where
  | drivingRod
  | drivingDisk
  | adjustablePlunger
  | adjacentRidgeSeparation
  deriving DecidableEq, Repr

/-- How the oscillating rod is supported. -/
inductive RodSupport where
  | clampedAtCenter
  | other
  deriving DecidableEq, Repr

/-- Direction of the rod motion that excites the gas. -/
inductive RodOscillation where
  | longitudinal
  | transverse
  deriving DecidableEq, Repr

/-- Material of the containing tube. -/
inductive TubeMaterial where
  | glass
  | other
  deriving DecidableEq, Repr

/-- Material distributed inside the tube to reveal displacement nodes. -/
inductive TracerMaterial where
  | corkFilings
  | other
  deriving DecidableEq, Repr

/-- Kind of acoustic medium occupying the resonant tube. -/
inductive AcousticMedium where
  | enclosedGas
  | other
  deriving DecidableEq, Repr

/-- The two axial ends of the resonant gas column. -/
inductive GasColumnEnd where
  | diskEnd
  | plungerEnd
  deriving DecidableEq, Repr

/-- Boundary apparatus at either axial end of the gas column. -/
inductive BoundaryApparatus where
  | projectingDrivingDisk
  | movablePlunger
  deriving DecidableEq, Repr

/-- The four cork ridges visible from left to right in the primary figure. -/
inductive CorkRidgeLabel where
  | ridge0
  | ridge1
  | ridge2
  | ridge3
  deriving DecidableEq, Repr

/-- Consecutive cork ridges in the left-to-right order shown in the figure. -/
inductive AdjacentCorkRidges : CorkRidgeLabel → CorkRidgeLabel → Prop where
  | ridge0_ridge1 : AdjacentCorkRidges .ridge0 .ridge1
  | ridge1_ridge2 : AdjacentCorkRidges .ridge1 .ridge2
  | ridge2_ridge3 : AdjacentCorkRidges .ridge2 .ridge3

/-!
The physical resonant-tube setup.  The sound speed and wavelength are
independent fields: neither is assigned the answer value here.
-/
structure ResonantGasTubeSetup where
  figureLabelTarget : FigureLabel → FigureComponent
  rodSupport : RodSupport
  rodOscillation : RodOscillation
  tubeMaterial : TubeMaterial
  tracerMaterial : TracerMaterial
  acousticMedium : AcousticMedium
  boundaryAt : GasColumnEnd → BoundaryApparatus
  diskIsAttachedAtRodEnd : Prop
  diskProjectsIntoTube : Prop
  plungerPositionIsAdjustable : Prop
  standingWaveIsEstablished : Prop
  gasColumnLength : AcousticLength
  drivingFrequency : AcousticFrequency
  soundSpeedInGas : DimSpeed
  standingWavelengthInGas : AcousticLength
  corkRidgeAxialPosition : CorkRidgeLabel → AcousticLength
  isDisplacementNodeAt : AcousticLength → Prop
  markedSeparationStartRidge : CorkRidgeLabel
  markedSeparationEndRidge : CorkRidgeLabel
  markedRidgeSeparation : AcousticLength

/-- The depicted ridges occur in strict left-to-right axial order. -/
def CorkRidgesAreStrictlyOrdered (setup : ResonantGasTubeSetup) : Prop :=
  metersValue (setup.corkRidgeAxialPosition .ridge0) <
      metersValue (setup.corkRidgeAxialPosition .ridge1) ∧
    metersValue (setup.corkRidgeAxialPosition .ridge1) <
      metersValue (setup.corkRidgeAxialPosition .ridge2) ∧
    metersValue (setup.corkRidgeAxialPosition .ridge2) <
      metersValue (setup.corkRidgeAxialPosition .ridge3)

/-!
Qualitative apparatus information and geometry read from the problem and the
primary figure.  The `d` marker spans the two central adjacent ridges.  Its
numerical `9.20 cm` readout is recorded separately.
-/
structure MatchesResonantTubeScenarioAndFigure
    (setup : ResonantGasTubeSetup) : Prop where
  label_R_is_rod : setup.figureLabelTarget .R = .drivingRod
  label_D_is_disk : setup.figureLabelTarget .D = .drivingDisk
  label_P_is_plunger : setup.figureLabelTarget .P = .adjustablePlunger
  label_d_is_ridge_separation :
    setup.figureLabelTarget .d = .adjacentRidgeSeparation
  rod_is_clamped_at_center : setup.rodSupport = .clampedAtCenter
  rod_oscillates_longitudinally : setup.rodOscillation = .longitudinal
  tube_is_glass : setup.tubeMaterial = .glass
  tracer_is_cork_filings : setup.tracerMaterial = .corkFilings
  tube_is_filled_with_gas : setup.acousticMedium = .enclosedGas
  disk_is_at_driven_end :
    setup.boundaryAt .diskEnd = .projectingDrivingDisk
  plunger_is_at_other_end : setup.boundaryAt .plungerEnd = .movablePlunger
  disk_is_attached_at_rod_end : setup.diskIsAttachedAtRodEnd
  disk_projects_into_tube : setup.diskProjectsIntoTube
  plunger_is_adjustable : setup.plungerPositionIsAdjustable
  standing_wave_is_established : setup.standingWaveIsEstablished
  ridges_are_ordered : CorkRidgesAreStrictlyOrdered setup
  all_ridges_lie_in_gas_column : ∀ ridge,
    metersValue (setup.corkRidgeAxialPosition ridge) ≤
      metersValue setup.gasColumnLength
  marked_separation_starts_at_second_ridge :
    setup.markedSeparationStartRidge = .ridge1
  marked_separation_ends_at_third_ridge :
    setup.markedSeparationEndRidge = .ridge2
  marked_ridges_are_adjacent :
    AdjacentCorkRidges
      setup.markedSeparationStartRidge setup.markedSeparationEndRidge
  marked_separation_is_endpoint_difference : ∀ unit : LengthUnit,
    lengthReadout unit setup.markedRidgeSeparation =
      lengthReadout unit
          (setup.corkRidgeAxialPosition setup.markedSeparationEndRidge) -
        lengthReadout unit
          (setup.corkRidgeAxialPosition setup.markedSeparationStartRidge)

/-- Numerical measurements stated in the problem. -/
structure MatchesResonantTubeNumericalReadouts
    (setup : ResonantGasTubeSetup) : Prop where
  driving_frequency_hertz : hertzValue setup.drivingFrequency = 4460
  adjacent_ridge_separation_centimeters :
    centimetersValue setup.markedRidgeSeparation = 46 / 5

/-- Positivity and containment conditions for the physical apparatus. -/
def HasPhysicalResonantTubeParameters (setup : ResonantGasTubeSetup) : Prop :=
  0 < metersValue setup.gasColumnLength ∧
    0 < hertzValue setup.drivingFrequency ∧
    0 < metersPerSecondValue setup.soundSpeedInGas ∧
    0 < metersValue setup.standingWavelengthInGas ∧
    0 < metersValue setup.markedRidgeSeparation

/-! ## Governing standing-wave and propagation laws -/

/-!
Cork-ridge observation law for this standing sound wave.  The ridges mark
displacement nodes, and consecutive displacement nodes are separated by one
half-wavelength.  This is a general standing-wave law and does not assign a
numerical wavelength or speed.
-/
structure SatisfiesCorkRidgeStandingWaveLaw
    (setup : ResonantGasTubeSetup) : Prop where
  cork_ridges_are_displacement_nodes : ∀ ridge,
    setup.isDisplacementNodeAt (setup.corkRidgeAxialPosition ridge)
  adjacent_node_separation :
    ∀ (unit : LengthUnit) {left right : CorkRidgeLabel},
      AdjacentCorkRidges left right →
        2 *
            (lengthReadout unit (setup.corkRidgeAxialPosition right) -
              lengthReadout unit (setup.corkRidgeAxialPosition left)) =
          lengthReadout unit setup.standingWavelengthInGas

/-!
Nondispersive acoustic propagation law `v = λ f` for the driven gas wave,
required in every compatible selection of length and time units.
-/
structure SatisfiesAcousticWaveSpeedLaw
    (setup : ResonantGasTubeSetup) : Prop where
  speed_equals_wavelength_times_frequency :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeedInGas =
        lengthReadout lengthUnit setup.standingWavelengthInGas *
          frequencyReadout timeUnit setup.drivingFrequency

/-! ## Derived wavelength, sound speed, and displayed answer -/

/-- The marked adjacent-ridge separation is one half-wavelength. -/
lemma markedRidgeSeparation_is_halfWavelength
    (setup : ResonantGasTubeSetup)
    (h_figure : MatchesResonantTubeScenarioAndFigure setup)
    (h_standing : SatisfiesCorkRidgeStandingWaveLaw setup) :
    2 * metersValue setup.markedRidgeSeparation =
      metersValue setup.standingWavelengthInGas := by
  rw [metersValue,
    h_figure.marked_separation_is_endpoint_difference LengthUnit.meters]
  exact h_standing.adjacent_node_separation LengthUnit.meters
    h_figure.marked_ridges_are_adjacent

/-- A `9.20 cm` node spacing determines a wavelength of `0.184 m`. -/
lemma standingWavelengthInGas_meters_eq
    (setup : ResonantGasTubeSetup)
    (h_figure : MatchesResonantTubeScenarioAndFigure setup)
    (h_readouts : MatchesResonantTubeNumericalReadouts setup)
    (h_physical : HasPhysicalResonantTubeParameters setup)
    (h_standing : SatisfiesCorkRidgeStandingWaveLaw setup) :
    metersValue setup.standingWavelengthInGas = (23 / 125 : ℝ) := by
  have centimeters_eq_one_hundred_meters (length : AcousticLength) :
      centimetersValue length = 100 * metersValue length := by
    change
      ((length {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) =
        100 * ((length UnitChoices.SI).val : ℝ)
    rw [length.2 UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices)]
    have h_scale :
        UnitChoices.dimScale UnitChoices.SI
          ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices)
          (dim (WithDim L𝓭 NNReal)) = 100 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    rw [h_scale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have h_separation_meters :
      metersValue setup.markedRidgeSeparation = (23 / 250 : ℝ) := by
    have h_readout :=
      h_readouts.adjacent_ridge_separation_centimeters
    rw [centimeters_eq_one_hundred_meters] at h_readout
    norm_num at h_readout ⊢
    linarith
  have h_half :=
    markedRidgeSeparation_is_halfWavelength setup h_figure h_standing
  rw [h_separation_meters] at h_half
  norm_num at h_half ⊢
  linarith

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metres-per-second value displayed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 756
  | .B => 778
  | .C => 793
  | .D => 821

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement after rounding a physical speed to the nearest whole m/s. -/
def RoundsToDisplayedSpeed
    (setup : ResonantGasTubeSetup) (choice : AnswerChoice) : Prop :=
  |metersPerSecondValue setup.soundSpeedInGas - choice.metersPerSecond| < 1 / 2

/-- A choice is the unique displayed value to which the physical speed rounds. -/
def IsUniqueRoundedDisplayedAnswer
    (setup : ResonantGasTubeSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedSpeed setup choice ∧
    ∀ otherChoice : AnswerChoice,
      RoundsToDisplayedSpeed setup otherChoice → otherChoice = choice

/-!
At `4.46 × 10^3 Hz`, the `0.184 m` wavelength gives the exact speed
`820.64 m/s = 20516/25 m/s`.  This rounds uniquely to `821 m/s`, displayed as
the recorded answer D.

This formalizes `thm:physics:phyx_mini_0328:target`.
-/
theorem problem_phyx_mini_0328
    (setup : ResonantGasTubeSetup)
    (h_figure : MatchesResonantTubeScenarioAndFigure setup)
    (h_readouts : MatchesResonantTubeNumericalReadouts setup)
    (h_physical : HasPhysicalResonantTubeParameters setup)
    (h_standing : SatisfiesCorkRidgeStandingWaveLaw setup)
    (h_wave : SatisfiesAcousticWaveSpeedLaw setup) :
    metersPerSecondValue setup.soundSpeedInGas = (20516 / 25 : ℝ) ∧
      IsUniqueRoundedDisplayedAnswer setup recordedDatasetAnswer := by
  have h_wavelength :=
    standingWavelengthInGas_meters_eq setup h_figure h_readouts h_physical
      h_standing
  have h_speed_law :=
    h_wave.speed_equals_wavelength_times_frequency
      LengthUnit.meters TimeUnit.seconds
  have h_speed :
      metersPerSecondValue setup.soundSpeedInGas = (20516 / 25 : ℝ) := by
    change
      metersPerSecondValue setup.soundSpeedInGas =
        metersValue setup.standingWavelengthInGas *
          hertzValue setup.drivingFrequency at h_speed_law
    rw [h_wavelength, h_readouts.driving_frequency_hertz] at h_speed_law
    norm_num at h_speed_law ⊢
    exact h_speed_law
  refine ⟨h_speed, ?_⟩
  constructor
  · norm_num [RoundsToDisplayedSpeed, recordedDatasetAnswer,
      AnswerChoice.metersPerSecond, h_speed]
  · intro otherChoice h_other
    cases otherChoice with
    | A =>
        norm_num [RoundsToDisplayedSpeed, AnswerChoice.metersPerSecond,
          h_speed] at h_other
    | B =>
        norm_num [RoundsToDisplayedSpeed, AnswerChoice.metersPerSecond,
          h_speed] at h_other
    | C =>
        norm_num [RoundsToDisplayedSpeed, AnswerChoice.metersPerSecond,
          h_speed] at h_other
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0328
