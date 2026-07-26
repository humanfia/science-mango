import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0210

open Dimension

/-!
# Resonant frequency of an overpass after adding a center support

An overpass initially resonates in a single half-wavelength loop when vertical
ground motion drives it at `3.0 Hz`.  A new support then anchors the midpoint of
the otherwise unchanged deck to the ground.  The new lowest standing-wave mode
has one loop on each of the two support intervals.

Lengths, frequencies, and wave speeds are represented by dimensionful Physlib
quantities.  Real numbers below are scalar readouts in a coherent unit system;
in particular, the inverse-second readout in `UnitChoices.SI` is in hertz.
-/

/-! ## Dimensionful physical quantities -/

/-- A physical longitudinal length or position along the overpass. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- An ordinary physical frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical wave-propagation speed in the overpass deck. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Scalar readout of a physical length in a coherent unit system. -/
def lengthReadout (units : UnitChoices) (quantity : LengthQuantity) : ℝ :=
  (quantity units).val

/-- Scalar readout of an ordinary frequency in a coherent unit system. -/
def frequencyReadout (units : UnitChoices) (quantity : FrequencyQuantity) : ℝ :=
  (quantity units).val

/-- Scalar readout of Physlib's nonnegative speed quantity. -/
def speedReadout (units : UnitChoices) (quantity : SpeedQuantity) : ℝ :=
  ((quantity units).val : ℝ)

/-! ## Configurations, figure labels, and setup -/

/-- The two panels explicitly labeled in the supplied figure. -/
inductive OverpassConfiguration where
  | beforeModification
  | afterModification
  deriving DecidableEq, Repr

/-- Longitudinal sites at which the figure may show a support. -/
inductive SupportSite where
  | leftEnd
  | midpoint
  | rightEnd
  deriving DecidableEq, Repr

/-- Mechanical support visible at a site in a given panel. -/
inductive SupportKind where
  | endSupport
  | addedGroundAnchor
  | absent
  deriving DecidableEq, Repr

/-- Transverse-displacement condition of a standing mode at a marked site. -/
inductive TransverseBoundaryCondition where
  | node
  | unconstrained
  deriving DecidableEq, Repr

/-- Direction of the earthquake's ground displacement. -/
inductive GroundMotionDirection where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Qualitative source of the external drive in the problem statement. -/
inductive ExcitationSource where
  | smallEarthquake
  | other
  deriving DecidableEq, Repr

/-- Text labels printed on the two panels and the new support. -/
inductive FigureLabel where
  | beforeModification
  | afterModification
  | addedSupport
  deriving DecidableEq, Repr

/-- Figure elements to which the printed labels point. -/
inductive FigureElement where
  | beforePanel
  | afterPanel
  | midpointSupport
  deriving DecidableEq, Repr

/--
Physical quantities and figure-indexed data for the overpass.

`halfWavelengthLoopCount` counts node-to-node loops across the entire deck.
The resonant frequency fields are unconstrained here: in particular, the
post-modification frequency is not built into the setup.
-/
structure OverpassResonanceSetup where
  excitationSource : ExcitationSource
  groundMotionDirection : GroundMotionDirection
  requestedConfiguration : OverpassConfiguration
  spanLength : LengthQuantity
  longitudinalPosition : SupportSite → LengthQuantity
  supportKind : OverpassConfiguration → SupportSite → SupportKind
  transverseBoundary :
    OverpassConfiguration → SupportSite → TransverseBoundaryCondition
  supportIntervalCount : OverpassConfiguration → ℕ
  halfWavelengthLoopCount : OverpassConfiguration → ℕ
  standingWavelength : OverpassConfiguration → LengthQuantity
  resonantFrequency : OverpassConfiguration → FrequencyQuantity
  waveSpeed : OverpassConfiguration → SpeedQuantity
  figureLabelTarget : FigureLabel → FigureElement

/-! ## Problem data and primary-figure readouts -/

/--
Data stated in the prose: the drive is a small earthquake with vertical ground
motion, the observed initial mode is one half-wavelength loop at `3.0 Hz`, and
the requested resonance is the one after modification.
-/
structure MatchesProblemDescription (setup : OverpassResonanceSetup) : Prop where
  source_is_small_earthquake : setup.excitationSource = .smallEarthquake
  ground_motion_is_vertical : setup.groundMotionDirection = .vertical
  initial_mode_is_one_loop :
    setup.halfWavelengthLoopCount .beforeModification = 1
  initial_resonant_frequency_hz :
    frequencyReadout UnitChoices.SI
        (setup.resonantFrequency .beforeModification) = 3
  asks_for_modified_resonance :
    setup.requestedConfiguration = .afterModification

/--
Readouts from the supplied image.  Both panels show the same deck and its two
end supports.  The center site is empty before modification and is a grounded
support afterward.  Its longitudinal coordinate is exactly the midpoint, so
the support divides the deck into two intervals.  The three printed labels are
also recorded explicitly.
-/
structure MatchesPrimaryFigure (setup : OverpassResonanceSetup) : Prop where
  left_end_at_origin :
    ∀ units,
      lengthReadout units (setup.longitudinalPosition .leftEnd) = 0
  right_end_at_span :
    ∀ units,
      lengthReadout units (setup.longitudinalPosition .rightEnd) =
        lengthReadout units setup.spanLength
  added_support_at_midpoint :
    ∀ units,
      lengthReadout units (setup.longitudinalPosition .midpoint) =
        lengthReadout units setup.spanLength / 2
  before_left_end_support :
    setup.supportKind .beforeModification .leftEnd = .endSupport
  before_center_is_open :
    setup.supportKind .beforeModification .midpoint = .absent
  before_right_end_support :
    setup.supportKind .beforeModification .rightEnd = .endSupport
  after_left_end_support :
    setup.supportKind .afterModification .leftEnd = .endSupport
  after_center_is_ground_anchor :
    setup.supportKind .afterModification .midpoint = .addedGroundAnchor
  after_right_end_support :
    setup.supportKind .afterModification .rightEnd = .endSupport
  before_has_one_support_interval :
    setup.supportIntervalCount .beforeModification = 1
  after_has_two_support_intervals :
    setup.supportIntervalCount .afterModification = 2
  before_panel_label :
    setup.figureLabelTarget .beforeModification = .beforePanel
  after_panel_label :
    setup.figureLabelTarget .afterModification = .afterPanel
  added_support_label :
    setup.figureLabelTarget .addedSupport = .midpointSupport

/-- Positivity conditions selecting nondegenerate overpass modes. -/
structure HasPhysicalOverpassParameters (setup : OverpassResonanceSetup) : Prop where
  span_length_positive :
    0 < lengthReadout UnitChoices.SI setup.spanLength
  support_interval_count_positive :
    ∀ configuration, 0 < setup.supportIntervalCount configuration
  loop_count_positive :
    ∀ configuration, 0 < setup.halfWavelengthLoopCount configuration
  wavelength_positive :
    ∀ configuration,
      0 < lengthReadout UnitChoices.SI
        (setup.standingWavelength configuration)
  resonant_frequency_positive :
    ∀ configuration,
      0 < frequencyReadout UnitChoices.SI
        (setup.resonantFrequency configuration)
  wave_speed_positive :
    ∀ configuration,
      0 < speedReadout UnitChoices.SI (setup.waveSpeed configuration)

/-! ## Governing resonance laws -/

/--
Standing-wave laws for the lowest mode compatible with the supports:

* every mechanical support anchors a transverse-displacement node;
* the lowest mode has one half-wavelength loop on each support interval;
* `n λ = 2 L` for `n` loops across a deck of length `L`;
* wave kinematics gives `v = f λ`;
* adding the ideal support does not change the deck's propagation speed.

These are generic physical/modeling relations.  None states the requested
post-modification frequency or names an answer choice.
-/
structure SatisfiesOverpassStandingWaveLaws
    (setup : OverpassResonanceSetup) : Prop where
  fixed_supports_are_nodes :
    ∀ configuration site,
      setup.supportKind configuration site ≠ .absent →
        setup.transverseBoundary configuration site = .node
  lowest_mode_has_one_loop_per_interval :
    ∀ configuration,
      setup.halfWavelengthLoopCount configuration =
        setup.supportIntervalCount configuration
  fixed_support_standing_wave_law :
    ∀ configuration units,
      (setup.halfWavelengthLoopCount configuration : ℝ) *
          lengthReadout units (setup.standingWavelength configuration) =
        2 * lengthReadout units setup.spanLength
  wave_kinematics :
    ∀ configuration units,
      speedReadout units (setup.waveSpeed configuration) =
        frequencyReadout units (setup.resonantFrequency configuration) *
          lengthReadout units (setup.standingWavelength configuration)
  unchanged_deck_wave_speed :
    ∀ units,
      speedReadout units (setup.waveSpeed .beforeModification) =
        speedReadout units (setup.waveSpeed .afterModification)

/-! ## Consequences and displayed answer -/

/--
The added midpoint node makes the lowest compatible mode contain two loops,
one on each half of the overpass.
-/
lemma postModificationLoopCount_eq_two
    (setup : OverpassResonanceSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_laws : SatisfiesOverpassStandingWaveLaws setup) :
    setup.halfWavelengthLoopCount .afterModification = 2 := by
  calc
    setup.halfWavelengthLoopCount .afterModification =
        setup.supportIntervalCount .afterModification :=
      _laws.lowest_mode_has_one_loop_per_interval .afterModification
    _ = 2 := _figure.after_has_two_support_intervals

/--
The wavelength of the new lowest mode is half the wavelength of the observed
one-loop mode before modification.
-/
lemma twice_postModificationWavelength_eq_beforeModificationWavelength
    (setup : OverpassResonanceSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalOverpassParameters setup)
    (_laws : SatisfiesOverpassStandingWaveLaws setup)
    (units : UnitChoices) :
    2 * lengthReadout units
          (setup.standingWavelength .afterModification) =
      lengthReadout units
        (setup.standingWavelength .beforeModification) := by
  have hBefore :=
    _laws.fixed_support_standing_wave_law .beforeModification units
  have hAfter :=
    _laws.fixed_support_standing_wave_law .afterModification units
  rw [_description.initial_mode_is_one_loop] at hBefore
  rw [postModificationLoopCount_eq_two setup _figure _laws] at hAfter
  norm_num at hBefore hAfter
  linarith

/--
With unchanged wave speed and `v = f λ`, halving the wavelength doubles the
ordinary resonant frequency.
-/
lemma postModificationFrequency_eq_twice_beforeModificationFrequency
    (setup : OverpassResonanceSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalOverpassParameters setup)
    (_laws : SatisfiesOverpassStandingWaveLaws setup)
    (units : UnitChoices) :
    frequencyReadout units (setup.resonantFrequency .afterModification) =
      2 * frequencyReadout units
        (setup.resonantFrequency .beforeModification) := by
  have hWavelength :=
    twice_postModificationWavelength_eq_beforeModificationWavelength
      setup _description _figure _physical _laws units
  have hBeforeKinematics :=
    _laws.wave_kinematics .beforeModification units
  have hAfterKinematics :=
    _laws.wave_kinematics .afterModification units
  have hUnchangedSpeed := _laws.unchanged_deck_wave_speed units
  have hAfterWavelengthPositive :
      0 < lengthReadout units
        (setup.standingWavelength .afterModification) := by
    have hSI :=
      _physical.wavelength_positive .afterModification
    unfold lengthReadout at hSI ⊢
    rw [(setup.standingWavelength .afterModification).property
      UnitChoices.SI units]
    simp only [WithDim.smul_val, NNReal.smul_def]
    exact mul_pos
      (by
        exact_mod_cast
          UnitChoices.dimScale_pos UnitChoices.SI units L𝓭)
      hSI
  have hProduct :
      frequencyReadout units
            (setup.resonantFrequency .afterModification) *
          lengthReadout units
            (setup.standingWavelength .afterModification) =
        (2 * frequencyReadout units
            (setup.resonantFrequency .beforeModification)) *
          lengthReadout units
            (setup.standingWavelength .afterModification) := by
    calc
      frequencyReadout units
              (setup.resonantFrequency .afterModification) *
            lengthReadout units
              (setup.standingWavelength .afterModification) =
          speedReadout units
            (setup.waveSpeed .afterModification) :=
        hAfterKinematics.symm
      _ = speedReadout units
            (setup.waveSpeed .beforeModification) :=
        hUnchangedSpeed.symm
      _ = frequencyReadout units
              (setup.resonantFrequency .beforeModification) *
            lengthReadout units
              (setup.standingWavelength .beforeModification) :=
        hBeforeKinematics
      _ = frequencyReadout units
              (setup.resonantFrequency .beforeModification) *
            (2 * lengthReadout units
              (setup.standingWavelength .afterModification)) := by
        rw [hWavelength]
      _ = (2 * frequencyReadout units
              (setup.resonantFrequency .beforeModification)) *
            lengthReadout units
              (setup.standingWavelength .afterModification) := by
        ring
  exact mul_right_cancel₀ (ne_of_gt hAfterWavelengthPositive) hProduct

/-- Labels of the four answer choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each answer choice. -/
def AnswerChoice.frequencyHz : AnswerChoice → ℝ
  | .A => 4
  | .B => 10
  | .C => 8
  | .D => 6

/-- An answer choice matches the requested post-modification SI frequency. -/
def IsCorrectFrequencyAnswer
    (setup : OverpassResonanceSetup) (choice : AnswerChoice) : Prop :=
  frequencyReadout UnitChoices.SI
      (setup.resonantFrequency setup.requestedConfiguration) =
    choice.frequencyHz

/--
The midpoint ground anchor doubles the lowest resonant frequency from
`3.0 Hz` to `6.0 Hz`, so the recorded answer is choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0210:target`.
-/
theorem problem_phyx_mini_0210
    (setup : OverpassResonanceSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalOverpassParameters setup)
    (_laws : SatisfiesOverpassStandingWaveLaws setup) :
    frequencyReadout UnitChoices.SI
          (setup.resonantFrequency .afterModification) = 6 ∧
      IsCorrectFrequencyAnswer setup .D := by
  have hFrequency :=
    postModificationFrequency_eq_twice_beforeModificationFrequency
      setup _description _figure _physical _laws UnitChoices.SI
  have hModified :
      frequencyReadout UnitChoices.SI
          (setup.resonantFrequency .afterModification) = 6 := by
    rw [_description.initial_resonant_frequency_hz] at hFrequency
    norm_num at hFrequency ⊢
    exact hFrequency
  refine ⟨hModified, ?_⟩
  simpa [IsCorrectFrequencyAnswer,
    _description.asks_for_modified_resonance,
    AnswerChoice.frequencyHz] using hModified

end PhyXMiniProblems.ProblemPhyXMini0210
