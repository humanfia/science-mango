import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0187

open Dimension

/-!
# Delayed two-antenna directional broadcasting

Two parallel AM antennas lie on one spatial axis. Antenna 1 is at `x = 0`,
antenna 2 is at `x = L`, the country is to the left, and the town is to the
right. Both antennas emit sinusoidal waves with the same amplitude,
wavelength, and period. Antenna 2 has an adjustable delay and hence an
adjustable initial phase.

Lengths, durations, and frequencies are unit-independent Physlib quantities.
Coordinates and times enter the displayed traveling-wave formulas through
readouts in a common system of units. Wave amplitude and phase are scalar
readouts because the source does not state a physical unit for the plotted
wave ordinate, while phases are dimensionless radian values.
-/

/-- A real-valued physical length, independent of the chosen unit readout. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A real-valued physical duration, independent of the chosen unit readout. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A real-valued physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Read a physical length as a real number in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a physical duration as a real number in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  (duration {UnitChoices.SI with time := unit}).val

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  (frequency {UnitChoices.SI with time := unit}).val

/-- Meter readout used in the traveling-wave and phase-propagation formulas. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout used for the period and broadcast-delay laws. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Nanosecond readout used by the four displayed answer choices. -/
def durationInNanoseconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.nanoseconds duration

/-- Kilohertz readout: inverse milliseconds are kilohertz. -/
def frequencyInKilohertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.milliseconds frequency

/-- The two labeled antennas in the figure. -/
inductive AntennaLabel where
  | antenna1
  | antenna2
  deriving DecidableEq, Repr

/-- The two axial propagation directions shown by the arrows. -/
inductive PropagationDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The two service regions on opposite sides of the antenna pair. -/
inductive ServiceRegion where
  | country
  | town
  deriving DecidableEq, Repr

/-- The four wave labels printed in the figure. -/
inductive RadiatedWaveLabel where
  | D1Left
  | D1Right
  | D2Left
  | D2Right
  deriving DecidableEq, Repr

/-- The source antenna denoted by each printed wave label. -/
def RadiatedWaveLabel.source : RadiatedWaveLabel → AntennaLabel
  | .D1Left => .antenna1
  | .D1Right => .antenna1
  | .D2Left => .antenna2
  | .D2Right => .antenna2

/-- The propagation direction denoted by each printed wave label. -/
def RadiatedWaveLabel.direction : RadiatedWaveLabel → PropagationDirection
  | .D1Left => .left
  | .D1Right => .right
  | .D2Left => .left
  | .D2Right => .right

/-- Sign of the spatial phase term for a right- or left-traveling wave. -/
def PropagationDirection.spatialSign : PropagationDirection → ℝ
  | .left => -1
  | .right => 1

/-!
The physical setup. The delay and phase offset are unknown fields: neither is
assigned its requested numerical value. The displacement function records the
four emitted waves as scalar amplitude readouts at physical positions and
times.
-/
structure DirectionalAntennaArraySetup where
  amplitudeReadout : ℝ
  wavelength : LengthQuantity
  period : DurationQuantity
  carrierFrequency : FrequencyQuantity
  antennaSeparation : LengthQuantity
  antennaPosition : AntennaLabel → LengthQuantity
  antennaTwoBroadcastDelay : DurationQuantity
  antennaTwoInitialPhaseRadians : ℝ
  regionInDirection : PropagationDirection → ServiceRegion
  displacementReadout :
    RadiatedWaveLabel → LengthQuantity → DurationQuantity → ℝ

/-- Source phase at the reference time; antenna 1 fixes the zero of phase. -/
def sourcePhaseRadians
    (setup : DirectionalAntennaArraySetup) : AntennaLabel → ℝ
  | .antenna1 => 0
  | .antenna2 => setup.antennaTwoInitialPhaseRadians

/-!
The qualitative and coordinate information in the problem and primary image:
antenna 1 is at the origin, antenna 2 is at `x = L`, country is left, and town
is right. No delay or phase value appears here.
-/
structure MatchesScenarioAndFigure
    (setup : DirectionalAntennaArraySetup) : Prop where
  antennaOneAtOrigin :
    lengthInMeters (setup.antennaPosition .antenna1) = 0
  antennaTwoAtSeparation :
    lengthInMeters (setup.antennaPosition .antenna2) =
      lengthInMeters setup.antennaSeparation
  countryIsLeft : setup.regionInDirection .left = .country
  townIsRight : setup.regionInDirection .right = .town

/-- The numerical carrier-frequency datum stated in the question. -/
structure HasStatedCarrierFrequency
    (setup : DirectionalAntennaArraySetup) : Prop where
  frequencyKilohertz : frequencyInKilohertz setup.carrierFrequency = 1000

/-- Positivity and nondegeneracy conditions for the physical wave system. -/
structure HasPhysicalWaveParameters
    (setup : DirectionalAntennaArraySetup) : Prop where
  amplitudeNonzero : setup.amplitudeReadout ≠ 0
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  periodPositive : 0 < durationInSeconds setup.period
  frequencyPositive : 0 < frequencyInKilohertz setup.carrierFrequency
  separationPositive : 0 < lengthInMeters setup.antennaSeparation
  delayNonnegative : 0 ≤ durationInSeconds setup.antennaTwoBroadcastDelay

/-!
The traveling-wave value predicted from the source, direction, common
wavelength `lambda`, and common period `T`. For antenna 1 at zero this expands
to the two formulas `a sin(2 pi (x/lambda - t/T))` and
`a sin(2 pi (-x/lambda - t/T))`. For antenna 2 at `L`, it expands to the two
corresponding formulas in `x - L` with the added phase `phi_20`.
-/
def idealTravelingWaveReadout
    (setup : DirectionalAntennaArraySetup)
    (wave : RadiatedWaveLabel) (position : LengthQuantity)
    (time : DurationQuantity) : ℝ :=
  setup.amplitudeReadout * Real.sin
    (2 * Real.pi *
        (wave.direction.spatialSign *
            ((lengthInMeters position -
                lengthInMeters (setup.antennaPosition wave.source)) /
              lengthInMeters setup.wavelength) -
          durationInSeconds time / durationInSeconds setup.period) +
      sourcePhaseRadians setup wave.source)

/-!
Governing laws for the monochromatic sources. The first field asserts all four
given sine-wave equations. The second is `f T = 1` in any time unit. Because
the displayed wave phase contains `-t/T`, delaying antenna 2 by `Delta t`
adds the phase `2 pi Delta t/T`, as recorded by the third field.
-/
structure SatisfiesDelayedTravelingWaveLaws
    (setup : DirectionalAntennaArraySetup) : Prop where
  emittedWaveform : ∀ wave position time,
    setup.displacementReadout wave position time =
      idealTravelingWaveReadout setup wave position time
  frequencyPeriodRelation : ∀ unit : TimeUnit,
    frequencyReadout unit setup.carrierFrequency *
      durationReadout unit setup.period = 1
  delayPhaseRelation : ∀ unit : TimeUnit,
    setup.antennaTwoInitialPhaseRadians =
      2 * Real.pi *
        durationReadout unit setup.antennaTwoBroadcastDelay /
          durationReadout unit setup.period

/-- Relative phase of antenna 2 versus antenna 1 on the town (right) side. -/
def townRelativePhaseRadians (setup : DirectionalAntennaArraySetup) : ℝ :=
  setup.antennaTwoInitialPhaseRadians -
    2 * Real.pi *
      lengthInMeters setup.antennaSeparation /
        lengthInMeters setup.wavelength

/-- Relative phase of antenna 2 versus antenna 1 on the country (left) side. -/
def countryRelativePhaseRadians (setup : DirectionalAntennaArraySetup) : ℝ :=
  setup.antennaTwoInitialPhaseRadians +
    2 * Real.pi *
      lengthInMeters setup.antennaSeparation /
        lengthInMeters setup.wavelength

/-!
The directional-interference design requirement. Equal-phase waves on the
town side differ by an integer number of full turns; opposite-phase waves on
the country side differ by an odd number of half turns. The orders are not
fixed to values that encode the requested delay.
-/
def SatisfiesDirectionalInterferenceDesign
    (setup : DirectionalAntennaArraySetup) : Prop :=
  ∃ townInterferenceOrder countryInterferenceOrder : ℤ,
    townRelativePhaseRadians setup =
        2 * Real.pi * (townInterferenceOrder : ℝ) ∧
      countryRelativePhaseRadians setup =
        (2 * (countryInterferenceOrder : ℝ) + 1) * Real.pi

/-!
Selection of the shortest positive antenna spacing and the principal positive
phase setting. These range conditions select the standard design branch
without assuming either a quarter wavelength or a quarter period.
-/
structure UsesPrincipalShortestSpacingBranch
    (setup : DirectionalAntennaArraySetup) : Prop where
  separationBelowHalfWavelength :
    lengthInMeters setup.antennaSeparation <
      lengthInMeters setup.wavelength / 2
  phasePositive : 0 < setup.antennaTwoInitialPhaseRadians
  phaseBelowFullTurn :
    setup.antennaTwoInitialPhaseRadians < 2 * Real.pi

/-- The four delay choices displayed in the question, in nanoseconds. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Nanosecond delay printed beside each answer label. -/
def displayedDelayNanoseconds : AnswerChoice → ℝ
  | .A => 500
  | .B => 125
  | .C => 100
  | .D => 250

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A physical antenna delay agrees with the value displayed for a choice. -/
def MatchesAnswerChoice
    (setup : DirectionalAntennaArraySetup) (choice : AnswerChoice) : Prop :=
  durationInNanoseconds setup.antennaTwoBroadcastDelay =
    displayedDelayNanoseconds choice

/-!
The principal constructive/destructive branch has quarter-wavelength spacing
and a quarter-turn initial phase. This is an intermediate consequence of the
two interference conditions and range restrictions, not an input premise.
-/
lemma principal_design_is_quarter_wavelength_and_phase
    (setup : DirectionalAntennaArraySetup)
    (hphysical : HasPhysicalWaveParameters setup)
    (hinterference : SatisfiesDirectionalInterferenceDesign setup)
    (hprincipal : UsesPrincipalShortestSpacingBranch setup) :
    lengthInMeters setup.antennaSeparation =
        lengthInMeters setup.wavelength / 4 ∧
      setup.antennaTwoInitialPhaseRadians = Real.pi / 2 := by
  rcases hinterference with ⟨m, n, hm, hn⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have hw : 0 < lengthInMeters setup.wavelength :=
    hphysical.wavelengthPositive
  have hs : 0 < lengthInMeters setup.antennaSeparation :=
    hphysical.separationPositive
  have hr_pos :
      0 < lengthInMeters setup.antennaSeparation /
        lengthInMeters setup.wavelength :=
    div_pos hs hw
  have hr_lt :
      lengthInMeters setup.antennaSeparation /
          lengthInMeters setup.wavelength <
        (1 : ℝ) / 2 := by
    apply (div_lt_iff₀ hw).2
    nlinarith [hprincipal.separationBelowHalfWavelength]
  have hq_pos :
      0 < 2 * Real.pi * lengthInMeters setup.antennaSeparation /
        lengthInMeters setup.wavelength :=
    div_pos (mul_pos (mul_pos (by norm_num) hpi) hs) hw
  have hpi_gap :
      0 < Real.pi *
        ((1 : ℝ) / 2 -
          lengthInMeters setup.antennaSeparation /
            lengthInMeters setup.wavelength) :=
    mul_pos hpi (sub_pos.mpr hr_lt)
  have hq_lt :
      2 * Real.pi * lengthInMeters setup.antennaSeparation /
          lengthInMeters setup.wavelength <
        Real.pi := by
    have hrewrite :
        2 * Real.pi * lengthInMeters setup.antennaSeparation /
            lengthInMeters setup.wavelength =
          2 * Real.pi *
            (lengthInMeters setup.antennaSeparation /
              lengthInMeters setup.wavelength) := by
      ring
    rw [hrewrite]
    nlinarith [hpi_gap]
  have hm_lower : -Real.pi < 2 * Real.pi * (m : ℝ) := by
    rw [← hm]
    dsimp [townRelativePhaseRadians]
    nlinarith [hprincipal.phasePositive, hq_lt]
  have hm_upper : 2 * Real.pi * (m : ℝ) < 2 * Real.pi := by
    rw [← hm]
    dsimp [townRelativePhaseRadians]
    nlinarith [hprincipal.phaseBelowFullTurn, hq_pos]
  have hm_lower_real : (-1 : ℝ) < 2 * (m : ℝ) := by
    have hmul :
        Real.pi * (-1 : ℝ) < Real.pi * (2 * (m : ℝ)) := by
      nlinarith [hm_lower]
    exact lt_of_mul_lt_mul_left hmul hpi.le
  have hm_upper_real : 2 * (m : ℝ) < 2 := by
    have hmul :
        Real.pi * (2 * (m : ℝ)) < Real.pi * 2 := by
      nlinarith [hm_upper]
    exact lt_of_mul_lt_mul_left hmul hpi.le
  have hm_lower_int : (-1 : ℤ) < 2 * m := by
    exact_mod_cast hm_lower_real
  have hm_upper_int : 2 * m < 2 := by
    exact_mod_cast hm_upper_real
  have hm_zero : m = 0 := by
    omega
  have hn_lower : 0 < (2 * (n : ℝ) + 1) * Real.pi := by
    rw [← hn]
    dsimp [countryRelativePhaseRadians]
    nlinarith [hprincipal.phasePositive, hq_pos]
  have hn_upper : (2 * (n : ℝ) + 1) * Real.pi < 3 * Real.pi := by
    rw [← hn]
    dsimp [countryRelativePhaseRadians]
    nlinarith [hprincipal.phaseBelowFullTurn, hq_lt]
  have hn_lower_real : (0 : ℝ) < 2 * (n : ℝ) + 1 := by
    have hmul :
        (0 : ℝ) * Real.pi < (2 * (n : ℝ) + 1) * Real.pi := by
      simpa using hn_lower
    exact lt_of_mul_lt_mul_right hmul hpi.le
  have hn_upper_real : 2 * (n : ℝ) + 1 < 3 := by
    exact lt_of_mul_lt_mul_right hn_upper hpi.le
  have hn_lower_int : (0 : ℤ) < 2 * n + 1 := by
    exact_mod_cast hn_lower_real
  have hn_upper_int : 2 * n + 1 < 3 := by
    exact_mod_cast hn_upper_real
  have hn_zero : n = 0 := by
    omega
  subst m
  subst n
  norm_num at hm hn
  have hp : setup.antennaTwoInitialPhaseRadians = Real.pi / 2 := by
    dsimp [townRelativePhaseRadians, countryRelativePhaseRadians] at hm hn
    nlinarith
  have hq_eq :
      2 * Real.pi * lengthInMeters setup.antennaSeparation /
          lengthInMeters setup.wavelength =
        Real.pi / 2 := by
    dsimp [townRelativePhaseRadians, countryRelativePhaseRadians] at hm hn
    nlinarith
  constructor
  · have hcross := (div_eq_iff (ne_of_gt hw)).mp hq_eq
    have hfactor :
        Real.pi *
            (2 * lengthInMeters setup.antennaSeparation -
              lengthInMeters setup.wavelength / 2) =
          0 := by
      nlinarith [hcross]
    have hlinear :
        2 * lengthInMeters setup.antennaSeparation -
            lengthInMeters setup.wavelength / 2 =
          0 :=
      (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hpi)
    nlinarith
  · exact hp

/-!
Combining the quarter-turn phase with the delay-to-phase law gives a delay of
one quarter of the carrier period. The conclusion remains unit-independent.
-/
lemma broadcast_delay_is_quarter_period
    (setup : DirectionalAntennaArraySetup)
    (hphysical : HasPhysicalWaveParameters setup)
    (hwaves : SatisfiesDelayedTravelingWaveLaws setup)
    (hinterference : SatisfiesDirectionalInterferenceDesign setup)
    (hprincipal : UsesPrincipalShortestSpacingBranch setup)
    (unit : TimeUnit) :
    durationReadout unit setup.antennaTwoBroadcastDelay =
      durationReadout unit setup.period / 4 := by
  have hphase :
      setup.antennaTwoInitialPhaseRadians = Real.pi / 2 :=
    (principal_design_is_quarter_wavelength_and_phase
      setup hphysical hinterference hprincipal).2
  have hperiod_ne : durationReadout unit setup.period ≠ 0 := by
    intro hzero
    have hfrequency_period := hwaves.frequencyPeriodRelation unit
    rw [hzero, mul_zero] at hfrequency_period
    norm_num at hfrequency_period
  have hdelay_phase := hwaves.delayPhaseRelation unit
  rw [hphase] at hdelay_phase
  have hcross :=
    (div_eq_iff hperiod_ne).mp hdelay_phase.symm
  have hfactor :
      Real.pi *
          (2 * durationReadout unit setup.antennaTwoBroadcastDelay -
            durationReadout unit setup.period / 2) =
        0 := by
    nlinarith [hcross]
  have hlinear :
      2 * durationReadout unit setup.antennaTwoBroadcastDelay -
          durationReadout unit setup.period / 2 =
        0 :=
    (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt Real.pi_pos)
  nlinarith

/-!
At `1000 kHz` the period is `1000 ns`, so the principal directional design
uses a `250 ns` antenna-2 delay, displayed answer D.

This formalizes `thm:physics:phyx_mini_0187:target`.
-/
theorem problem_phyx_mini_0187
    (setup : DirectionalAntennaArraySetup)
    (hfigure : MatchesScenarioAndFigure setup)
    (hfrequency : HasStatedCarrierFrequency setup)
    (hphysical : HasPhysicalWaveParameters setup)
    (hwaves : SatisfiesDelayedTravelingWaveLaws setup)
    (hinterference : SatisfiesDirectionalInterferenceDesign setup)
    (hprincipal : UsesPrincipalShortestSpacingBranch setup) :
    durationInNanoseconds setup.antennaTwoBroadcastDelay = 250 ∧
      MatchesAnswerChoice setup recordedDatasetAnswer := by
  have hfrequency_khz :
      frequencyReadout TimeUnit.milliseconds setup.carrierFrequency = 1000 := by
    exact hfrequency.frequencyKilohertz
  have hfrequency_period :=
    hwaves.frequencyPeriodRelation TimeUnit.milliseconds
  have hperiod_ms :
      durationReadout TimeUnit.milliseconds setup.period =
        (1 : ℝ) / 1000 := by
    nlinarith
  have hdelay_ms :=
    broadcast_delay_is_quarter_period setup hphysical hwaves
      hinterference hprincipal TimeUnit.milliseconds
  have hdelay_ms_value :
      durationReadout TimeUnit.milliseconds
          setup.antennaTwoBroadcastDelay =
        (1 : ℝ) / 4000 := by
    nlinarith
  have hconversion :
      durationInNanoseconds setup.antennaTwoBroadcastDelay =
        1000000 *
          durationReadout TimeUnit.milliseconds
            setup.antennaTwoBroadcastDelay := by
    have h_units_val := congrArg WithDim.val
      (setup.antennaTwoBroadcastDelay.2
        {UnitChoices.SI with time := TimeUnit.milliseconds}
        {UnitChoices.SI with time := TimeUnit.nanoseconds})
    convert h_units_val using 1 <;>
      norm_num [durationInNanoseconds, durationReadout,
        UnitChoices.dimScale, TimeUnit.nanoseconds,
        TimeUnit.milliseconds, TimeUnit.seconds, TimeUnit.scale,
        TimeUnit.div_eq_val, NNReal.smul_def]
    exact Or.inl rfl
  have hdelay_ns :
      durationInNanoseconds setup.antennaTwoBroadcastDelay = 250 := by
    nlinarith
  constructor
  · exact hdelay_ns
  · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedDelayNanoseconds] using hdelay_ns

end PhyXMiniProblems.ProblemPhyXMini0187
