import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/-!
# A spider web loaded by a trapped insect

This file models problem `phyx_mini_0200`.  A spider of mass `0.30 g`
vibrates with its negligibly massive web at about `15 Hz`.  A trapped insect
of mass `0.10 g` is then added.  For slight vibrations, the web is modeled as
the same linear harmonic spring before and after the insect is caught, while
the effective oscillating mass changes.

Mass, stiffness, and frequency are represented by Physlib dimensionful
quantities.  The scalar fields of Physlib's `HarmonicOscillator` are connected
explicitly to coherent SI readouts; they are not used as replacements for the
physical quantities.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0200

open Dimension

/-! ## Dimensionful quantities and coherent readouts -/

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/--
The effective stiffness of the web, with dimension force per length,
equivalently mass per time squared.
-/
abbrev StiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical cyclic frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Gram readout of a physical mass. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Newton-per-metre readout of the web's effective stiffness. -/
def stiffnessInNewtonsPerMeter (stiffness : StiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-! ## Physical setup and primary-image readout -/

/-- The two sides used to describe the occupants' locations in the image. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The web geometry visible in the supplied image. -/
inductive WebGeometry where
  | spiralOrb
  deriving DecidableEq, Repr

/--
The physical quantities and labeled image features in the two-load experiment.

The two `HarmonicOscillator` fields are Physlib's scalar oscillator models for
the spider-only and spider-plus-insect configurations.  Their masses and
stiffnesses are related to the dimensionful quantities only by the governing
law below.  In particular, this structure assigns no requested value to
`loadedFrequency`.
-/
structure SpiderWebSetup where
  spiderMass : MassQuantity
  trappedInsectMass : MassQuantity
  webMass : MassQuantity
  webEffectiveStiffness : StiffnessQuantity
  spiderOnlyFrequency : FrequencyQuantity
  loadedFrequency : FrequencyQuantity
  spiderOnlyOscillator : ClassicalMechanics.HarmonicOscillator
  loadedOscillator : ClassicalMechanics.HarmonicOscillator
  spiderLocation : FigureSide
  trappedInsectLocation : FigureSide
  geometry : WebGeometry

/--
The numerical and visual data supplied by the problem and its primary image.

The `1/2 Hz` interval records the wording "about `15 Hz`" at whole-hertz
precision.  It is a calibration of the spider-only configuration, not an
assumption about the frequency after the insect is added.
-/
def MatchesProblemData (setup : SpiderWebSetup) : Prop :=
  massInGrams setup.spiderMass = 3 / 10 ∧
    massInGrams setup.trappedInsectMass = 1 / 10 ∧
    massInGrams setup.webMass = 0 ∧
    |frequencyInHertz setup.spiderOnlyFrequency - 15| ≤ 1 / 2 ∧
    setup.spiderLocation = .right ∧
    setup.trappedInsectLocation = .left ∧
    setup.geometry = .spiralOrb

/-! ## Governing small-oscillation law -/

/--
For slight vibrations, the web and its occupants form a linear harmonic
oscillator.  The effective mass is the web plus the occupants present in each
configuration.  The web has the same effective stiffness in both cases, and
the physical cyclic frequency `f` is related to Physlib's angular frequency by
`ω = 2 π f`.

This interface states the physical modeling law.  It does not assume the
requested loaded frequency or any answer-choice relation.
-/
structure SatisfiesSharedHarmonicOscillatorModel
    (setup : SpiderWebSetup) : Prop where
  spiderOnlyEffectiveMass :
    setup.spiderOnlyOscillator.m =
      massInKilograms setup.spiderMass + massInKilograms setup.webMass
  loadedEffectiveMass :
    setup.loadedOscillator.m =
      massInKilograms setup.spiderMass +
        massInKilograms setup.trappedInsectMass +
        massInKilograms setup.webMass
  spiderOnlyEffectiveStiffness :
    setup.spiderOnlyOscillator.k =
      stiffnessInNewtonsPerMeter setup.webEffectiveStiffness
  loadedEffectiveStiffness :
    setup.loadedOscillator.k =
      stiffnessInNewtonsPerMeter setup.webEffectiveStiffness
  spiderOnlyAngularFrequency :
    2 * Real.pi * frequencyInHertz setup.spiderOnlyFrequency =
      setup.spiderOnlyOscillator.ω
  loadedAngularFrequency :
    2 * Real.pi * frequencyInHertz setup.loadedFrequency =
      setup.loadedOscillator.ω

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 19
  | .B => 16
  | .C => 10
  | .D => 13

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Agreement with a displayed whole-hertz answer.  The half-hertz tolerance makes
the conclusion a rounding claim rather than an unphysical exact identification
of the oscillator's frequency with an integer.
-/
def MatchesAnswerChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ 1 / 2

/--
Adding the `0.10 g` insect to the `0.30 g` spider changes the effective mass
while leaving the web stiffness fixed.  Consequently the expected loaded
frequency rounds to `13 Hz`, recorded as answer D.

This formalizes `thm:physics:phyx_mini_0200:target`.
-/
theorem loadedFrequency_matches_recordedAnswerD
    (setup : SpiderWebSetup)
    (h_data : MatchesProblemData setup)
    (h_model : SatisfiesSharedHarmonicOscillatorModel setup) :
    MatchesAnswerChoice setup.loadedFrequency recordedAnswerChoice := by
  change |frequencyInHertz setup.loadedFrequency - 13| ≤ 1 / 2
  rcases h_data with
    ⟨h_spider_g, h_insect_g, h_web_g, h_freq, h_loc_s, h_loc_i, h_geom⟩
  have h_spider_kg : massInKilograms setup.spiderMass = 3 / 10000 := by
    unfold massInGrams at h_spider_g
    norm_num at h_spider_g ⊢
    linarith only [h_spider_g]
  have h_insect_kg : massInKilograms setup.trappedInsectMass = 1 / 10000 := by
    unfold massInGrams at h_insect_g
    norm_num at h_insect_g ⊢
    linarith only [h_insect_g]
  have h_web_kg : massInKilograms setup.webMass = 0 := by
    unfold massInGrams at h_web_g
    norm_num at h_web_g ⊢
    linarith only [h_web_g]
  have hs_m : setup.spiderOnlyOscillator.m = 3 / 10000 := by
    rw [h_model.spiderOnlyEffectiveMass, h_spider_kg, h_web_kg]
    norm_num
  have hl_m : setup.loadedOscillator.m = 1 / 2500 := by
    rw [h_model.loadedEffectiveMass, h_spider_kg, h_insect_kg, h_web_kg]
    norm_num
  have h_k : setup.loadedOscillator.k = setup.spiderOnlyOscillator.k := by
    rw [h_model.loadedEffectiveStiffness, h_model.spiderOnlyEffectiveStiffness]
  have hso := setup.spiderOnlyOscillator.ω_sq
  have hlo := setup.loadedOscillator.ω_sq
  rw [hs_m] at hso
  rw [hl_m, h_k] at hlo
  field_simp at hso hlo
  have h_omega_ratio :
      4 * setup.loadedOscillator.ω ^ 2 =
        3 * setup.spiderOnlyOscillator.ω ^ 2 := by
    nlinarith only [hso, hlo]
  have h_frequency_ratio :
      4 * frequencyInHertz setup.loadedFrequency ^ 2 =
        3 * frequencyInHertz setup.spiderOnlyFrequency ^ 2 := by
    apply mul_left_cancel₀
      (pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero) :
        (2 * Real.pi) ^ 2 ≠ 0)
    calc
      (2 * Real.pi) ^ 2 *
          (4 * frequencyInHertz setup.loadedFrequency ^ 2) =
          4 * (2 * Real.pi *
            frequencyInHertz setup.loadedFrequency) ^ 2 := by
            ring
      _ = 4 * setup.loadedOscillator.ω ^ 2 := by
        rw [h_model.loadedAngularFrequency]
      _ = 3 * setup.spiderOnlyOscillator.ω ^ 2 := h_omega_ratio
      _ = 3 * (2 * Real.pi *
          frequencyInHertz setup.spiderOnlyFrequency) ^ 2 := by
        rw [h_model.spiderOnlyAngularFrequency]
      _ = (2 * Real.pi) ^ 2 *
          (3 * frequencyInHertz setup.spiderOnlyFrequency ^ 2) := by
        ring
  have hl_pos : 0 < frequencyInHertz setup.loadedFrequency := by
    have hω := setup.loadedOscillator.ω_pos
    rw [← h_model.loadedAngularFrequency] at hω
    nlinarith only [hω, Real.pi_pos]
  rcases (abs_le.mp h_freq) with ⟨h_freq_lower, h_freq_upper⟩
  have hs_lower :
      (29 : ℝ) / 2 ≤ frequencyInHertz setup.spiderOnlyFrequency := by
    nlinarith only [h_freq_lower]
  have hs_upper :
      frequencyInHertz setup.spiderOnlyFrequency ≤ (31 : ℝ) / 2 := by
    nlinarith only [h_freq_upper]
  have hs_sq_lower :
      (29 / 2 : ℝ) ^ 2 ≤
        frequencyInHertz setup.spiderOnlyFrequency ^ 2 := by
    have hprod : 0 ≤
        (frequencyInHertz setup.spiderOnlyFrequency - 29 / 2) *
          (frequencyInHertz setup.spiderOnlyFrequency + 29 / 2) :=
      mul_nonneg (sub_nonneg.mpr hs_lower) (by nlinarith only [hs_lower])
    nlinarith only [hprod]
  have hs_sq_upper :
      frequencyInHertz setup.spiderOnlyFrequency ^ 2 ≤
        (31 / 2 : ℝ) ^ 2 := by
    have hprod : 0 ≤
        (31 / 2 - frequencyInHertz setup.spiderOnlyFrequency) *
          (31 / 2 + frequencyInHertz setup.spiderOnlyFrequency) :=
      mul_nonneg (sub_nonneg.mpr hs_upper) (by nlinarith only [hs_lower])
    nlinarith only [hprod]
  have hl_lower :
      (25 : ℝ) / 2 ≤ frequencyInHertz setup.loadedFrequency := by
    by_contra h
    have hlt :
        frequencyInHertz setup.loadedFrequency < 25 / 2 :=
      lt_of_not_ge h
    have hprod : 0 <
        (25 / 2 - frequencyInHertz setup.loadedFrequency) *
          (25 / 2 + frequencyInHertz setup.loadedFrequency) :=
      mul_pos (sub_pos.mpr hlt) (by nlinarith only [hl_pos])
    nlinarith only [hprod, hs_sq_lower, h_frequency_ratio]
  have hl_upper :
      frequencyInHertz setup.loadedFrequency ≤ (27 : ℝ) / 2 := by
    by_contra h
    have hgt :
        27 / 2 < frequencyInHertz setup.loadedFrequency :=
      lt_of_not_ge h
    have hprod : 0 <
        (frequencyInHertz setup.loadedFrequency - 27 / 2) *
          (frequencyInHertz setup.loadedFrequency + 27 / 2) :=
      mul_pos (sub_pos.mpr hgt) (by nlinarith only [hl_pos])
    nlinarith only [hprod, hs_sq_upper, h_frequency_ratio]
  exact abs_le.mpr
    ⟨by linarith only [hl_lower], by linarith only [hl_upper]⟩

end PhyXMiniProblems.ProblemPhyXMini0200
