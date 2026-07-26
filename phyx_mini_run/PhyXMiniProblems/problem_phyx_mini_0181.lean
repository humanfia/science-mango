import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# Fundamental frequency of a wire supporting a horizontal bar

This file models problem `phyx_mini_0181`.  A steel wire runs from a wall
anchor to the free end of a horizontal, wall-hinged bar.  The bar carries a
hanging mass at that free end.  Static torque balance determines the wire
tension; the wire's mass and geometry determine its linear mass density; and
the fixed-end stretched-string law determines its fundamental frequency.

Masses, lengths, acceleration, force, linear mass density, and frequency are
represented by Physlib dimensionful quantities.  Real numbers are used only
for dimensionless angles and coherent SI readouts.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0181

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The magnitude of a physical acceleration. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- The magnitude of a physical force, used below for the wire tension. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical mass per unit length. -/
abbrev LinearMassDensity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev Frequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Newton readout of a force magnitude in coherent SI base units. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Kilograms-per-metre readout of a linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : Frequency) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-! ## Physical setup and primary-figure data -/

/--
The dimensionful quantities in the wall--bar--wire setup.

The bar is horizontal and hinged to the wall at its left endpoint.  The wire
joins the wall anchor to the bar's right endpoint, where the hanging mass is
attached.  `barCenterLeverArm` is the distance from the wall hinge to the
bar's center of mass.  The angle is measured in radians above the horizontal
bar.  Tension, linear density, and fundamental frequency are unknown physical
quantities; this structure does not assign them their requested values.
-/
structure SteelWireBarSetup where
  barMass : MassQuantity
  barLength : LengthQuantity
  barCenterLeverArm : LengthQuantity
  hangingMass : MassQuantity
  wireMass : MassQuantity
  wireLength : LengthQuantity
  wireAngle : ℝ
  gravitationalAcceleration : AccelerationMagnitude
  wireTension : ForceMagnitude
  wireLinearMassDensity : LinearMassDensity
  wireFundamentalFrequency : Frequency

/--
The numerical readouts printed in the primary figure: a `4.0 kg`, `2.0 m`
horizontal bar, a `75 g` steel wire at `45°`, and an `8.0 kg` hanging mass.

No value for the wire length, tension, density, or frequency is included here.
-/
def MatchesPrimaryFigure (setup : SteelWireBarSetup) : Prop :=
  massInKilograms setup.barMass = 4 ∧
    lengthInMeters setup.barLength = 2 ∧
    massInKilograms setup.hangingMass = 8 ∧
    massInKilograms setup.wireMass = 75 / 1000 ∧
    setup.wireAngle = Real.pi / 4

/--
The standard classroom approximation `g = 9.8 m/s²`, kept separate because it
is auxiliary calibration data rather than a number printed in the figure.
-/
def UsesStandardGravity (setup : SteelWireBarSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 9.8

/--
For the uniform bar shown in the figure, its center of mass lies halfway from
the wall hinge to the wire/load junction.
-/
def HasUniformBarMassDistribution (setup : SteelWireBarSetup) : Prop :=
  lengthInMeters setup.barCenterLeverArm =
    lengthInMeters setup.barLength / 2

/--
Right-triangle geometry for the wire: its horizontal projection equals the
distance from the wall hinge to the bar's free end.  The wall anchor is
vertically above the hinge, as in the primary figure.
-/
def SatisfiesWireGeometry (setup : SteelWireBarSetup) : Prop :=
  lengthInMeters setup.wireLength * Real.cos setup.wireAngle =
    lengthInMeters setup.barLength

/-! ## Governing physical laws -/

/--
Static torque balance about the wall hinge.  The wire contributes the moment
of its vertical tension component at the bar end; the hanging load acts at
that end, while the uniform bar's weight acts at its center of mass.
-/
structure SatisfiesStaticTorqueBalance (setup : SteelWireBarSetup) : Prop where
  torqueBalance :
    forceInNewtons setup.wireTension * Real.sin setup.wireAngle *
        lengthInMeters setup.barLength =
      massInKilograms setup.hangingMass *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters setup.barLength +
        massInKilograms setup.barMass *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters setup.barCenterLeverArm

/-- The wire's linear mass density is its total mass divided by its length. -/
structure SatisfiesWireLinearDensityLaw (setup : SteelWireBarSetup) : Prop where
  densityLaw :
    linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity =
      massInKilograms setup.wireMass / lengthInMeters setup.wireLength

/--
The fundamental-mode law for a taut, uniform wire fixed at both ends:
`f₁ = (1 / (2 L)) * sqrt (T / μ)` in coherent SI readouts.
-/
structure SatisfiesFixedEndFundamentalFrequencyLaw
    (setup : SteelWireBarSetup) : Prop where
  frequencyLaw :
    frequencyInHertz setup.wireFundamentalFrequency =
      1 / (2 * lengthInMeters setup.wireLength) *
        Real.sqrt
          (forceInNewtons setup.wireTension /
            linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity)

/-- Positivity conditions appropriate to a taut massive wire in gravity. -/
def HasPositivePhysicalParameters (setup : SteelWireBarSetup) : Prop :=
  0 < massInKilograms setup.barMass ∧
    0 < lengthInMeters setup.barLength ∧
    0 < lengthInMeters setup.barCenterLeverArm ∧
    0 < massInKilograms setup.hangingMass ∧
    0 < massInKilograms setup.wireMass ∧
    0 < lengthInMeters setup.wireLength ∧
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration ∧
    0 < forceInNewtons setup.wireTension ∧
    0 < linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity

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
  | .A => 72.3
  | .B => 17.4
  | .C => 6.5
  | .D => 13

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Agreement with a displayed whole-hertz answer.  A half-hertz tolerance models
rounding to the nearest hertz rather than identifying the physical frequency
with an exact integer.
-/
def MatchesAnswerChoice
    (frequency : Frequency) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ 1 / 2

/--
Under the figure data, static support laws, and stretched-wire mode law, the
wire's fundamental frequency agrees with recorded answer D (`13 Hz`) to the
precision displayed by that answer.

This formalizes `thm:physics:phyx_mini_0181:target`.
-/
theorem fundamentalFrequency_matches_recordedAnswerD
    (setup : SteelWireBarSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_gravity : UsesStandardGravity setup)
    (h_uniformBar : HasUniformBarMassDistribution setup)
    (h_geometry : SatisfiesWireGeometry setup)
    (h_torque : SatisfiesStaticTorqueBalance setup)
    (h_density : SatisfiesWireLinearDensityLaw setup)
    (h_frequency : SatisfiesFixedEndFundamentalFrequencyLaw setup)
    (h_positive : HasPositivePhysicalParameters setup) :
    MatchesAnswerChoice setup.wireFundamentalFrequency recordedAnswerChoice := by
  rcases h_figure with
    ⟨h_barMass, h_barLength, h_hangingMass, h_wireMass, h_wireAngle⟩
  have h_gravityValue := h_gravity
  unfold UsesStandardGravity at h_gravityValue
  have h_barCenter := h_uniformBar
  unfold HasUniformBarMassDistribution at h_barCenter
  rw [h_barLength] at h_barCenter
  norm_num at h_barCenter
  have h_wireLength_pos :
      0 < lengthInMeters setup.wireLength :=
    h_positive.2.2.2.2.2.1
  have h_tension_pos :
      0 < forceInNewtons setup.wireTension :=
    h_positive.2.2.2.2.2.2.2.1
  have h_density_pos :
      0 < linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity :=
    h_positive.2.2.2.2.2.2.2.2
  -- Basic identities and nonvanishing for `√2`.
  have h_sqrtTwo_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h_sqrtTwo_ne : Real.sqrt 2 ≠ 0 := ne_of_gt h_sqrtTwo_pos
  have h_sqrtTwo_sq : (Real.sqrt 2) ^ 2 = 2 := by
    norm_num
  -- The 45-degree geometry makes the wire length `2√2` metres.
  have h_wireLength :
      lengthInMeters setup.wireLength = 2 * Real.sqrt 2 := by
    unfold SatisfiesWireGeometry at h_geometry
    rw [h_wireAngle, Real.cos_pi_div_four, h_barLength] at h_geometry
    have h_product :
        lengthInMeters setup.wireLength * Real.sqrt 2 = 4 := by
      nlinarith [h_geometry]
    calc
      lengthInMeters setup.wireLength =
          (lengthInMeters setup.wireLength * Real.sqrt 2) / Real.sqrt 2 := by
            field_simp
      _ = 4 / Real.sqrt 2 := by rw [h_product]
      _ = 2 * Real.sqrt 2 := by
        field_simp
        nlinarith [h_sqrtTwo_sq]
  -- Torque balance about the hinge makes the tension `98√2` newtons.
  have h_torqueBalance := h_torque.torqueBalance
  rw [h_wireAngle, Real.sin_pi_div_four, h_barLength, h_hangingMass,
    h_gravityValue, h_barMass, h_barCenter] at h_torqueBalance
  have h_tensionProduct :
      forceInNewtons setup.wireTension * Real.sqrt 2 = 196 := by
    norm_num at h_torqueBalance ⊢
    nlinarith [h_torqueBalance]
  have h_tension :
      forceInNewtons setup.wireTension = 98 * Real.sqrt 2 := by
    calc
      forceInNewtons setup.wireTension =
          (forceInNewtons setup.wireTension * Real.sqrt 2) / Real.sqrt 2 := by
            field_simp
      _ = 196 / Real.sqrt 2 := by rw [h_tensionProduct]
      _ = 98 * Real.sqrt 2 := by
        field_simp
        nlinarith [h_sqrtTwo_sq]
  -- Dividing the wire mass by its length determines its linear density.
  have h_densityLaw := h_density.densityLaw
  rw [h_wireMass, h_wireLength] at h_densityLaw
  have h_densityValue :
      linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity =
        3 * Real.sqrt 2 / 160 := by
    calc
      linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity =
          (75 / 1000 : ℝ) / (2 * Real.sqrt 2) := h_densityLaw
      _ = 3 * Real.sqrt 2 / 160 := by
        field_simp
        nlinarith [h_sqrtTwo_sq]
  -- The square roots cancel in the tension-to-density ratio.
  have h_tensionDensityRatio :
      forceInNewtons setup.wireTension /
          linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity =
        15680 / 3 := by
    rw [h_tension, h_densityValue]
    field_simp
    nlinarith [h_sqrtTwo_sq]
  -- The mode law consequently gives `f² = 490/3`.
  have h_frequencyLaw := h_frequency.frequencyLaw
  rw [h_wireLength, h_tensionDensityRatio] at h_frequencyLaw
  have h_radicand_nonneg : (0 : ℝ) ≤ 15680 / 3 := by norm_num
  have h_radicand_sqrt_sq :
      (Real.sqrt (15680 / 3 : ℝ)) ^ 2 = 15680 / 3 :=
    Real.sq_sqrt h_radicand_nonneg
  have h_frequency_nonneg :
      0 ≤ frequencyInHertz setup.wireFundamentalFrequency := by
    rw [h_frequency.frequencyLaw]
    positivity
  have h_frequency_sq :
      (frequencyInHertz setup.wireFundamentalFrequency) ^ 2 = 490 / 3 := by
    rw [h_frequencyLaw]
    field_simp
    nlinarith [h_sqrtTwo_sq, h_radicand_sqrt_sq]
  -- A nonnegative number with this square lies between `12.5` and `13.5`.
  simp only [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.hertz]
  rw [abs_le]
  constructor <;> nlinarith [h_frequency_sq]

end PhyXMiniProblems.ProblemPhyXMini0181
