import Mathlib
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0642

open Dimension

/-!
# Photoelectron emission rate from a saturation-current graph

The supplied graph plots photocurrent `I`, in microamperes, against applied
potential difference `ΔV`, in volts.  It shows zero current through about
`-2 V`, a rising transition, and a `10 μA` saturation plateau.  In the
photoelectric model, the saturation current is the charge transported per
second by all emitted photoelectrons.

Electric potential, current, charge, and emission rate are represented by
Physlib dimensionful quantities.  Real numbers below occur only as calibrated
unit readouts, plotted coordinates, or the displayed multiple-choice values.

Assumption/target split:

* `MatchesSuppliedPhotoelectricGraph` contains only axis labels, ticks, curve
  shape, and the stopping-potential and saturation-current readouts visible in
  image `642.png`;
* `UsesRoundedElectronChargeDatum` contains the conventional textbook value
  `1.6 × 10⁻¹⁹ C` for the magnitude of the electron charge;
* `SatisfiesSaturationChargeFlowLaw` states the governing relation `I = q N`
  between saturation current, electron charge, and particles emitted per
  second; and
* the equality identifying the experiment's requested rate as
  `6.25 × 10¹³ s⁻¹`, hence answer choice B, occurs only in the conclusion of
  `photoelectrons_ejected_per_second`.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- Electric current has physical dimension charge divided by time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential has dimension energy divided by charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed physical electric potential difference. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative physical electric-current magnitude. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative physical electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative particle-emission rate, with inverse-time dimension. -/
abbrev ParticleRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an applied potential difference in volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read an electric-current magnitude in amperes. -/
def electricCurrentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Read an electric-current magnitude in microamperes. -/
def electricCurrentInMicroamperes (current : ElectricCurrentQuantity) : ℝ :=
  10 ^ 6 * electricCurrentInAmperes current

/-- Read a charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/--
Read a charge magnitude in Physlib elementary-charge units.  The theorem's
numerical premise separately records the rounded textbook coulomb conversion
used by the answer choices.
-/
def chargeMagnitudeInElementaryCharges
    (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge {UnitChoices.SI with
      charge := ChargeUnit.elementaryCharge}).val : ℝ)

/-- Read a particle-emission rate as particles per second. -/
def particleRatePerSecond (rate : ParticleRateQuantity) : ℝ :=
  nonnegativeSIReadout rate

/-! ## Multiple-choice and primary-figure vocabulary -/

/-- The answer-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A | B | C | D
  deriving DecidableEq, Fintype, Repr

/-- The four displayed candidate emission rates, in particles per second. -/
def displayedRateForChoice : AnswerChoice → ℝ
  | .A => 6.2 * 10 ^ 13
  | .B => 6.25 * 10 ^ 13
  | .C => 6.3 * 10 ^ 13
  | .D => 6.35 * 10 ^ 13

/-- The horizontal and vertical axes of the supplied graph. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantities named by the two graph-axis labels. -/
inductive FigureQuantityLabel where
  | potentialDifferenceDeltaV
  | photocurrentI
  deriving DecidableEq, Repr

/-- Units printed in parentheses beside the graph-axis labels. -/
inductive FigureUnitLabel where
  | volts
  | microamperes
  deriving DecidableEq, Repr

/-!
Calibrated scalar data and visual attributes of image `642.png`.  The curve is
a graph readout in microamperes as a function of volts; it is not used as a
replacement for the dimensionful saturation current in the experiment.
-/
structure PhotoelectricCurrentVoltageFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  axisQuantity : FigureAxis → FigureQuantityLabel
  axisUnit : FigureAxis → FigureUnitLabel
  voltageTickShown : ℤ → Bool
  currentTickShownMicroamperes : ℕ → Bool
  curveMicroamperesAtVolts : ℝ → ℝ
  stoppingPotentialVolts : ℝ
  saturationOnsetVolts : ℝ
  saturationCurrentMicroamperes : ℝ
  curveIsPurple : Bool

/-!
Independent physical quantities of the experiment.  In particular,
`photoelectronEmissionRate` is stored independently rather than defined from
the saturation current or from any answer choice.
-/
structure PhotoelectricExperiment where
  stoppingPotentialDifference : ElectricPotentialQuantity
  saturationOnsetPotentialDifference : ElectricPotentialQuantity
  saturationPhotocurrent : ElectricCurrentQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  photoelectronEmissionRate : ParticleRateQuantity
  figure : PhotoelectricCurrentVoltageFigure

/-! ## Scenario, figure evidence, reference data, and governing law -/

/-- Qualitative physical conditions for the represented photoelectric setup. -/
structure MatchesPhotoelectricExperiment
    (setup : PhotoelectricExperiment) : Prop where
  stoppingPotentialIsNegative :
    electricPotentialInVolts setup.stoppingPotentialDifference < 0
  saturationCurrentIsPositive :
    0 < electricCurrentInAmperes setup.saturationPhotocurrent
  electronChargeMagnitudeIsPositive :
    0 < chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  emissionRateIsNonnegative :
    0 ≤ particleRatePerSecond setup.photoelectronEmissionRate

/-!
Labels, ticks, calibrated readouts, and qualitative curve geometry read from
the primary image.  The hand-drawn saturation onset lies strictly between the
displayed `0 V` and `1 V` ticks; the exact onset is irrelevant to the requested
plateau-current calculation.
-/
structure MatchesSuppliedPhotoelectricGraph
    (setup : PhotoelectricExperiment) : Prop where
  rasterWidth : setup.figure.rasterWidthPixels = 712
  rasterHeight : setup.figure.rasterHeightPixels = 376
  horizontalQuantityLabel :
    setup.figure.axisQuantity .horizontal = .potentialDifferenceDeltaV
  verticalQuantityLabel :
    setup.figure.axisQuantity .vertical = .photocurrentI
  horizontalUnitLabel : setup.figure.axisUnit .horizontal = .volts
  verticalUnitLabel : setup.figure.axisUnit .vertical = .microamperes
  voltageTickMinusThree : setup.figure.voltageTickShown (-3) = true
  voltageTickMinusTwo : setup.figure.voltageTickShown (-2) = true
  voltageTickMinusOne : setup.figure.voltageTickShown (-1) = true
  voltageTickZero : setup.figure.voltageTickShown 0 = true
  voltageTickOne : setup.figure.voltageTickShown 1 = true
  voltageTickTwo : setup.figure.voltageTickShown 2 = true
  voltageTickThree : setup.figure.voltageTickShown 3 = true
  currentTickTen : setup.figure.currentTickShownMicroamperes 10 = true
  purpleCurve : setup.figure.curveIsPurple = true
  stoppingPotentialReadout : setup.figure.stoppingPotentialVolts = -2
  saturationOnsetBetweenZeroAndOne :
    0 < setup.figure.saturationOnsetVolts ∧
      setup.figure.saturationOnsetVolts < 1
  saturationLevelReadout :
    setup.figure.saturationCurrentMicroamperes = 10
  physicalStoppingPotentialMatchesGraph :
    electricPotentialInVolts setup.stoppingPotentialDifference =
      setup.figure.stoppingPotentialVolts
  physicalSaturationOnsetMatchesGraph :
    electricPotentialInVolts setup.saturationOnsetPotentialDifference =
      setup.figure.saturationOnsetVolts
  physicalSaturationCurrentMatchesGraph :
    electricCurrentInMicroamperes setup.saturationPhotocurrent =
      setup.figure.saturationCurrentMicroamperes
  zeroCurrentRegion :
    ∀ volts : ℝ, volts ≤ setup.figure.stoppingPotentialVolts →
      setup.figure.curveMicroamperesAtVolts volts = 0
  strictlyRisingTransition :
    ∀ {volts₁ volts₂ : ℝ},
      setup.figure.stoppingPotentialVolts ≤ volts₁ →
      volts₁ < volts₂ →
      volts₂ ≤ setup.figure.saturationOnsetVolts →
      setup.figure.curveMicroamperesAtVolts volts₁ <
        setup.figure.curveMicroamperesAtVolts volts₂
  saturationPlateau :
    ∀ volts : ℝ, setup.figure.saturationOnsetVolts ≤ volts →
      setup.figure.curveMicroamperesAtVolts volts =
        setup.figure.saturationCurrentMicroamperes

/-!
The conventional rounded charge magnitude used in the textbook arithmetic.
It is reference data, not the requested emission rate.
-/
structure UsesRoundedElectronChargeDatum
    (setup : PhotoelectricExperiment) : Prop where
  electronChargeInCoulombs :
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
      (1.6 : ℝ) / 10 ^ 19

/-!
At saturation, every emitted photoelectron contributes its charge to the
collected charge per unit time, so the current magnitude is `q N`.
-/
structure SatisfiesSaturationChargeFlowLaw
    (setup : PhotoelectricExperiment) : Prop where
  saturationCurrentEqualsChargeTimesRate :
    electricCurrentInAmperes setup.saturationPhotocurrent =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        particleRatePerSecond setup.photoelectronEmissionRate

/--
From the `10 μA` saturation plateau and the rounded electron charge
`1.6 × 10⁻¹⁹ C`, the experiment ejects `6.25 × 10¹³` photoelectrons per
second, which is the value printed as answer choice B.

Blueprint label: `thm:physics:phyx_mini_0642:target`.
-/
theorem photoelectrons_ejected_per_second
    (setup : PhotoelectricExperiment)
    (hScenario : MatchesPhotoelectricExperiment setup)
    (hFigure : MatchesSuppliedPhotoelectricGraph setup)
    (hCharge : UsesRoundedElectronChargeDatum setup)
    (hLaw : SatisfiesSaturationChargeFlowLaw setup) :
    particleRatePerSecond setup.photoelectronEmissionRate =
      6.25 * 10 ^ 13 := by
  have hCurrentMicroamperes :
      electricCurrentInMicroamperes setup.saturationPhotocurrent = 10 := by
    calc
      electricCurrentInMicroamperes setup.saturationPhotocurrent =
          setup.figure.saturationCurrentMicroamperes :=
        hFigure.physicalSaturationCurrentMatchesGraph
      _ = 10 := hFigure.saturationLevelReadout
  have hCurrentAmperes :
      electricCurrentInAmperes setup.saturationPhotocurrent =
        (1 : ℝ) / 10 ^ 5 := by
    rw [electricCurrentInMicroamperes] at hCurrentMicroamperes
    norm_num at hCurrentMicroamperes ⊢
    linarith
  have hChargeFlow := hLaw.saturationCurrentEqualsChargeTimesRate
  rw [hCurrentAmperes, hCharge.electronChargeInCoulombs] at hChargeFlow
  norm_num at hChargeFlow ⊢
  linarith

end PhyXMiniProblems.ProblemPhyXMini0642
