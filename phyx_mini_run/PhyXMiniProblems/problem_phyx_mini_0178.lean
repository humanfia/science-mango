import Mathlib
import Physlib.Units.WithDim.Speed

namespace PhyXMiniProblems.ProblemPhyXMini0178

open Dimension

/-!
# Four-antinodal standing wave after a tension increase

The string's length, linear mass density, tension, wave speed, and frequency
are represented as unit-independent dimensionful quantities. The initial and
post-increase states refer to the same physical string, so its length and
linear density are shared.
-/

/-- The two configurations compared in the problem. -/
inductive StringState where
  | initial
  | afterTensionIncrease
  deriving DecidableEq, Repr

/-- The fixed supports visible at the left and right ends of the figure. -/
inductive StringEndpoint where
  | left
  | right
  deriving DecidableEq, Repr

/-- A physical length, independent of a choice of units. -/
abbrev DimLength : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A physical (ordinary, not angular) frequency, with dimension inverse time. -/
abbrev DimFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- String tension, carrying the physical dimension of force. -/
abbrev DimTension : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Linear mass density, carrying the physical dimension mass per length. -/
abbrev DimLinearMassDensity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- The real-valued SI readout of a nonnegative dimensionful quantity. -/
noncomputable def siReadout {d : Dimension}
    (q : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((q UnitChoices.SI).val : ℝ)

/--
Data for the same string before and after its tension is increased. The
boolean-free propositions record whether a configuration is a standing wave
and whether each supported endpoint is a node.
-/
structure VibratingStringSetup where
  length : DimLength
  linearMassDensity : DimLinearMassDensity
  tension : StringState → DimTension
  waveSpeed : StringState → DimSpeed
  frequency : StringState → DimFrequency
  antinodeCount : StringState → ℕ
  isStandingWave : StringState → Prop
  endpointIsNode : StringState → StringEndpoint → Prop

/-- The original diagram is a fixed-end standing wave with four antinodes. -/
def MatchesInitialFigure (s : VibratingStringSetup) : Prop :=
  s.isStandingWave .initial ∧
  s.antinodeCount .initial = 4 ∧
  ∀ endpoint, s.endpointIsNode .initial endpoint

/--
The requested post-increase configuration is again a fixed-end standing wave
with four antinodes.
-/
def IsRequiredFourAntinodeMode (s : VibratingStringSetup) : Prop :=
  s.isStandingWave .afterTensionIncrease ∧
  s.antinodeCount .afterTensionIncrease = 4 ∧
  ∀ endpoint, s.endpointIsNode .afterTensionIncrease endpoint

/-- The stated fourfold increase of the physical string tension. -/
def TensionIncreasedByFour (s : VibratingStringSetup) : Prop :=
  s.tension .afterTensionIncrease =
    (4 : NNReal) • s.tension .initial

/--
The transverse-wave speed law for a stretched string, written without a
square root as \(v^2 μ = T\) in SI readouts.
-/
def ObeysTransverseStringWaveSpeedLaw (s : VibratingStringSetup) : Prop :=
  ∀ state,
    siReadout (s.waveSpeed state) ^ 2 *
        siReadout s.linearMassDensity =
      siReadout (s.tension state)

/--
For a standing wave with nodes at both fixed endpoints, \(2 L f = n v\),
where \(n\) is the number of antinodes.
-/
def ObeysFixedEndStandingWaveLaw (s : VibratingStringSetup) : Prop :=
  ∀ state,
    s.isStandingWave state →
    (∀ endpoint, s.endpointIsNode state endpoint) →
    0 < s.antinodeCount state →
    2 * siReadout s.length * siReadout (s.frequency state) =
      (s.antinodeCount state : ℝ) * siReadout (s.waveSpeed state)

/-- The nondegeneracy conditions for the physical string and both modes. -/
def HasPositivePhysicalData (s : VibratingStringSetup) : Prop :=
  0 < siReadout s.length ∧
  0 < siReadout s.linearMassDensity ∧
  ∀ state,
    0 < siReadout (s.tension state) ∧
    0 < siReadout (s.waveSpeed state) ∧
    0 < siReadout (s.frequency state)

/-- Labels of the multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless frequency multipliers displayed in choices A--D. -/
noncomputable def answerFrequencyFactor : AnswerChoice → ℝ
  | .A => Real.sqrt 2
  | .B => 1
  | .C => 1 / 2
  | .D => 2

/--
The wave-speed law and a fourfold tension increase make the wave speed double
on the unchanged string.
-/
theorem waveSpeed_after_fourfold_tension
    (s : VibratingStringSetup)
    (hPositive : HasPositivePhysicalData s)
    (hWaveSpeed : ObeysTransverseStringWaveSpeedLaw s)
    (hTension : TensionIncreasedByFour s) :
    s.waveSpeed .afterTensionIncrease =
      (2 : NNReal) • s.waveSpeed .initial := by
  have hμ : 0 < siReadout s.linearMassDensity := hPositive.2.1
  have hv₀ : 0 < siReadout (s.waveSpeed .initial) :=
    (hPositive.2.2 .initial).2.1
  have hv₁ : 0 < siReadout (s.waveSpeed .afterTensionIncrease) :=
    (hPositive.2.2 .afterTensionIncrease).2.1
  have hLaw₀ := hWaveSpeed .initial
  have hLaw₁ := hWaveSpeed .afterTensionIncrease
  have hTensionSI :
      siReadout (s.tension .afterTensionIncrease) =
        4 * siReadout (s.tension .initial) := by
    simpa [siReadout] using congrArg siReadout hTension
  have hScaledSquares :
      siReadout (s.waveSpeed .afterTensionIncrease) ^ 2 *
          siReadout s.linearMassDensity =
        4 * (siReadout (s.waveSpeed .initial) ^ 2 *
          siReadout s.linearMassDensity) := by
    calc
      siReadout (s.waveSpeed .afterTensionIncrease) ^ 2 *
            siReadout s.linearMassDensity =
          siReadout (s.tension .afterTensionIncrease) := hLaw₁
      _ = 4 * siReadout (s.tension .initial) := hTensionSI
      _ = 4 * (siReadout (s.waveSpeed .initial) ^ 2 *
            siReadout s.linearMassDensity) := by rw [hLaw₀]
  have hSquares :
      siReadout (s.waveSpeed .afterTensionIncrease) ^ 2 =
        4 * siReadout (s.waveSpeed .initial) ^ 2 := by
    apply mul_right_cancel₀ (ne_of_gt hμ)
    nlinarith [hScaledSquares]
  have hSpeedReadout :
      siReadout (s.waveSpeed .afterTensionIncrease) =
        2 * siReadout (s.waveSpeed .initial) := by
    nlinarith [hSquares]
  have hSI :
      s.waveSpeed .afterTensionIncrease UnitChoices.SI =
        ((2 : NNReal) • s.waveSpeed .initial) UnitChoices.SI := by
    apply WithDim.ext
    apply NNReal.eq
    simpa [siReadout] using hSpeedReadout
  apply Dimensionful.ext
  funext units
  calc
    s.waveSpeed .afterTensionIncrease units =
        UnitChoices.SI.dimScale units
            (dim (WithDim (L𝓭 * T𝓭⁻¹) NNReal)) •
          s.waveSpeed .afterTensionIncrease UnitChoices.SI :=
      (s.waveSpeed .afterTensionIncrease).property UnitChoices.SI units
    _ = UnitChoices.SI.dimScale units
            (dim (WithDim (L𝓭 * T𝓭⁻¹) NNReal)) •
          ((2 : NNReal) • s.waveSpeed .initial) UnitChoices.SI := by
      rw [hSI]
    _ = ((2 : NNReal) • s.waveSpeed .initial) units :=
      (((2 : NNReal) • s.waveSpeed .initial).property
        UnitChoices.SI units).symm

/--
For the same four-antinodal fixed-end mode, a fourfold tension increase
requires twice the initial frequency. This is answer D.
-/
theorem frequency_for_four_antinodes_after_fourfold_tension
    (s : VibratingStringSetup)
    (hFigure : MatchesInitialFigure s)
    (hRequiredMode : IsRequiredFourAntinodeMode s)
    (hPositive : HasPositivePhysicalData s)
    (hWaveSpeed : ObeysTransverseStringWaveSpeedLaw s)
    (hStandingWave : ObeysFixedEndStandingWaveLaw s)
    (hTension : TensionIncreasedByFour s) :
    s.frequency .afterTensionIncrease =
      (2 : NNReal) • s.frequency .initial := by
  have hSpeed :=
    waveSpeed_after_fourfold_tension s hPositive hWaveSpeed hTension
  have hSpeedReadout :
      siReadout (s.waveSpeed .afterTensionIncrease) =
        2 * siReadout (s.waveSpeed .initial) := by
    simpa [siReadout] using congrArg siReadout hSpeed
  have hInitialStanding :
      2 * siReadout s.length * siReadout (s.frequency .initial) =
        4 * siReadout (s.waveSpeed .initial) := by
    have h :=
      hStandingWave .initial hFigure.1 hFigure.2.2 (by
        simp [hFigure.2.1])
    simpa [hFigure.2.1] using h
  have hAfterStanding :
      2 * siReadout s.length *
          siReadout (s.frequency .afterTensionIncrease) =
        4 * siReadout (s.waveSpeed .afterTensionIncrease) := by
    have h :=
      hStandingWave .afterTensionIncrease hRequiredMode.1
        hRequiredMode.2.2 (by simp [hRequiredMode.2.1])
    simpa [hRequiredMode.2.1] using h
  have hLength : 0 < siReadout s.length := hPositive.1
  have hFrequencyProducts :
      siReadout s.length *
          siReadout (s.frequency .afterTensionIncrease) =
        siReadout s.length *
          (2 * siReadout (s.frequency .initial)) := by
    nlinarith [hInitialStanding, hAfterStanding, hSpeedReadout]
  have hFrequencyReadout :
      siReadout (s.frequency .afterTensionIncrease) =
        2 * siReadout (s.frequency .initial) := by
    exact mul_left_cancel₀ (ne_of_gt hLength) hFrequencyProducts
  have hSI :
      s.frequency .afterTensionIncrease UnitChoices.SI =
        ((2 : NNReal) • s.frequency .initial) UnitChoices.SI := by
    apply WithDim.ext
    apply NNReal.eq
    simpa [siReadout] using hFrequencyReadout
  apply Dimensionful.ext
  funext units
  calc
    s.frequency .afterTensionIncrease units =
        UnitChoices.SI.dimScale units
            (dim (WithDim T𝓭⁻¹ NNReal)) •
          s.frequency .afterTensionIncrease UnitChoices.SI :=
      (s.frequency .afterTensionIncrease).property UnitChoices.SI units
    _ = UnitChoices.SI.dimScale units
            (dim (WithDim T𝓭⁻¹ NNReal)) •
          ((2 : NNReal) • s.frequency .initial) UnitChoices.SI := by
      rw [hSI]
    _ = ((2 : NNReal) • s.frequency .initial) units :=
      (((2 : NNReal) • s.frequency .initial).property
        UnitChoices.SI units).symm

end PhyXMiniProblems.ProblemPhyXMini0178
