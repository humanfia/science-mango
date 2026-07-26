import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic

noncomputable section

open MeasureTheory
open scoped Interval

namespace PhyXMini0506

/-!
The horizontal coordinate is the numerical value of position measured in millimetres.
Correspondingly, `waveAmplitudePerSqrtMillimetre x` is the numerical complex
wavefunction amplitude at that position, measured in inverse square-root millimetres.
-/

/-- The left wall of the confining region shown in the figure, in millimetres. -/
def leftWallMillimetres : ℝ := -4

/-- The right wall of the confining region shown in the figure, in millimetres. -/
def rightWallMillimetres : ℝ := 4

/-- The lower endpoint of the interval queried in the problem, in millimetres. -/
def queryLowerMillimetres : ℝ := -2

/-- The upper endpoint of the interval queried in the problem, in millimetres. -/
def queryUpperMillimetres : ℝ := 2

/--
The Born-rule probability of finding the particle between two position readouts.
The integration variable is the numerical position in millimetres.
-/
def positionProbability
    (waveAmplitudePerSqrtMillimetre : ℝ → ℂ)
    (lowerMillimetres upperMillimetres : ℝ) : ℝ :=
  ∫ xMillimetres in lowerMillimetres..upperMillimetres,
    Complex.normSq (waveAmplitudePerSqrtMillimetre xMillimetres)

/--
`RoundsToHundredth probability n` means that the nearest-hundredth display of
`probability` is `n / 100`, using the usual half-up convention at the lower boundary.
-/
def RoundsToHundredth (probability : ℝ) (hundredths : ℤ) : Prop :=
  (hundredths : ℝ) / 100 - 1 / 200 ≤ probability ∧
    probability < (hundredths : ℝ) / 100 + 1 / 200

/--
For the normalized, confined wavefunction read from the figure, the probability of
finding the particle between `-2 mm` and `2 mm` is exactly `1/8`, which is displayed
to the nearest hundredth as `0.13` (answer choice C).
-/
theorem central_interval_probability
    (waveAmplitudePerSqrtMillimetre : ℝ → ℂ)
    (cPerSqrtMillimetre : ℝ)
    (h_squareIntegrable :
      QuantumMechanics.OneDimension.HilbertSpace.MemHS
        waveAmplitudePerSqrtMillimetre)
    (h_c_positive : 0 < cPerSqrtMillimetre)
    (h_zero_outside : ∀ xMillimetres : ℝ,
      xMillimetres < leftWallMillimetres ∨ rightWallMillimetres < xMillimetres →
        waveAmplitudePerSqrtMillimetre xMillimetres = 0)
    (h_linear_inside : ∀ xMillimetres : ℝ,
      leftWallMillimetres ≤ xMillimetres →
      xMillimetres ≤ rightWallMillimetres →
        waveAmplitudePerSqrtMillimetre xMillimetres =
          ((cPerSqrtMillimetre * xMillimetres / 4 : ℝ) : ℂ))
    (h_normalized :
      (∫ xMillimetres : ℝ,
        Complex.normSq (waveAmplitudePerSqrtMillimetre xMillimetres)) = 1) :
    positionProbability waveAmplitudePerSqrtMillimetre
        queryLowerMillimetres queryUpperMillimetres = (1 : ℝ) / 8 ∧
      RoundsToHundredth
        (positionProbability waveAmplitudePerSqrtMillimetre
          queryLowerMillimetres queryUpperMillimetres)
        13 := by
  have hAmplitudeSqInside (xMillimetres : ℝ)
      (hLeft : leftWallMillimetres ≤ xMillimetres)
      (hRight : xMillimetres ≤ rightWallMillimetres) :
      Complex.normSq (waveAmplitudePerSqrtMillimetre xMillimetres) =
        cPerSqrtMillimetre ^ 2 * xMillimetres ^ 2 / 16 := by
    rw [h_linear_inside xMillimetres hLeft hRight, Complex.normSq_ofReal]
    ring

  have hAmplitudeSqOutside (xMillimetres : ℝ)
      (hOutside : xMillimetres < leftWallMillimetres ∨
        rightWallMillimetres < xMillimetres) :
      Complex.normSq (waveAmplitudePerSqrtMillimetre xMillimetres) = 0 := by
    rw [h_zero_outside xMillimetres hOutside]
    exact Complex.normSq_zero

  have hAmplitudeSq (xMillimetres : ℝ) :
      Complex.normSq (waveAmplitudePerSqrtMillimetre xMillimetres) =
        (Set.Icc leftWallMillimetres rightWallMillimetres).indicator
          (fun x : ℝ ↦ cPerSqrtMillimetre ^ 2 * x ^ 2 / 16)
          xMillimetres := by
    by_cases hx :
        xMillimetres ∈ Set.Icc leftWallMillimetres rightWallMillimetres
    · rw [Set.indicator_of_mem hx]
      exact hAmplitudeSqInside xMillimetres hx.1 hx.2
    · rw [Set.indicator_of_notMem hx]
      apply hAmplitudeSqOutside xMillimetres
      rw [Set.mem_Icc] at hx
      by_cases hLeftOutside : xMillimetres < leftWallMillimetres
      · exact Or.inl hLeftOutside
      · right
        have hLeft : leftWallMillimetres ≤ xMillimetres :=
          le_of_not_gt hLeftOutside
        exact lt_of_not_ge fun hRight ↦ hx ⟨hLeft, hRight⟩

  have hRampNormalization :
      (∫ x : ℝ in leftWallMillimetres..rightWallMillimetres,
        cPerSqrtMillimetre ^ 2 * x ^ 2 / 16) = 1 := by
    calc
      (∫ x : ℝ in leftWallMillimetres..rightWallMillimetres,
          cPerSqrtMillimetre ^ 2 * x ^ 2 / 16) =
          ∫ x : ℝ in Set.Icc leftWallMillimetres rightWallMillimetres,
            cPerSqrtMillimetre ^ 2 * x ^ 2 / 16 := by
              rw [intervalIntegral.integral_of_le (by
                norm_num [leftWallMillimetres, rightWallMillimetres]),
                ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = ∫ x : ℝ,
          (Set.Icc leftWallMillimetres rightWallMillimetres).indicator
            (fun y : ℝ ↦ cPerSqrtMillimetre ^ 2 * y ^ 2 / 16) x :=
        (MeasureTheory.integral_indicator measurableSet_Icc).symm
      _ = ∫ x : ℝ,
          Complex.normSq (waveAmplitudePerSqrtMillimetre x) := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ (hAmplitudeSq x).symm
      _ = 1 := h_normalized

  have hRampIntegral :
      (∫ x : ℝ in leftWallMillimetres..rightWallMillimetres,
        cPerSqrtMillimetre ^ 2 * x ^ 2 / 16) =
        (8 / 3 : ℝ) * cPerSqrtMillimetre ^ 2 := by
    calc
      (∫ x : ℝ in leftWallMillimetres..rightWallMillimetres,
          cPerSqrtMillimetre ^ 2 * x ^ 2 / 16) =
          ∫ x : ℝ in leftWallMillimetres..rightWallMillimetres,
            (cPerSqrtMillimetre ^ 2 / 16) * x ^ 2 := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
      _ = (cPerSqrtMillimetre ^ 2 / 16) *
          (∫ x : ℝ in leftWallMillimetres..rightWallMillimetres,
            x ^ 2) := intervalIntegral.integral_const_mul _ _
      _ = (8 / 3 : ℝ) * cPerSqrtMillimetre ^ 2 := by
        rw [integral_pow]
        norm_num [leftWallMillimetres, rightWallMillimetres]
        ring

  have hcSq : cPerSqrtMillimetre ^ 2 = (3 / 8 : ℝ) := by
    rw [hRampIntegral] at hRampNormalization
    linarith

  have hCentralProbability :
      positionProbability waveAmplitudePerSqrtMillimetre
          queryLowerMillimetres queryUpperMillimetres = 1 / 8 := by
    calc
      positionProbability waveAmplitudePerSqrtMillimetre
          queryLowerMillimetres queryUpperMillimetres =
          ∫ x : ℝ in queryLowerMillimetres..queryUpperMillimetres,
            cPerSqrtMillimetre ^ 2 * x ^ 2 / 16 := by
              apply intervalIntegral.integral_congr
              intro x hx
              rw [Set.uIcc_of_le (by
                norm_num [queryLowerMillimetres, queryUpperMillimetres])] at hx
              apply hAmplitudeSqInside x
              · dsimp [leftWallMillimetres, queryLowerMillimetres] at *
                linarith [hx.1]
              · dsimp [rightWallMillimetres, queryUpperMillimetres] at *
                linarith [hx.2]
      _ = ∫ x : ℝ in queryLowerMillimetres..queryUpperMillimetres,
          (cPerSqrtMillimetre ^ 2 / 16) * x ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x _
            ring
      _ = (cPerSqrtMillimetre ^ 2 / 16) *
          (∫ x : ℝ in queryLowerMillimetres..queryUpperMillimetres,
            x ^ 2) := intervalIntegral.integral_const_mul _ _
      _ = 1 / 8 := by
        rw [hcSq, integral_pow]
        norm_num [queryLowerMillimetres, queryUpperMillimetres]

  refine ⟨hCentralProbability, ?_⟩
  rw [hCentralProbability]
  norm_num [RoundsToHundredth]

end PhyXMini0506
