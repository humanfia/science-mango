import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

namespace PhyXMiniProblems.PhyxMini0004

open Dimension

/-!
# Ultrasound reflection from a liver tumor

The figure gives an incident angle measured from a vertical normal and the
horizontal separation between the beam's entry and exit normals. Lengths and
wave speeds remain dimensionful; real numbers are used only for readouts in a
specified unit and for angles measured in radians.
-/

/-- A physical length, independent of the choice of length unit. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Unit choices in which length readouts are expressed in centimeters. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The scalar centimeter readout of a dimensionful length. -/
noncomputable def lengthInCentimeters (x : DimLength) : ℝ :=
  ((x centimeterUnitChoices).val : ℝ)

/-- The scalar SI readout, in meters per second, of a dimensionful speed. -/
noncomputable def speedInMetersPerSecond (v : DimSpeed) : ℝ :=
  ((v UnitChoices.SI).val : ℝ)

/-- Convert the degree measure printed in the figure to radians. -/
noncomputable def degrees (x : ℝ) : ℝ := x * Real.pi / 180

/--
The four ray angles, all measured from the local vertical normal: before
entry, along the downward and upward liver paths, and after exit.
-/
structure BeamAngles where
  surroundingIncidentRad : ℝ
  liverDownwardRad : ℝ
  liverUpwardRad : ℝ
  surroundingExitRad : ℝ

/--
The physical quantities in the ultrasound/liver/tumor setup. `tumorDepth` is
the vertical distance from the upper liver interface to the reflecting
liver--tumor interface.
-/
structure UltrasoundTumorSetup where
  surroundingMediumWaveSpeed : DimSpeed
  liverWaveSpeed : DimSpeed
  entryExitSeparation : DimLength
  tumorDepth : DimLength
  angles : BeamAngles

/-- The two numerical readouts printed in the figure. -/
def MatchesFigureReadouts (s : UltrasoundTumorSetup) : Prop :=
  lengthInCentimeters s.entryExitSeparation = 12 ∧
  s.angles.surroundingIncidentRad = degrees 50

/-- The stated fact that sound propagates ten percent more slowly in liver. -/
def LiverSpeedIsTenPercentLower (s : UltrasoundTumorSetup) : Prop :=
  s.liverWaveSpeed =
    ((9 : NNReal) / 10) • s.surroundingMediumWaveSpeed

/-- Both propagation speeds used by Snell's law are nonzero. -/
def HasPositivePropagationSpeeds (s : UltrasoundTumorSetup) : Prop :=
  0 < speedInMetersPerSecond s.surroundingMediumWaveSpeed ∧
  0 < speedInMetersPerSecond s.liverWaveSpeed

/--
Snell's law at entry into and exit from the liver, written in the equivalent
form `sin θ₁ * v₂ = sin θ₂ * v₁`.
-/
def ObeysSnellRefraction (s : UltrasoundTumorSetup) : Prop :=
  Real.sin s.angles.surroundingIncidentRad *
      speedInMetersPerSecond s.liverWaveSpeed =
    Real.sin s.angles.liverDownwardRad *
      speedInMetersPerSecond s.surroundingMediumWaveSpeed ∧
  Real.sin s.angles.liverUpwardRad *
      speedInMetersPerSecond s.surroundingMediumWaveSpeed =
    Real.sin s.angles.surroundingExitRad *
      speedInMetersPerSecond s.liverWaveSpeed

/-- Specular reflection at the approximately horizontal tumor boundary. -/
def ObeysSpecularReflection (s : UltrasoundTumorSetup) : Prop :=
  s.angles.liverUpwardRad = s.angles.liverDownwardRad

/--
The 12 cm horizontal separation is the sum of the two right-triangle offsets
inside the liver.
-/
def ObeysFigureGeometry (s : UltrasoundTumorSetup) : Prop :=
  lengthInCentimeters s.entryExitSeparation =
    lengthInCentimeters s.tumorDepth * Real.tan s.angles.liverDownwardRad +
    lengthInCentimeters s.tumorDepth * Real.tan s.angles.liverUpwardRad

/-- The pictured rays make acute angles with the vertical normals. -/
def HasAcuteRayAngles (s : UltrasoundTumorSetup) : Prop :=
  0 < s.angles.surroundingIncidentRad ∧
  s.angles.surroundingIncidentRad < Real.pi / 2 ∧
  0 < s.angles.liverDownwardRad ∧
  s.angles.liverDownwardRad < Real.pi / 2 ∧
  0 < s.angles.liverUpwardRad ∧
  s.angles.liverUpwardRad < Real.pi / 2 ∧
  0 < s.angles.surroundingExitRad ∧
  s.angles.surroundingExitRad < Real.pi / 2

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A | B | C | D
  deriving DecidableEq

/-- The four candidate depths, in centimeters. -/
def answerDepthInCentimeters : AnswerChoice → ℝ
  | .A => 8.50
  | .B => 4.90
  | .C => 6.30
  | .D => 10.80

/--
The ten-percent speed reduction and entry Snell law determine the sine of the
downward angle inside the liver.
-/
theorem liverDownwardSin_eq_nineTenthsIncidentSin
    (s : UltrasoundTumorSetup)
    (hSlower : LiverSpeedIsTenPercentLower s)
    (hPositive : HasPositivePropagationSpeeds s)
    (hSnell : ObeysSnellRefraction s) :
    Real.sin s.angles.liverDownwardRad =
      (9 / 10 : ℝ) * Real.sin s.angles.surroundingIncidentRad := by
  rcases hPositive with ⟨hSurrounding, _⟩
  rcases hSnell with ⟨hEntry, _⟩
  simp only [speedInMetersPerSecond] at hSurrounding
  rw [hSlower] at hEntry
  simp only [speedInMetersPerSecond, Dimensionful.smul_apply,
    WithDim.smul_val, smul_eq_mul] at hEntry
  norm_num at hEntry ⊢
  nlinarith

/-- The two triangular horizontal offsets determine the tumor depth. -/
theorem tumorDepth_eq_geometryQuotient
    (s : UltrasoundTumorSetup)
    (hGeometry : ObeysFigureGeometry s)
    (hAcute : HasAcuteRayAngles s) :
    lengthInCentimeters s.tumorDepth =
      lengthInCentimeters s.entryExitSeparation /
        (Real.tan s.angles.liverDownwardRad +
          Real.tan s.angles.liverUpwardRad) := by
  rcases hAcute with ⟨_, _, hDownPos, hDownLt, hUpPos, hUpLt, _⟩
  have hTanDown : 0 < Real.tan s.angles.liverDownwardRad :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hDownPos hDownLt
  have hTanUp : 0 < Real.tan s.angles.liverUpwardRad :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hUpPos hUpLt
  rw [eq_div_iff (ne_of_gt (add_pos hTanDown hTanUp))]
  simpa [ObeysFigureGeometry, mul_add] using hGeometry.symm

/--
Under the wave laws and figure readouts, the tumor depth rounds to answer C,
6.30 cm. The `1/200` cm bound expresses rounding to the nearest hundredth.
-/
theorem tumorDepth_matches_choice_C
    (s : UltrasoundTumorSetup)
    (hFigure : MatchesFigureReadouts s)
    (hSlower : LiverSpeedIsTenPercentLower s)
    (hPositive : HasPositivePropagationSpeeds s)
    (hSnell : ObeysSnellRefraction s)
    (hReflection : ObeysSpecularReflection s)
    (hGeometry : ObeysFigureGeometry s)
    (hAcute : HasAcuteRayAngles s) :
    abs (lengthInCentimeters s.tumorDepth -
      answerDepthInCentimeters .C) ≤ (1 / 200 : ℝ) := by
  have hCos40Bounds :
      (68938 / 90000 : ℝ) < Real.cos (2 * Real.pi / 9) ∧
        Real.cos (2 * Real.pi / 9) < (68952 / 90000 : ℝ) := by
    have hCubic :
        4 * Real.cos (2 * Real.pi / 9) ^ 3 -
            3 * Real.cos (2 * Real.pi / 9) = -(1 / 2 : ℝ) := by
      have hTriple : Real.cos (3 * (2 * Real.pi / 9)) =
          4 * Real.cos (2 * Real.pi / 9) ^ 3 -
            3 * Real.cos (2 * Real.pi / 9) := by
        rw [show 3 * (2 * Real.pi / 9) =
          2 * (2 * Real.pi / 9) + 2 * Real.pi / 9 by ring,
          Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
        have hTrigMul := congrArg
          (fun x : ℝ => x * Real.cos (2 * Real.pi / 9))
          (Real.sin_sq_add_cos_sq (2 * Real.pi / 9))
        ring_nf at hTrigMul ⊢
        linarith
      rw [show 3 * (2 * Real.pi / 9) =
        Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three] at hTriple
      norm_num at hTriple ⊢
      exact hTriple.symm
    have hHalf : (1 / 2 : ℝ) < Real.cos (2 * Real.pi / 9) := by
      rw [← Real.cos_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi
        (by positivity) (by linarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
    constructor
    · by_contra h
      have hLe : Real.cos (2 * Real.pi / 9) ≤
          (68938 / 90000 : ℝ) := le_of_not_gt h
      have hBracket : 0 <
          4 * ((68938 / 90000 : ℝ) ^ 2 +
            (68938 / 90000 : ℝ) * Real.cos (2 * Real.pi / 9) +
            Real.cos (2 * Real.pi / 9) ^ 2) - 3 := by
        nlinarith [sq_nonneg (Real.cos (2 * Real.pi / 9) - 1 / 2)]
      have hProduct : 0 ≤
          ((68938 / 90000 : ℝ) - Real.cos (2 * Real.pi / 9)) *
            (4 * ((68938 / 90000 : ℝ) ^ 2 +
              (68938 / 90000 : ℝ) * Real.cos (2 * Real.pi / 9) +
              Real.cos (2 * Real.pi / 9) ^ 2) - 3) :=
        mul_nonneg (sub_nonneg.2 hLe) hBracket.le
      nlinarith
    · by_contra h
      have hGe : (68952 / 90000 : ℝ) ≤
          Real.cos (2 * Real.pi / 9) := le_of_not_gt h
      have hBracket : 0 <
          4 * (Real.cos (2 * Real.pi / 9) ^ 2 +
            Real.cos (2 * Real.pi / 9) * (68952 / 90000 : ℝ) +
            (68952 / 90000 : ℝ) ^ 2) - 3 := by
        nlinarith [sq_nonneg (Real.cos (2 * Real.pi / 9) - 1 / 2)]
      have hProduct : 0 ≤
          (Real.cos (2 * Real.pi / 9) - (68952 / 90000 : ℝ)) *
            (4 * (Real.cos (2 * Real.pi / 9) ^ 2 +
              Real.cos (2 * Real.pi / 9) * (68952 / 90000 : ℝ) +
              (68952 / 90000 : ℝ) ^ 2) - 3) :=
        mul_nonneg (sub_nonneg.2 hGe) hBracket.le
      nlinarith
  rcases hCos40Bounds with ⟨hCos40Lower, hCos40Upper⟩
  rcases hFigure with ⟨hSeparation, hIncident⟩
  have hIncidentSin : Real.sin s.angles.surroundingIncidentRad =
      Real.cos (2 * Real.pi / 9) := by
    rw [hIncident, degrees]
    rw [show (50 : ℝ) * Real.pi / 180 =
      Real.pi / 2 - 2 * Real.pi / 9 by ring,
      Real.sin_pi_div_two_sub]
  have hDownSin := liverDownwardSin_eq_nineTenthsIncidentSin
    s hSlower hPositive hSnell
  rw [hIncidentSin] at hDownSin
  have hSinLower : (68938 / 100000 : ℝ) <
      Real.sin s.angles.liverDownwardRad := by
    nlinarith only [hDownSin, hCos40Lower]
  have hSinUpper : Real.sin s.angles.liverDownwardRad <
      (68952 / 100000 : ℝ) := by
    nlinarith only [hDownSin, hCos40Upper]
  rcases hAcute with ⟨_, _, hDownPos, hDownLt, _, _, _⟩
  change s.angles.liverUpwardRad = s.angles.liverDownwardRad at hReflection
  change lengthInCentimeters s.entryExitSeparation =
    lengthInCentimeters s.tumorDepth * Real.tan s.angles.liverDownwardRad +
    lengthInCentimeters s.tumorDepth * Real.tan s.angles.liverUpwardRad at hGeometry
  rw [hSeparation, hReflection] at hGeometry
  have hTanPos : 0 < Real.tan s.angles.liverDownwardRad :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hDownPos hDownLt
  have hDepthTan : lengthInCentimeters s.tumorDepth *
      Real.tan s.angles.liverDownwardRad = 6 := by
    linarith only [hGeometry]
  have hDepthPos : 0 < lengthInCentimeters s.tumorDepth := by
    by_contra h
    have hNonpos : lengthInCentimeters s.tumorDepth ≤ 0 := le_of_not_gt h
    have hProductNonpos := mul_nonpos_of_nonpos_of_nonneg hNonpos hTanPos.le
    linarith only [hDepthTan, hProductNonpos]
  have hCosPos : 0 < Real.cos s.angles.liverDownwardRad :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hDownLt⟩
  rw [Real.tan_eq_sin_div_cos] at hDepthTan
  have hDepthSin : lengthInCentimeters s.tumorDepth *
      Real.sin s.angles.liverDownwardRad =
      6 * Real.cos s.angles.liverDownwardRad := by
    field_simp [hCosPos.ne'] at hDepthTan
    simpa [mul_comm] using hDepthTan
  have hDepthSinSq := congrArg (fun x : ℝ ↦ x ^ 2) hDepthSin
  have hTrig := Real.sin_sq_add_cos_sq s.angles.liverDownwardRad
  have hDepthEquation :
      (lengthInCentimeters s.tumorDepth ^ 2 + 36) *
        Real.sin s.angles.liverDownwardRad ^ 2 = 36 := by
    nlinarith only [hDepthSinSq, hTrig]
  have hSinPos : 0 < Real.sin s.angles.liverDownwardRad :=
    lt_trans (by norm_num) hSinLower
  have hDepthLower : (1259 / 200 : ℝ) ≤
      lengthInCentimeters s.tumorDepth := by
    by_contra h
    have hDepthLt : lengthInCentimeters s.tumorDepth <
        (1259 / 200 : ℝ) := lt_of_not_ge h
    have hDepthSq : lengthInCentimeters s.tumorDepth ^ 2 <
        (1259 / 200 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hDepthPos.le (by norm_num)).2 hDepthLt
    have hSinSq : Real.sin s.angles.liverDownwardRad ^ 2 <
        (68952 / 100000 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hSinPos.le (by norm_num)).2 hSinUpper
    have hProduct :
        (lengthInCentimeters s.tumorDepth ^ 2 + 36) *
            Real.sin s.angles.liverDownwardRad ^ 2 <
          ((1259 / 200 : ℝ) ^ 2 + 36) *
            (68952 / 100000 : ℝ) ^ 2 :=
      mul_lt_mul (by nlinarith only [hDepthSq]) hSinSq.le
        (pow_pos hSinPos 2) (by positivity)
    norm_num at hProduct
    nlinarith only [hProduct, hDepthEquation]
  have hDepthUpper : lengthInCentimeters s.tumorDepth ≤
      (1261 / 200 : ℝ) := by
    by_contra h
    have hDepthGt : (1261 / 200 : ℝ) <
        lengthInCentimeters s.tumorDepth := lt_of_not_ge h
    have hDepthSq : (1261 / 200 : ℝ) ^ 2 <
        lengthInCentimeters s.tumorDepth ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hDepthPos.le).2 hDepthGt
    have hSinSq : (68938 / 100000 : ℝ) ^ 2 <
        Real.sin s.angles.liverDownwardRad ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hSinPos.le).2 hSinLower
    have hProduct :
        ((1261 / 200 : ℝ) ^ 2 + 36) *
            (68938 / 100000 : ℝ) ^ 2 <
          (lengthInCentimeters s.tumorDepth ^ 2 + 36) *
            Real.sin s.angles.liverDownwardRad ^ 2 :=
      mul_lt_mul (by nlinarith only [hDepthSq]) hSinSq.le
        (by positivity) (by positivity)
    norm_num at hProduct
    nlinarith only [hProduct, hDepthEquation]
  rw [abs_le]
  norm_num [answerDepthInCentimeters]
  constructor <;> linarith

end PhyXMiniProblems.PhyxMini0004
