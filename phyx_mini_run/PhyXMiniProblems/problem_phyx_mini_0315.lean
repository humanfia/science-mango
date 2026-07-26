import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Destructive interference in a straight-and-semicircular sound tube

This file models problem `phyx_mini_0315`. A sound wave from the labelled
source splits at the left junction. One part traverses the straight diameter
of a semicircle, while the other traverses its semicircular arc; the parts
rejoin before reaching the labelled detector.

Physical lengths are represented by Physlib dimensionful quantities. Real
numbers occur only as readouts in a selected length unit, phase readouts in
radians, and dimensionless answer data.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0315

open Dimension

/-! ## Dimensionful lengths and unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical acoustic length in a chosen length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a physical acoustic length in centimeters. -/
def centimetersValue (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-! ## Figure labels and physical setup -/

/-- Named points in the supplied source--tube--detector figure. -/
inductive FigurePoint where
  | source
  | leftJunction
  | center
  | rightJunction
  | detector
  deriving DecidableEq, Repr

/-- The two competing routes between the junctions. -/
inductive TubeBranch where
  | straight
  | semicircular
  deriving DecidableEq, Repr

/-- The geometric kind of a depicted route. -/
inductive TubePathKind where
  | straightSegment
  | semicircularArc
  deriving DecidableEq, Repr

/-- A route drawn between two labelled points of the tube. -/
structure DepictedTubePath where
  startPoint : FigurePoint
  endPoint : FigurePoint
  kind : TubePathKind

/-!
Qualitative information read from the primary image. The radius segment is
drawn from the circle center to the semicircular branch and carries the label
`r`; the scalar value of that radius is deliberately not figure data.
-/
structure SemicircularTubeFigure where
  path : TubeBranch → DepictedTubePath
  pointShown : FigurePoint → Bool
  sourceLabelShown : Bool
  detectorLabelShown : Bool
  radiusSegmentCenter : FigurePoint
  radiusSegmentEndsOn : TubeBranch
  radiusLabelRShown : Bool

/-!
The independent physical quantities and observables in the experiment.
`Amplitude` remains abstract because the source amplitude and its unit are not
specified. Path lengths and the detector-minimum observation depend on the
candidate physical radius used to build the semicircular bypass.
-/
structure TwoPathSoundTubeSetup (Amplitude : Type) where
  figure : SemicircularTubeFigure
  wavelength : AcousticLength
  branchAmplitudeAtDetector : TubeBranch → Amplitude
  phaseAtSplitRadians : TubeBranch → ℝ
  pathLength : TubeBranch → AcousticLength → AcousticLength
  pathDifferenceAtDetector : AcousticLength → AcousticLength
  intensityMinimumAtDetector : AcousticLength → Prop

/-!
The points and paths shown in the image. Both competing routes begin and end
at the same junctions; one is a straight diameter and the other a semicircle.
This contains no radius value and no interference conclusion.
-/
def MatchesSuppliedFigure {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude) : Prop :=
  (∀ point, setup.figure.pointShown point = true) ∧
    setup.figure.sourceLabelShown = true ∧
    setup.figure.detectorLabelShown = true ∧
    setup.figure.path .straight =
      { startPoint := .leftJunction
        endPoint := .rightJunction
        kind := .straightSegment } ∧
    setup.figure.path .semicircular =
      { startPoint := .leftJunction
        endPoint := .rightJunction
        kind := .semicircularArc } ∧
    setup.figure.radiusSegmentCenter = .center ∧
    setup.figure.radiusSegmentEndsOn = .semicircular ∧
    setup.figure.radiusLabelRShown = true

/-- The wavelength readout supplied in the prose is `40.0 cm`. -/
structure MatchesProblemReadout {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude) : Prop where
  wavelength_centimeters : centimetersValue setup.wavelength = 40

/-!
Both parts originate by splitting one wave, so the model assumes equal
amplitudes at recombination and a common phase at the split. This is source
data, not a claim about the phase accumulated along either route.
-/
def EmitsCoherentlyFromSingleSource {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude) : Prop :=
  setup.branchAmplitudeAtDetector .straight =
      setup.branchAmplitudeAtDetector .semicircular ∧
    setup.phaseAtSplitRadians .straight =
      setup.phaseAtSplitRadians .semicircular

/-- The supplied wavelength is a strictly positive physical length. -/
structure HasPhysicalAcousticParameters {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude) : Prop where
  wavelength_pos : ∀ unit,
    0 < lengthReadout unit setup.wavelength

/-! ## Governing geometry and interference laws -/

/-!
For every candidate radius, the direct route is a diameter of length `2 r`
and the bypass is a semicircular arc of length `π r`. These are general
geometric laws, stated in every supported length unit.
-/
structure SatisfiesSemicircularTubeGeometry {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude) : Prop where
  straight_path_length : ∀ unit radius,
    lengthReadout unit (setup.pathLength .straight radius) =
      2 * lengthReadout unit radius
  semicircular_path_length : ∀ unit radius,
    lengthReadout unit (setup.pathLength .semicircular radius) =
      Real.pi * lengthReadout unit radius

/-- The path difference is the magnitude of the two branch-length difference. -/
structure SatisfiesPathDifferenceLaw {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude) : Prop where
  path_difference : ∀ unit radius,
    lengthReadout unit (setup.pathDifferenceAtDetector radius) =
      |lengthReadout unit (setup.pathLength .semicircular radius) -
        lengthReadout unit (setup.pathLength .straight radius)|

/-!
The general destructive-interference law for two coherent equal-amplitude
parts of one monochromatic wave: a positive-radius tube gives an intensity
minimum exactly when its path difference is an odd half-integer multiple of
the wavelength. The same integer order witnesses the equality in every unit.
No radius value or least-radius claim occurs in this law.
-/
structure SatisfiesTwoPathDestructiveInterferenceLaw {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude) : Prop where
  minimum_iff_odd_half_wavelength :
    EmitsCoherentlyFromSingleSource setup →
      ∀ radius,
        0 < centimetersValue radius →
        (setup.intensityMinimumAtDetector radius ↔
          ∃ order : ℕ,
            ∀ unit,
              lengthReadout unit (setup.pathDifferenceAtDetector radius) =
                ((2 * (order : ℝ) + 1) / 2) *
                  lengthReadout unit setup.wavelength)

/-!
A proposed radius is the answer to the word "smallest" when it is positive,
produces an intensity minimum, and is no larger (in centimeter readout) than
any other positive radius that produces a minimum.
-/
def IsSmallestPositiveMinimumRadius {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude)
    (radius : AcousticLength) : Prop :=
  0 < centimetersValue radius ∧
    setup.intensityMinimumAtDetector radius ∧
    ∀ other : AcousticLength,
      0 < centimetersValue other →
      setup.intensityMinimumAtDetector other →
      centimetersValue radius ≤ centimetersValue other

/-!
The geometry and path-difference law imply the general formula
`ΔL = (π - 2) r` for every positive candidate radius.
-/
lemma pathDifference_eq_pi_sub_two_mul_radius {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude)
    (hGeometry : SatisfiesSemicircularTubeGeometry setup)
    (hPathDifference : SatisfiesPathDifferenceLaw setup) :
    ∀ radius,
      0 < centimetersValue radius →
      centimetersValue (setup.pathDifferenceAtDetector radius) =
        (Real.pi - 2) * centimetersValue radius := by
  intro radius hRadius
  change 0 < lengthReadout LengthUnit.centimeters radius at hRadius
  change lengthReadout LengthUnit.centimeters
      (setup.pathDifferenceAtDetector radius) =
    (Real.pi - 2) * lengthReadout LengthUnit.centimeters radius
  rw [hPathDifference.path_difference, hGeometry.semicircular_path_length,
    hGeometry.straight_path_length]
  rw [abs_of_pos]
  · ring
  · have hPi : (2 : ℝ) < Real.pi := by
      have hPiNe : (2 : ℝ) ≠ Real.pi := by
        intro h
        have hSin : 0 < Real.sin (2 : ℝ) :=
          Real.sin_pos_of_pos_of_le_two (by norm_num) (by norm_num)
        rw [h, Real.sin_pi] at hSin
        exact (lt_irrefl 0) hSin
      exact lt_of_le_of_ne Real.two_le_pi hPiNe
    nlinarith

/-! ## Multiple-choice data and requested conclusion -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The radius in centimeters printed beside each answer label. -/
def displayedRadiusCentimeters : AnswerChoice → ℝ
  | .A => 10
  | .B => 25 / 2
  | .C => 15
  | .D => 35 / 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A real value rounds to the displayed value at the nearest tenth. -/
def RoundsToNearestTenth (value displayedValue : ℝ) : Prop :=
  |value - displayedValue| < 1 / 20

/-!
The least positive destructive-interference radius has exact centimeter
readout `20 / (π - 2)`: the first path difference is half of the `40 cm`
wavelength. This value rounds to `17.5 cm`, selecting recorded choice D.

Blueprint: `thm:physics:phyx_mini_0315:target`.
-/
theorem smallestRadius_selects_answerD {Amplitude : Type}
    (setup : TwoPathSoundTubeSetup Amplitude)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadout : MatchesProblemReadout setup)
    (hCoherent : EmitsCoherentlyFromSingleSource setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hGeometry : SatisfiesSemicircularTubeGeometry setup)
    (hPathDifference : SatisfiesPathDifferenceLaw setup)
    (hInterference : SatisfiesTwoPathDestructiveInterferenceLaw setup) :
    ∃ radius : AcousticLength,
      IsSmallestPositiveMinimumRadius setup radius ∧
        centimetersValue radius = 20 / (Real.pi - 2) ∧
        RoundsToNearestTenth
          (centimetersValue radius)
          (displayedRadiusCentimeters recordedAnswerChoice) := by
  clear hFigure
  have hSinLt {x : ℝ} (h : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with h' | h'
    · exact (Real.sin_le_one x).trans_lt h'
    have hx : |x| = x := abs_of_nonneg h.le
    have hBound :=
      le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
    rw [sub_le_iff_le_add', hx] at hBound
    apply hBound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
    apply pow_le_pow_of_le_one h.le h'
    simp
  have hSinGtSubCube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) :
      x - x ^ 3 / 4 < Real.sin x := by
    have hx : |x| = x := abs_of_nonneg h.le
    have hBound :=
      neg_le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
    rw [le_sub_iff_add_le, hx] at hBound
    refine lt_of_lt_of_le ?_ hBound
    have hDifference :
        x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', hDifference]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
    apply pow_le_pow_of_le_one h.le h'
    simp
  have hPiGtSeries (n : ℕ) :
      2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) <
        Real.pi := by
    have h :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 *
            2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply hSinLt
        apply div_pos Real.pi_pos
      all_goals positivity
    refine lt_of_le_of_lt (le_of_eq ?_) h
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have hPiLtSeries (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have h :
        Real.pi <
          (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 +
              1 / (2 ^ n) ^ 3 / 4) *
            (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by simp), ← Real.sin_pi_over_two_pow_succ,
        ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <| hSinGtSubCube (by positivity)
            (div_le_one_of_le₀ (by
              calc
                Real.pi ≤ 4 := Real.pi_le_four
                _ = 2 ^ (0 + 2) := by norm_num
                _ ≤ 2 ^ (n + 2) := by gcongr <;> norm_num)
              (by positivity))
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le h (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div,
      ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc,
        mul_comm n]
    all_goals norm_num
  have hPiLowerBoundStart (n : ℕ) {a : ℝ}
      (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
        (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
      a < Real.pi := by
    refine lt_of_le_of_lt ?_ (hPiGtSeries n)
    rw [mul_comm]
    refine (div_le_iff₀ (pow_pos (by simp) _)).mp
      (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm, show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
      rw [Nat.cast_zero, zero_div]]
  have hSqrtSeriesStepUp (c d : ℕ) {a b n : ℕ} {z : ℝ}
      (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
      (hb : 0 < b) (hd : 0 < d)
      (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
      Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
    refine le_trans ?_ hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
      div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
      div_le_div_iff₀ hb' (pow_pos hd' _)]
    exact_mod_cast h
  have hPiUpperBoundStart (n : ℕ) {a : ℝ}
      (h : (2 : ℝ) -
          ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
      (hSmall : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
      Real.pi < a := by
    refine lt_of_lt_of_le (hPiLtSeries n) ?_
    rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left,
      sub_le_comm]
    · rwa [Nat.cast_zero, zero_div] at h
    · exact div_nonneg (sub_nonneg.2 hSmall)
        (pow_nonneg (le_of_lt zero_lt_two) _)
    · exact pow_pos zero_lt_two _
  have hSqrtSeriesStepDown (a b : ℕ) {c d n : ℕ} {z : ℝ}
      (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
      (hb : 0 < b) (hd : 0 < d)
      (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
      z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
    apply le_trans hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    apply Real.le_sqrt_of_sq_le
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
      div_le_div_iff₀ (pow_pos hb' _) hd']
    exact_mod_cast h
  have hPiLower : (3.14 : ℝ) < Real.pi := by
    apply hPiLowerBoundStart 4
    refine hSqrtSeriesStepUp 338 239 ?_ (by norm_num) (by norm_num)
      (by norm_num)
    refine hSqrtSeriesStepUp 704 381 ?_ (by norm_num) (by norm_num)
      (by norm_num)
    refine hSqrtSeriesStepUp 1940 989 ?_ (by norm_num) (by norm_num)
      (by norm_num)
    refine hSqrtSeriesStepUp 1447 727 ?_ (by norm_num) (by norm_num)
      (by norm_num)
    simp [Real.sqrtTwoAddSeries]
    norm_num
  have hPiUpper : Real.pi < (3.1416 : ℝ) := by
    apply hPiUpperBoundStart 9
    · refine hSqrtSeriesStepDown 4756 3363 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 14965 8099 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 21183 10799 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 49188 24713 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 43947 22000 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 235667 117869 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 624137 312092 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 903049 451533 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      refine hSqrtSeriesStepDown 849938 424971 ?_ (by norm_num)
        (by norm_num) (by norm_num)
      simp [Real.sqrtTwoAddSeries]
      norm_num
    · norm_num
  have hPiSubTwoPos : 0 < Real.pi - 2 := by
    nlinarith [hPiLower]
  let radiusScale : NNReal :=
    ⟨1 / (2 * (Real.pi - 2)),
      (div_pos zero_lt_one (mul_pos (by norm_num) hPiSubTwoPos)).le⟩
  let radius : AcousticLength := radiusScale • setup.wavelength
  have hScalePos : 0 < (radiusScale : ℝ) := by
    change 0 < 1 / (2 * (Real.pi - 2))
    positivity
  have hReadoutScale (unit : LengthUnit) :
      lengthReadout unit radius =
        (radiusScale : ℝ) * lengthReadout unit setup.wavelength := by
    simp [radius, lengthReadout]
  have hRadiusCentimeters :
      centimetersValue radius = 20 / (Real.pi - 2) := by
    change lengthReadout LengthUnit.centimeters radius =
      20 / (Real.pi - 2)
    rw [hReadoutScale]
    change (radiusScale : ℝ) * centimetersValue setup.wavelength = _
    rw [hReadout.wavelength_centimeters]
    change (1 / (2 * (Real.pi - 2))) * 40 = 20 / (Real.pi - 2)
    field_simp
    norm_num
  have hRadiusPositive : 0 < centimetersValue radius := by
    rw [hRadiusCentimeters]
    exact div_pos (by norm_num) hPiSubTwoPos
  have hRadiusReadoutPositive (unit : LengthUnit) :
      0 < lengthReadout unit radius := by
    rw [hReadoutScale]
    exact mul_pos hScalePos (hPhysical.wavelength_pos unit)
  have hRadiusPathDifference (unit : LengthUnit) :
      lengthReadout unit (setup.pathDifferenceAtDetector radius) =
        (Real.pi - 2) * lengthReadout unit radius := by
    rw [hPathDifference.path_difference,
      hGeometry.semicircular_path_length,
      hGeometry.straight_path_length]
    rw [abs_of_pos]
    · ring
    · nlinarith [
        mul_pos hPiSubTwoPos (hRadiusReadoutPositive unit)]
  have hRadiusMinimum :
      setup.intensityMinimumAtDetector radius := by
    apply (hInterference.minimum_iff_odd_half_wavelength
      hCoherent radius hRadiusPositive).2
    refine ⟨0, ?_⟩
    intro unit
    rw [hRadiusPathDifference, hReadoutScale]
    change
      (Real.pi - 2) *
          ((1 / (2 * (Real.pi - 2))) *
            lengthReadout unit setup.wavelength) =
        ((2 * ((0 : ℕ) : ℝ) + 1) / 2) *
          lengthReadout unit setup.wavelength
    field_simp [ne_of_gt hPiSubTwoPos]
    ring
  have hRadiusLeast (other : AcousticLength)
      (hOtherPositive : 0 < centimetersValue other)
      (hOtherMinimum : setup.intensityMinimumAtDetector other) :
      centimetersValue radius ≤ centimetersValue other := by
    rcases (hInterference.minimum_iff_odd_half_wavelength
      hCoherent other hOtherPositive).mp hOtherMinimum with
      ⟨order, hOrder⟩
    have hOrderCentimeters := hOrder LengthUnit.centimeters
    change
      centimetersValue (setup.pathDifferenceAtDetector other) =
        ((2 * (order : ℝ) + 1) / 2) *
          centimetersValue setup.wavelength at hOrderCentimeters
    rw [pathDifference_eq_pi_sub_two_mul_radius setup hGeometry
      hPathDifference other hOtherPositive,
      hReadout.wavelength_centimeters] at hOrderCentimeters
    have hOrderNonnegative : (0 : ℝ) ≤ (order : ℝ) :=
      Nat.cast_nonneg order
    have hTwentyLe :
        20 ≤ (Real.pi - 2) * centimetersValue other := by
      nlinarith [hOrderNonnegative]
    rw [hRadiusCentimeters, div_le_iff₀ hPiSubTwoPos]
    nlinarith
  refine ⟨radius,
    ⟨hRadiusPositive, hRadiusMinimum, hRadiusLeast⟩,
    hRadiusCentimeters, ?_⟩
  change |centimetersValue radius - 35 / 2| < 1 / 20
  rw [hRadiusCentimeters, abs_lt]
  constructor
  · have hValueLower :
        (349 : ℝ) / 20 < 20 / (Real.pi - 2) := by
      rw [lt_div_iff₀ hPiSubTwoPos]
      norm_num at hPiUpper ⊢
      nlinarith
    nlinarith
  · have hValueUpper :
        20 / (Real.pi - 2) < (351 : ℝ) / 20 := by
      rw [div_lt_iff₀ hPiSubTwoPos]
      norm_num at hPiLower ⊢
      nlinarith
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0315
