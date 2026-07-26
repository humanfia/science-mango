import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0081

open Dimension

/-!
# Longer wavelength in a two-line x-ray diffraction pattern

The primary figure plots relative intensity against the Bragg angle `θ`.  Its
horizontal calibration is `θₛ = 2.00°`; four peaks form the first- and
second-order pairs of the two wavelengths in the incident x-ray beam.  The
reflecting-plane spacing is `0.94 nm`.

Physical wavelengths and plane spacings are represented by PhysLean
dimensionful lengths.  Real scalars are used only for readouts in a named unit,
angles in degrees or radians, and dimensionless relative intensities.
-/

/-- A nonnegative physical quantity carrying the dimension of length. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length as a real scalar in the specified length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- The nanometer readout used for the crystal spacing and Bragg equation. -/
def nanometersValue (length : LengthMagnitude) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- The picometer readout used by the displayed answer choices. -/
def picometersValue (length : LengthMagnitude) : ℝ :=
  lengthValueIn LengthUnit.picometers length

/-- Convert a scalar angle readout in degrees to radians. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- The two spectral components of the incident x-ray beam. -/
inductive SpectralLine where
  | shorter
  | longer
  deriving DecidableEq, Repr

/-- The four diffraction peaks, ordered from left to right in the figure. -/
inductive DiffractionPeak where
  | first
  | second
  | third
  | fourth
  deriving DecidableEq, Repr

/-- Labels printed on the two axes of the primary figure. -/
inductive FigureAxisLabel where
  | thetaDegrees
  | intensity
  deriving DecidableEq, Repr

/-- An x-ray beam consisting of two physical wavelength components. -/
structure TwoWavelengthXRayBeam where
  /-- Vacuum wavelength of each spectral component. -/
  wavelength : SpectralLine → LengthMagnitude

/-- The family of parallel reflecting planes in the crystal. -/
structure ReflectingCrystal where
  /-- Perpendicular spacing `d` between successive reflecting planes. -/
  reflectingPlaneSpacing : LengthMagnitude

/-
Only relative peak heights can be read from the unlabeled vertical scale, so
they are dimensionless nonnegative readouts rather than physical intensity
values in an invented unit.
-/
structure AngularDiffractionFigure where
  /-- The angle represented by the printed horizontal label `θₛ`, in degrees. -/
  thetaScaleDegrees : ℝ
  /-- Angular position of each visible peak, in degrees. -/
  peakAngleDegrees : DiffractionPeak → ℝ
  /-- Dimensionless height read from the graph's unspecified intensity scale. -/
  relativePeakIntensity : DiffractionPeak → NNReal
  horizontalAxisLabel : FigureAxisLabel
  verticalAxisLabel : FigureAxisLabel
  angleAxisStartsAtZero : Bool
  gridShown : Bool

/-
The peak family identified by the standard two-line Bragg interpretation of
the plotted pattern: peaks one and three belong to the shorter line, while
peaks two and four belong to the longer line.
-/
def spectralLineAtPeak : DiffractionPeak → SpectralLine
  | .first => .shorter
  | .second => .longer
  | .third => .shorter
  | .fourth => .longer

/-- The corresponding first- or second-order Bragg reflection. -/
def diffractionOrderAtPeak : DiffractionPeak → ℕ
  | .first => 1
  | .second => 1
  | .third => 2
  | .fourth => 2

/-
Problem-text and primary-figure readouts.  The peak-location bands record the
limited precision of reading the unnumbered grid.  In particular, the second
peak lies at about `0.59 θₛ`, and the fourth near `1.2 θₛ`.

No wavelength or answer-choice value occurs in this predicate.
-/
def MatchesProblemAndFigureReadouts
    (crystal : ReflectingCrystal)
    (figure : AngularDiffractionFigure) : Prop :=
  nanometersValue crystal.reflectingPlaneSpacing = 94 / 100 ∧
    figure.thetaScaleDegrees = 2 ∧
    figure.horizontalAxisLabel = .thetaDegrees ∧
    figure.verticalAxisLabel = .intensity ∧
    figure.angleAxisStartsAtZero = true ∧
    figure.gridShown = true ∧
    7 / 20 * figure.thetaScaleDegrees ≤
      figure.peakAngleDegrees .first ∧
    figure.peakAngleDegrees .first ≤
      2 / 5 * figure.thetaScaleDegrees ∧
    23 / 40 * figure.thetaScaleDegrees ≤
      figure.peakAngleDegrees .second ∧
    figure.peakAngleDegrees .second ≤
      3 / 5 * figure.thetaScaleDegrees ∧
    3 / 4 * figure.thetaScaleDegrees ≤
      figure.peakAngleDegrees .third ∧
    figure.peakAngleDegrees .third ≤
      17 / 20 * figure.thetaScaleDegrees ∧
    23 / 20 * figure.thetaScaleDegrees ≤
      figure.peakAngleDegrees .fourth ∧
    figure.peakAngleDegrees .fourth ≤
      5 / 4 * figure.thetaScaleDegrees ∧
    figure.relativePeakIntensity .fourth <
      figure.relativePeakIntensity .third ∧
    figure.relativePeakIntensity .third <
      figure.relativePeakIntensity .second ∧
    figure.relativePeakIntensity .second <
      figure.relativePeakIntensity .first

/-
Positivity and the strict ordering that gives the two spectral-line labels
their physical meaning.  This contains no numerical wavelength conclusion.
-/
def HasPhysicalTwoLineParameters
    (beam : TwoWavelengthXRayBeam)
    (crystal : ReflectingCrystal) : Prop :=
  0 < nanometersValue crystal.reflectingPlaneSpacing ∧
    0 < picometersValue (beam.wavelength .shorter) ∧
    picometersValue (beam.wavelength .shorter) <
      picometersValue (beam.wavelength .longer)

/-
Bragg's law `n λ = 2 d sin θ` for every displayed peak.  Nanometer readouts are
used on both sides, and the degree readout from the graph is converted to the
radian argument expected by `Real.sin`.

This is a governing-law interface; it does not state the requested wavelength.
-/
structure SatisfiesTwoLineBraggLaws
    (beam : TwoWavelengthXRayBeam)
    (crystal : ReflectingCrystal)
    (figure : AngularDiffractionFigure) : Prop where
  peakAnglesPhysical :
    ∀ peak,
      0 < figure.peakAngleDegrees peak ∧
        figure.peakAngleDegrees peak < 90
  braggEquation :
    ∀ peak,
      (diffractionOrderAtPeak peak : ℝ) *
          nanometersValue (beam.wavelength (spectralLineAtPeak peak)) =
        2 * nanometersValue crystal.reflectingPlaneSpacing *
          Real.sin (degreesToRadians (figure.peakAngleDegrees peak))

/-- Labels of the four answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The wavelength printed beside each answer label, in picometers. -/
def answerWavelengthPicometers : AnswerChoice → ℝ
  | .A => 30
  | .B => 35
  | .C => 38
  | .D => 25

/-
A displayed answer is selected when its printed wavelength is strictly closer
to the inferred longer wavelength than every other displayed value.  This
matches the precision of extracting an angle from the graph.
-/
def IsUniqueClosestDisplayedAnswer
    (beam : TwoWavelengthXRayBeam) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |picometersValue (beam.wavelength .longer) -
        answerWavelengthPicometers choice| <
      |picometersValue (beam.wavelength .longer) -
        answerWavelengthPicometers other|

/-
The second first-order peak, the `0.94 nm` plane spacing, and Bragg's law put
the longer wavelength between `37 pm` and `40 pm`.  This numerical interval is
a derived conclusion, not a figure or law assumption.
-/
lemma longerWavelengthPicometers_bounds
    (beam : TwoWavelengthXRayBeam)
    (crystal : ReflectingCrystal)
    (figure : AngularDiffractionFigure)
    (h_readouts : MatchesProblemAndFigureReadouts crystal figure)
    (h_physical : HasPhysicalTwoLineParameters beam crystal)
    (h_bragg : SatisfiesTwoLineBraggLaws beam crystal figure) :
    37 < picometersValue (beam.wavelength .longer) ∧
      picometersValue (beam.wavelength .longer) < 40 := by
  exact by
      have picometers_eq_thousand_nanometers (length : LengthMagnitude) :
          picometersValue length = 1000 * nanometersValue length := by
        rw [picometersValue, nanometersValue, lengthValueIn, lengthValueIn]
        rw [length.2 ({ UnitChoices.SI with length := LengthUnit.nanometers })
          ({ UnitChoices.SI with length := LengthUnit.picometers })]
        simp [UnitChoices.dimScale, LengthUnit.picometers, LengthUnit.nanometers,
          LengthUnit.scale, LengthUnit.div_eq_val]
        left
        field_simp [LengthUnit.val_ne_zero]
        norm_num
        rfl

      rcases h_readouts with
        ⟨h_spacing, h_scale, _, _, _, _, _, _, h_second_lower, h_second_upper, _⟩
      have h_second_physical := h_bragg.peakAnglesPhysical .second
      have h_bragg_second := h_bragg.braggEquation .second
      simp [diffractionOrderAtPeak, spectralLineAtPeak] at h_bragg_second
      have h_wavelength :
          picometersValue (beam.wavelength .longer) =
            1880 * Real.sin
              (degreesToRadians (figure.peakAngleDegrees .second)) := by
        rw [picometers_eq_thousand_nanometers]
        rw [h_bragg_second, h_spacing]
        ring

      have sin_add_le_of_nonneg (u v : ℝ)
          (hu : 0 ≤ Real.sin u) (hv : 0 ≤ Real.sin v) :
          Real.sin (u + v) ≤ Real.sin u + Real.sin v := by
        rw [Real.sin_add]
        calc
          Real.sin u * Real.cos v + Real.cos u * Real.sin v ≤
              Real.sin u * 1 + 1 * Real.sin v :=
            add_le_add
              (mul_le_mul_of_nonneg_left (Real.cos_le_one v) hu)
              (mul_le_mul_of_nonneg_right (Real.cos_le_one u) hv)
          _ = Real.sin u + Real.sin v := by ring

      have sin_five_formula (x : ℝ) :
          Real.sin (5 * x) =
            16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 + 5 * Real.sin x := by
        rw [show 5 * x = 2 * x + (2 * x + x) by ring, Real.sin_add,
          Real.sin_two_mul, Real.cos_two_mul, Real.sin_add, Real.cos_add,
          Real.sin_two_mul, Real.cos_two_mul]
        ring_nf
        rw [show Real.cos x ^ 4 = (Real.cos x ^ 2) ^ 2 by ring, Real.cos_sq']
        ring

      have h_sin_pi_div_thirty_two_bounds :
          (49 : ℝ) / 500 < Real.sin (Real.pi / 32) ∧
            Real.sin (Real.pi / 32) < (981 : ℝ) / 10000 := by
        rw [Real.sin_pi_div_thirty_two]
        have hs2_gt : (14142 : ℝ) / 10000 < Real.sqrt 2 := by
          rw [Real.lt_sqrt (by norm_num)]
          norm_num
        have hs2_lt : Real.sqrt 2 < (1414214 : ℝ) / 1000000 := by
          rw [Real.sqrt_lt' (by norm_num)]
          norm_num
        have hb_gt :
            (184775 : ℝ) / 100000 < Real.sqrt (2 + Real.sqrt 2) := by
          rw [Real.lt_sqrt (by norm_num)]
          norm_num
          linarith only [hs2_gt]
        have hb_lt :
            Real.sqrt (2 + Real.sqrt 2) < (18477592 : ℝ) / 10000000 := by
          rw [Real.sqrt_lt' (by norm_num)]
          norm_num
          linarith only [hs2_lt]
        have hc_gt :
            (1961506 : ℝ) / 1000000 <
              Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
          rw [Real.lt_sqrt (by norm_num)]
          norm_num
          linarith only [hb_gt]
        have hc_lt :
            Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
              (1961571 : ℝ) / 1000000 := by
          rw [Real.sqrt_lt' (by norm_num)]
          norm_num
          linarith only [hb_lt]
        constructor
        · rw [lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]
          norm_num
          linarith only [hc_lt]
        · rw [div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]
          norm_num
          linarith only [hc_gt]
      have h_sin_pi_div_thirty_two_lower :=
        h_sin_pi_div_thirty_two_bounds.1
      have h_sin_pi_div_thirty_two_upper :=
        h_sin_pi_div_thirty_two_bounds.2

      let a : ℝ := Real.pi / 160
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        positivity
      have h_sin_a_nonneg : 0 ≤ Real.sin a :=
        Real.sin_nonneg_of_nonneg_of_le_pi ha_nonneg (by
          dsimp [a]
          nlinarith only [Real.pi_pos])
      have h_sin_a_lower : (49 : ℝ) / 2500 < Real.sin a := by
        have ha_five_le_pi : 5 * a ≤ Real.pi := by
          dsimp [a]
          nlinarith only [Real.pi_pos]
        have hs2 : 0 ≤ Real.sin (2 * a) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
            (by linarith only [ha_nonneg, ha_five_le_pi])
        have hs3 : 0 ≤ Real.sin (3 * a) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
            (by linarith only [ha_nonneg, ha_five_le_pi])
        have hs4 : 0 ≤ Real.sin (4 * a) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
            (by linarith only [ha_nonneg, ha_five_le_pi])
        have h2 : Real.sin (2 * a) ≤ 2 * Real.sin a := by
          rw [show 2 * a = a + a by ring]
          simpa [two_mul] using
            sin_add_le_of_nonneg a a h_sin_a_nonneg h_sin_a_nonneg
        have h3 : Real.sin (3 * a) ≤ 3 * Real.sin a := by
          rw [show 3 * a = 2 * a + a by ring]
          exact (sin_add_le_of_nonneg (2 * a) a hs2 h_sin_a_nonneg).trans (by
            linarith only [h2])
        have h4 : Real.sin (4 * a) ≤ 4 * Real.sin a := by
          rw [show 4 * a = 3 * a + a by ring]
          exact (sin_add_le_of_nonneg (3 * a) a hs3 h_sin_a_nonneg).trans (by
            linarith only [h3])
        have h5 : Real.sin (5 * a) ≤ 5 * Real.sin a := by
          rw [show 5 * a = 4 * a + a by ring]
          exact (sin_add_le_of_nonneg (4 * a) a hs4 h_sin_a_nonneg).trans (by
            linarith only [h4])
        have ha_angle : 5 * a = Real.pi / 32 := by
          dsimp [a]
          ring
        rw [ha_angle] at h5
        linarith only [h_sin_pi_div_thirty_two_lower, h5]

      have h_cos_pi_div_thirty_two :
          (199 : ℝ) / 200 < Real.cos (Real.pi / 32) := by
        have hspos : 0 < Real.sin (Real.pi / 32) :=
          Real.sin_pos_of_pos_of_lt_pi (by positivity)
            (by nlinarith only [Real.pi_pos])
        have hssq :
            Real.sin (Real.pi / 32) ^ 2 < ((981 : ℝ) / 10000) ^ 2 := by
          nlinarith only [hspos, h_sin_pi_div_thirty_two_upper,
            mul_pos hspos (sub_pos.mpr h_sin_pi_div_thirty_two_upper)]
        have hc0 : 0 ≤ Real.cos (Real.pi / 32) :=
          Real.cos_nonneg_of_mem_Icc
            ⟨by nlinarith only [Real.pi_pos], by nlinarith only [Real.pi_pos]⟩
        nlinarith only [hc0, hssq,
          Real.sin_sq_add_cos_sq (Real.pi / 32)]

      have h_sin_pi_div_128_upper :
          Real.sin (Real.pi / 128) < (1 : ℝ) / 40 := by
        let z : ℝ := Real.pi / 128
        have hzpos : 0 < z := by
          dsimp [z]
          positivity
        have hsinzpos : 0 < Real.sin z :=
          Real.sin_pos_of_pos_of_lt_pi hzpos (by
            dsimp [z]
            nlinarith only [Real.pi_pos])
        have hcosz :
            (199 : ℝ) / 200 < Real.cos z := by
          exact lt_of_lt_of_le h_cos_pi_div_thirty_two
            (Real.cos_le_cos_of_nonneg_of_le_pi hzpos.le
              (by nlinarith only [Real.pi_pos]) (by
                dsimp [z]
                nlinarith only [Real.pi_pos]))
        have hcos2z :
            (199 : ℝ) / 200 < Real.cos (2 * z) := by
          exact lt_of_lt_of_le h_cos_pi_div_thirty_two
            (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
              (by nlinarith only [Real.pi_pos]) (by
                dsimp [z]
                nlinarith only [Real.pi_pos]))
        have hmul1 :
            ((199 : ℝ) / 200) * Real.sin z <
              Real.cos z * Real.sin z := by
          exact mul_lt_mul_of_pos_right hcosz hsinzpos
        have hmul2 :
            ((199 : ℝ) / 200) ^ 2 * Real.sin z <
              Real.cos (2 * z) * (Real.cos z * Real.sin z) := by
          calc
            ((199 : ℝ) / 200) ^ 2 * Real.sin z =
                ((199 : ℝ) / 200) *
                  (((199 : ℝ) / 200) * Real.sin z) := by ring
            _ < ((199 : ℝ) / 200) *
                  (Real.cos z * Real.sin z) :=
              mul_lt_mul_of_pos_left hmul1 (by norm_num)
            _ < Real.cos (2 * z) * (Real.cos z * Real.sin z) :=
              mul_lt_mul_of_pos_right hcos2z
                (mul_pos (lt_trans (by norm_num) hcosz) hsinzpos)
        have hidentity :
            Real.sin (Real.pi / 32) =
              4 * (Real.cos (2 * z) * (Real.cos z * Real.sin z)) := by
          rw [show Real.pi / 32 = 4 * z by
            dsimp [z]
            ring]
          rw [show 4 * z = 2 * (2 * z) by ring, Real.sin_two_mul,
            Real.sin_two_mul]
          ring
        dsimp [z] at hmul2 ⊢
        linarith only [hmul2, hidentity,
          h_sin_pi_div_thirty_two_upper]

      have h_sin_a_upper : Real.sin a < (197 : ℝ) / 10000 := by
        let s : ℝ := Real.sin a
        have ha_lt : a < Real.pi / 128 := by
          dsimp [a]
          nlinarith only [Real.pi_pos]
        have ha_upper : Real.pi / 128 ≤ Real.pi / 2 := by
          nlinarith only [Real.pi_pos]
        have hs_lt_sin128 : s < Real.sin (Real.pi / 128) := by
          dsimp [s]
          exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
            (by
              dsimp [a]
              nlinarith only [Real.pi_pos]) ha_upper ha_lt
        have hfive_formula :
            Real.sin (5 * a) = 16 * s ^ 5 - 20 * s ^ 3 + 5 * s := by
          simpa [s] using sin_five_formula a
        have hfive_angle : 5 * a = Real.pi / 32 := by
          dsimp [a]
          ring
        rw [hfive_angle] at hfive_formula
        by_contra hnot
        have hrs : (197 : ℝ) / 10000 ≤ s := le_of_not_gt hnot
        have hs0 : 0 ≤ s := by
          simpa [s] using h_sin_a_nonneg
        have hs_le : s ≤ (1 : ℝ) / 40 := by
          linarith only [hs_lt_sin128, h_sin_pi_div_128_upper]
        have hs_sq : s ^ 2 ≤ (1 : ℝ) / 1600 := by
          nlinarith only [hs0, hs_le,
            mul_nonneg hs0 (sub_nonneg.mpr hs_le)]
        have hs_cube : s ^ 3 ≤ s / 1600 := by
          nlinarith only [hs0, hs_sq,
            mul_nonneg hs0 (sub_nonneg.mpr hs_sq)]
        have hs_fifth : 0 ≤ s ^ 5 := by positivity
        nlinarith only [h_sin_pi_div_thirty_two_upper, hfive_formula,
          hrs, hs_cube, hs_fifth]

      have h_cos_pi_div_sixty_four :
          (1997 : ℝ) / 2000 < Real.cos (Real.pi / 64) := by
        have hc0 : 0 ≤ Real.cos (Real.pi / 64) :=
          Real.cos_nonneg_of_mem_Icc
            ⟨by nlinarith only [Real.pi_pos],
              by nlinarith only [Real.pi_pos]⟩
        have hsq := Real.cos_sq (Real.pi / 64)
        rw [show 2 * (Real.pi / 64) = Real.pi / 32 by ring] at hsq
        nlinarith only [hc0, hsq, h_cos_pi_div_thirty_two]

      have h_sin_pi_div_8192_lower :
          (19 : ℝ) / 50000 < Real.sin (Real.pi / 8192) := by
        let y : ℝ := Real.pi / 8192
        have hy256 : 256 * y = Real.pi / 32 := by
          dsimp [y]
          ring
        have hsin_nonneg (k : ℕ) (hk : k ≤ 256) :
            0 ≤ Real.sin ((k : ℝ) * y) := by
          have hkreal : (k : ℝ) ≤ 256 := by exact_mod_cast hk
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          · positivity
          · dsimp [y]
            nlinarith only [Real.pi_pos, hkreal]
        have hstep (k : ℕ) (hk : k ≤ 128) :
            Real.sin (((2 * k : ℕ) : ℝ) * y) ≤
              2 * Real.sin ((k : ℝ) * y) := by
          rw [show ((2 * k : ℕ) : ℝ) * y =
            (k : ℝ) * y + (k : ℝ) * y by norm_num; ring]
          simpa [two_mul] using
            sin_add_le_of_nonneg ((k : ℝ) * y) ((k : ℝ) * y)
              (hsin_nonneg k (by omega)) (hsin_nonneg k (by omega))
        have h1 := hstep 1 (by norm_num)
        have h2 := hstep 2 (by norm_num)
        have h4 := hstep 4 (by norm_num)
        have h8 := hstep 8 (by norm_num)
        have h16 := hstep 16 (by norm_num)
        have h32 := hstep 32 (by norm_num)
        have h64 := hstep 64 (by norm_num)
        have h128 := hstep 128 (by norm_num)
        norm_num at h1 h2 h4 h8 h16 h32 h64 h128
        rw [hy256] at h128
        dsimp [y] at h1
        linarith only [h_sin_pi_div_thirty_two_lower,
          h1, h2, h4, h8, h16, h32, h64, h128]

      have h_sin_pi_div_2048_upper :
          Real.sin (Real.pi / 2048) < (31 : ℝ) / 20000 := by
        let y : ℝ := Real.pi / 2048
        have hy64 : 64 * y = Real.pi / 32 := by
          dsimp [y]
          ring
        have hcos (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ 32) :
            (1997 : ℝ) / 2000 < Real.cos ((k : ℝ) * y) := by
          have hkreal : (k : ℝ) ≤ 32 := by exact_mod_cast hkle
          have hangle_nonneg : 0 ≤ (k : ℝ) * y := by positivity
          have hangle_le : (k : ℝ) * y ≤ Real.pi / 64 := by
            dsimp [y]
            nlinarith only [Real.pi_pos, hkreal]
          exact lt_of_lt_of_le h_cos_pi_div_sixty_four
            (Real.cos_le_cos_of_nonneg_of_le_pi hangle_nonneg
              (by nlinarith only [Real.pi_pos]) hangle_le)
        have hsinpos (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ 64) :
            0 < Real.sin ((k : ℝ) * y) := by
          have hkreal : (k : ℝ) ≤ 64 := by exact_mod_cast hkle
          apply Real.sin_pos_of_pos_of_lt_pi
          · positivity
          · dsimp [y]
            nlinarith only [Real.pi_pos, hkreal]
        have hstep (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ 32) :
            (1997 : ℝ) / 1000 * Real.sin ((k : ℝ) * y) <
              Real.sin (((2 * k : ℕ) : ℝ) * y) := by
          rw [show ((2 * k : ℕ) : ℝ) * y =
            2 * ((k : ℝ) * y) by norm_num; ring, Real.sin_two_mul]
          have hs := hsinpos k hkpos (by omega)
          have hc := hcos k hkpos hkle
          have hmul := mul_lt_mul_of_pos_right hc hs
          linarith only [hmul]
        have h1 := hstep 1 (by norm_num) (by norm_num)
        have h2 := hstep 2 (by norm_num) (by norm_num)
        have h4 := hstep 4 (by norm_num) (by norm_num)
        have h8 := hstep 8 (by norm_num) (by norm_num)
        have h16 := hstep 16 (by norm_num) (by norm_num)
        have h32 := hstep 32 (by norm_num) (by norm_num)
        norm_num at h1 h2 h4 h8 h16 h32
        rw [hy64] at h32
        dsimp [y] at h1
        linarith only [h_sin_pi_div_thirty_two_upper,
          h1, h2, h4, h8, h16, h32]

      have h_cos_a : (99 : ℝ) / 100 < Real.cos a := by
        have ha_le : a ≤ Real.pi / 32 := by
          dsimp [a]
          nlinarith only [Real.pi_pos]
        exact lt_of_lt_of_le (by
          linarith only [h_cos_pi_div_thirty_two])
          (Real.cos_le_cos_of_nonneg_of_le_pi ha_nonneg
            (by nlinarith only [Real.pi_pos]) ha_le)

      let delta : ℝ := Real.pi / 7200
      have hdelta_pos : 0 < delta := by
        dsimp [delta]
        positivity
      have h_delta_lt_pi_div_32 : delta < Real.pi / 32 := by
        dsimp [delta]
        nlinarith only [Real.pi_pos]
      have h_cos_delta : (99 : ℝ) / 100 < Real.cos delta := by
        exact lt_of_lt_of_le (by
          linarith only [h_cos_pi_div_thirty_two])
          (Real.cos_le_cos_of_nonneg_of_le_pi hdelta_pos.le
            (by nlinarith only [Real.pi_pos]) h_delta_lt_pi_div_32.le)
      have h_sin_delta : (19 : ℝ) / 50000 < Real.sin delta := by
        have hy_lt : Real.pi / 8192 < delta := by
          dsimp [delta]
          nlinarith only [Real.pi_pos]
        have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
          (by nlinarith only [Real.pi_pos])
          (by
            dsimp [delta]
            nlinarith only [Real.pi_pos]) hy_lt
        linarith only [h_sin_pi_div_8192_lower, hmono]
      have h_sin_lower_angle :
          (37 : ℝ) / 1880 < Real.sin (a + delta) := by
        rw [Real.sin_add]
        have hmul1 :
            ((49 : ℝ) / 2500) * ((99 : ℝ) / 100) <
              Real.sin a * Real.cos delta := by
          calc
            ((49 : ℝ) / 2500) * ((99 : ℝ) / 100) <
                Real.sin a * ((99 : ℝ) / 100) :=
              mul_lt_mul_of_pos_right h_sin_a_lower (by norm_num)
            _ < Real.sin a * Real.cos delta :=
              mul_lt_mul_of_pos_left h_cos_delta
                (lt_trans (by norm_num) h_sin_a_lower)
        have hmul2 :
            ((99 : ℝ) / 100) * ((19 : ℝ) / 50000) <
              Real.cos a * Real.sin delta := by
          calc
            ((99 : ℝ) / 100) * ((19 : ℝ) / 50000) <
                Real.cos a * ((19 : ℝ) / 50000) :=
              mul_lt_mul_of_pos_right h_cos_a (by norm_num)
            _ < Real.cos a * Real.sin delta :=
              mul_lt_mul_of_pos_left h_sin_delta
                (lt_trans (by norm_num) h_cos_a)
        linarith only [hmul1, hmul2]

      let epsilon : ℝ := Real.pi / 2048
      have hepsilon_pos : 0 < epsilon := by
        dsimp [epsilon]
        positivity
      have h_sin_epsilon_nonneg : 0 ≤ Real.sin epsilon :=
        Real.sin_nonneg_of_nonneg_of_le_pi hepsilon_pos.le (by
          dsimp [epsilon]
          nlinarith only [Real.pi_pos])
      have h_sin_upper_angle :
          Real.sin (a + epsilon) < (1 : ℝ) / 47 := by
        have hadd := sin_add_le_of_nonneg a epsilon h_sin_a_nonneg
          h_sin_epsilon_nonneg
        dsimp [epsilon] at hadd
        linarith only [hadd, h_sin_a_upper,
          h_sin_pi_div_2048_upper]

      have h_angle_lower :
          a + delta ≤ degreesToRadians (figure.peakAngleDegrees .second) := by
        have hdegrees :
            (23 : ℝ) / 20 ≤ figure.peakAngleDegrees .second := by
          rw [h_scale] at h_second_lower
          norm_num at h_second_lower ⊢
          linarith only [h_second_lower]
        dsimp [a, delta, degreesToRadians]
        have hpi := Real.pi_pos
        nlinarith only [hdegrees, hpi,
          mul_nonneg (sub_nonneg.mpr hdegrees) hpi.le]
      have h_angle_upper :
          degreesToRadians (figure.peakAngleDegrees .second) < a + epsilon := by
        have hdegrees :
            figure.peakAngleDegrees .second ≤ (6 : ℝ) / 5 := by
          rw [h_scale] at h_second_upper
          norm_num at h_second_upper ⊢
          linarith only [h_second_upper]
        dsimp [a, epsilon, degreesToRadians]
        have hpi := Real.pi_pos
        nlinarith only [hdegrees, hpi,
          mul_nonneg (sub_nonneg.mpr hdegrees) hpi.le]
      have h_radian_pos :
          0 < degreesToRadians (figure.peakAngleDegrees .second) := by
        have hdegrees := h_second_physical.1
        dsimp [degreesToRadians]
        have hmul := mul_pos hdegrees Real.pi_pos
        nlinarith only [hmul]
      have h_radian_lt_half_pi :
          degreesToRadians (figure.peakAngleDegrees .second) < Real.pi / 2 := by
        have hdegrees := h_second_physical.2
        dsimp [degreesToRadians]
        nlinarith only [Real.pi_pos, hdegrees,
          mul_pos (sub_pos.mpr hdegrees) Real.pi_pos]
      have h_sin_lower :
          (37 : ℝ) / 1880 <
            Real.sin (degreesToRadians (figure.peakAngleDegrees .second)) := by
        exact h_sin_lower_angle.trans_le
          (Real.sin_le_sin_of_le_of_le_pi_div_two
            (by nlinarith only [Real.pi_pos, ha_nonneg, hdelta_pos])
              h_radian_lt_half_pi.le h_angle_lower)
      have h_sin_upper :
          Real.sin (degreesToRadians (figure.peakAngleDegrees .second)) <
            (1 : ℝ) / 47 := by
        have h_a_epsilon_le_half_pi : a + epsilon ≤ Real.pi / 2 := by
          dsimp [a, epsilon]
          nlinarith only [Real.pi_pos]
        exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two
          (by nlinarith only [h_radian_pos, Real.pi_pos])
            h_a_epsilon_le_half_pi h_angle_upper).trans
            h_sin_upper_angle
      rw [h_wavelength]
      constructor <;> nlinarith only [h_sin_lower, h_sin_upper]

/-
The longer wavelength is therefore represented by the uniquely closest
displayed value `38 pm`, namely answer choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0081:target`.
-/
theorem problem_phyx_mini_0081
    (beam : TwoWavelengthXRayBeam)
    (crystal : ReflectingCrystal)
    (figure : AngularDiffractionFigure)
    (h_readouts : MatchesProblemAndFigureReadouts crystal figure)
    (h_physical : HasPhysicalTwoLineParameters beam crystal)
    (h_bragg : SatisfiesTwoLineBraggLaws beam crystal figure) :
    IsUniqueClosestDisplayedAnswer beam .C ∧
      answerWavelengthPicometers .C = 38 := by
  rcases longerWavelengthPicometers_bounds beam crystal figure
    h_readouts h_physical h_bragg with ⟨hlower, hupper⟩
  constructor
  · intro other hother
    cases other with
    | A =>
        simp only [answerWavelengthPicometers]
        rw [abs_of_pos (show
          0 < picometersValue (beam.wavelength .longer) - 30 by linarith)]
        rw [abs_lt]
        constructor <;> linarith
    | B =>
        simp only [answerWavelengthPicometers]
        rw [abs_of_pos (show
          0 < picometersValue (beam.wavelength .longer) - 35 by linarith)]
        rw [abs_lt]
        constructor <;> linarith
    | C => exact (hother rfl).elim
    | D =>
        simp only [answerWavelengthPicometers]
        rw [abs_of_pos (show
          0 < picometersValue (beam.wavelength .longer) - 25 by linarith)]
        rw [abs_lt]
        constructor <;> linarith
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0081
