import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.Basic

/-!
# Dispersion of visible light through a silica flint-glass prism

Angles represented by real numbers in this file are measured in radians.  The
refractive-index function returns dimensionless scalar readouts for a specified
optical medium and visible-light color.  Physlib's unit infrastructure is
imported to make the dimensional grounding explicit; neither plane angles nor
refractive indices require a nontrivial `Dimensionful` wrapper in this model.
-/

namespace PhyXMiniProblems.Problem0008

/-- The six outgoing ray labels shown on the screen, ordered from red to violet. -/
inductive VisibleColor where
  | red
  | orange
  | yellow
  | green
  | blue
  | violet
  deriving DecidableEq, Repr

/-- The two media crossed by each ray in the prism experiment. -/
inductive OpticalMedium where
  | air
  | silicaFlintGlass
  deriving DecidableEq, Repr

/-- Convert a scalar angle read in degrees to its value in radians. -/
noncomputable def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/--
Experimental data shared by every color: a color-dependent dimensionless
refractive index, the incidence angle, and the triangular prism's apex angle.
-/
structure PrismSetup where
  refractiveIndex : OpticalMedium → VisibleColor → ℝ
  incidenceAngleRadians : ℝ
  apexAngleRadians : ℝ

/--
The four directed angle readouts needed to trace one colored ray through the
two faces of the prism.
-/
structure PrismRayAngles (color : VisibleColor) where
  firstRefractionRadians : ℝ
  secondIncidenceRadians : ℝ
  emergenceRadians : ℝ
  deviationRadians : ℝ

/--
The geometrical-optics laws for one color.  The interval conditions select the
physical, principal-angle branch of Snell's law.
-/
structure SatisfiesPrismRayLaws
    (setup : PrismSetup) {color : VisibleColor}
    (ray : PrismRayAngles color) : Prop where
  airIndex_pos : 0 < setup.refractiveIndex .air color
  glassIndex_pos : 0 < setup.refractiveIndex .silicaFlintGlass color
  incidence_nonneg : 0 ≤ setup.incidenceAngleRadians
  incidence_le : setup.incidenceAngleRadians ≤ Real.pi / 2
  firstRefraction_nonneg : 0 ≤ ray.firstRefractionRadians
  firstRefraction_le : ray.firstRefractionRadians ≤ Real.pi / 2
  secondIncidence_nonneg : 0 ≤ ray.secondIncidenceRadians
  secondIncidence_le : ray.secondIncidenceRadians ≤ Real.pi / 2
  emergence_nonneg : 0 ≤ ray.emergenceRadians
  emergence_le : ray.emergenceRadians ≤ Real.pi / 2
  firstFaceSnell :
    setup.refractiveIndex .air color * Real.sin setup.incidenceAngleRadians =
      setup.refractiveIndex .silicaFlintGlass color *
        Real.sin ray.firstRefractionRadians
  prismAngleGeometry :
    ray.firstRefractionRadians + ray.secondIncidenceRadians =
      setup.apexAngleRadians
  secondFaceSnell :
    setup.refractiveIndex .silicaFlintGlass color *
        Real.sin ray.secondIncidenceRadians =
      setup.refractiveIndex .air color * Real.sin ray.emergenceRadians
  deviationGeometry :
    ray.deviationRadians =
      setup.incidenceAngleRadians + ray.emergenceRadians - setup.apexAngleRadians

/-- The angular separation from the red ray to the violet ray in the figure. -/
def angularSpreadRadians
    (redRay : PrismRayAngles .red) (violetRay : PrismRayAngles .violet) : ℝ :=
  violetRay.deviationRadians - redRay.deviationRadians

/--
The two angle labels explicitly drawn in the source figure.  The colored rays
terminate on the screen in the order represented by `VisibleColor` above.
-/
structure DispersionFigureReadout where
  redDeviationRadians : ℝ
  angularSpreadRadians : ℝ

/-- Multiple-choice labels from the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed degree value attached to each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 4.37
  | .B => 8.74
  | .C => 4.61
  | .D => 2.11

/--
For the stated glass indices and prism geometry, the red-to-violet angular
spread is answer C to the precision displayed by the answer choices.

The tolerance `0.005°` expresses rounding to the nearest hundredth of a degree;
the exact numerical value is approximately `4.6118°`.
-/
theorem angularSpread_is_answer_C
    (setup : PrismSetup)
    (redRay : PrismRayAngles .red)
    (violetRay : PrismRayAngles .violet)
    (figure : DispersionFigureReadout)
    (h_air_red : setup.refractiveIndex .air .red = 1)
    (h_air_violet : setup.refractiveIndex .air .violet = 1)
    (h_glass_red : setup.refractiveIndex .silicaFlintGlass .red = 1.62)
    (h_glass_violet : setup.refractiveIndex .silicaFlintGlass .violet = 1.66)
    (h_incidence : setup.incidenceAngleRadians = degreesToRadians 50)
    (h_apex : setup.apexAngleRadians = degreesToRadians 60)
    (h_red_laws : SatisfiesPrismRayLaws setup redRay)
    (h_violet_laws : SatisfiesPrismRayLaws setup violetRay)
    (h_red_figure : figure.redDeviationRadians = redRay.deviationRadians)
    (h_spread_figure :
      figure.angularSpreadRadians = angularSpreadRadians redRay violetRay) :
    abs (figure.angularSpreadRadians -
      degreesToRadians (answerAngleDegrees .C)) ≤ degreesToRadians 0.005 := by
      have sin_lt_local {x : ℝ} (hx0 : 0 < x) : Real.sin x < x := by
        rcases lt_or_ge 1 x with hx1 | hx1
        · exact (Real.sin_le_one x).trans_lt hx1
        have hx : |x| = x := abs_of_nonneg hx0.le
        have hb := le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
        rw [sub_le_iff_le_add', hx] at hb
        apply hb.trans_lt
        rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
        refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx0 3)
        apply pow_le_pow_of_le_one hx0.le hx1
        simp
  
      have sin_gt_cube {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
          x - x ^ 3 / 4 < Real.sin x := by
        have hx : |x| = x := abs_of_nonneg hx0.le
        have hb := neg_le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
        rw [le_sub_iff_add_le, hx] at hb
        refine lt_of_lt_of_le ?_ hb
        have hcalc : x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
          norm_num [div_eq_mul_inv, ← mul_sub]
        rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
          ← lt_sub_iff_add_lt', hcalc]
        refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx0 3)
        apply pow_le_pow_of_le_one hx0.le hx1
        simp
  
      have pi_gt_series (n : ℕ) :
          2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) < Real.pi := by
        have h :
            Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) <
              Real.pi := by
          rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
          focus
            apply sin_lt_local
            apply div_pos Real.pi_pos
          all_goals apply pow_pos <;> norm_num
        refine lt_of_le_of_lt (le_of_eq ?_) h
        rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
        simp
  
      have lower_start (n : ℕ) {a : ℝ}
          (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
            (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) : a < Real.pi := by
        refine lt_of_le_of_lt ?_ (pi_gt_series n)
        rw [mul_comm]
        refine (div_le_iff₀ (pow_pos (by simp) _)).mp (Real.le_sqrt_of_sq_le ?_)
        rwa [le_sub_comm,
          show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by rw [Nat.cast_zero, zero_div]]
  
      have step_up (c d : ℕ) {a b n : ℕ} {z : ℝ}
          (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
          (hb : 0 < b) (hd : 0 < d)
          (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
          Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
        refine le_trans ?_ hz
        rw [Real.sqrtTwoAddSeries_succ]
        apply Real.sqrtTwoAddSeries_monotone_left
        have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
        have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
        rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg), div_pow,
          add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
          div_le_div_iff₀ hb' (pow_pos hd' _)]
        exact_mod_cast h
  
      have pi_lt_series (n : ℕ) :
          Real.pi <
            2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) + 1 / 4 ^ n := by
        have h : Real.pi <
            (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 +
                1 / (2 ^ n) ^ 3 / 4) * (2 : ℝ) ^ (n + 2) := by
          rw [← div_lt_iff₀ (by simp), ← Real.sin_pi_over_two_pow_succ,
            ← sub_lt_iff_lt_add']
          calc
            Real.pi / 2 ^ (n + 2) - Real.sin (Real.pi / 2 ^ (n + 2)) <
                (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
              sub_lt_comm.1 <| sin_gt_cube (by positivity) <|
                div_le_one_of_le₀ (by
                  calc
                    Real.pi ≤ 4 := Real.pi_le_four
                    _ = 2 ^ (0 + 2) := by norm_num
                    _ ≤ 2 ^ (n + 2) := by gcongr <;> norm_num) (by positivity)
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
        simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div, ← pow_add]
        rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
          mul_inv_eq_iff_eq_mul₀, ← pow_add]
        · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc, mul_comm n]
        all_goals norm_num
  
      have upper_start (n : ℕ) {a : ℝ}
          (h : (2 : ℝ) - ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
            Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
          (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) : Real.pi < a := by
        refine lt_of_lt_of_le (pi_lt_series n) ?_
        rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left, sub_le_comm]
        · rwa [Nat.cast_zero, zero_div] at h
        · exact div_nonneg (sub_nonneg.2 h₂) (pow_nonneg (le_of_lt zero_lt_two) _)
        · exact pow_pos zero_lt_two _
  
      have step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
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
  
      have hpi_lower : (3.1415 : ℝ) < Real.pi := by
        apply lower_start 6
        apply step_up 1970 1393 <;> try norm_num1
        apply step_up 3010 1629 <;> try norm_num1
        apply step_up 11689 5959 <;> try norm_num1
        apply step_up 10127 5088 <;> try norm_num1
        apply step_up 33997 17019 <;> try norm_num1
        apply step_up 23235 11621 <;> try norm_num1
        simp [Real.sqrtTwoAddSeries]
        all_goals norm_num1
  
      have hpi_upper : Real.pi < (3.1416 : ℝ) := by
        apply upper_start 9
        · apply step_down 4756 3363 <;> try norm_num1
          apply step_down 14965 8099 <;> try norm_num1
          apply step_down 21183 10799 <;> try norm_num1
          apply step_down 49188 24713 <;> try norm_num1
          apply step_down (2 * 22000 - 53) 22000 <;> try norm_num1
          apply step_down (2 * 117869 - 71) 117869 <;> try norm_num1
          apply step_down (2 * 312092 - 47) 312092 <;> try norm_num1
          apply step_down (2 * 451533 - 17) 451533 <;> try norm_num1
          apply step_down (2 * 424971 - 4) 424971 <;> try norm_num1
          simp [Real.sqrtTwoAddSeries]
          all_goals norm_num1
        · norm_num
  
      have small_bounds {x L U : ℝ} (hL0 : 0 ≤ L) (hLx : L ≤ x)
          (hxU : x ≤ U) (hU1 : U ≤ 1) :
          L - U ^ 3 / 6 - U ^ 4 * (5 / 96) ≤ Real.sin x ∧
          Real.sin x ≤ U - L ^ 3 / 6 + U ^ 4 * (5 / 96) ∧
          1 - U ^ 2 / 2 - U ^ 4 * (5 / 96) ≤ Real.cos x ∧
          Real.cos x ≤ 1 - L ^ 2 / 2 + U ^ 4 * (5 / 96) := by
        have hx0 : 0 ≤ x := hL0.trans hLx
        have hU0 : 0 ≤ U := hx0.trans hxU
        have hx1 : |x| ≤ 1 := by
          rw [abs_of_nonneg hx0]
          exact hxU.trans hU1
        have hL2 : L ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hL0 hLx 2
        have hL3 : L ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hL0 hLx 3
        have hx2 : x ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hx0 hxU 2
        have hx3 : x ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ hx0 hxU 3
        have hx4 : x ^ 4 ≤ U ^ 4 := pow_le_pow_left₀ hx0 hxU 4
        have hs := abs_le.mp (Real.sin_bound hx1)
        have hc := abs_le.mp (Real.cos_bound hx1)
        rw [abs_of_nonneg hx0] at hs hc
        constructor
        · linarith only [hs.1, hLx, hx3, hx4]
        constructor
        · linarith only [hs.2, hxU, hL3, hx4]
        constructor
        · linarith only [hc.1, hx2, hx4]
        · linarith only [hc.2, hL2, hx4]
  
      have mul_bounds {a b al au bl bu : ℝ}
          (hal0 : 0 ≤ al) (hau0 : 0 ≤ au) (hbl0 : 0 < bl)
          (hal : al < a) (hau : a < au) (hbl : bl < b) (hbu : b < bu) :
          al * bl < a * b ∧ a * b < au * bu := by
        exact
          ⟨mul_lt_mul hal hbl.le hbl0 (hal0.trans hal.le),
            mul_lt_mul hau hbu.le (hbl0.trans hbl) hau0⟩
  
      let t : ℝ := Real.pi / 72
      have htL : (3.1415 : ℝ) / 72 ≤ t := by
        dsimp [t]
        linarith
      have htU : t ≤ (3.1416 : ℝ) / 72 := by
        dsimp [t]
        linarith
      have ht := small_bounds (x := t) (L := (3.1415 : ℝ) / 72)
        (U := (3.1416 : ℝ) / 72) (by norm_num) htL htU (by norm_num)
      have hs_t : (0.0436179103 : ℝ) < Real.sin t ∧
          Real.sin t < (0.0436196781 : ℝ) := by
        constructor <;> nlinarith only [ht.1, ht.2.1]
      have hc_t : (0.9990478773 : ℝ) < Real.cos t ∧
          Real.cos t < (0.9990483155 : ℝ) := by
        constructor <;> nlinarith only [ht.2.2.1, ht.2.2.2]
      have hprod_t := mul_bounds (by norm_num : (0 : ℝ) ≤ 0.0436179103) (by norm_num)
        (by norm_num : (0 : ℝ) < 0.9990478773) hs_t.1 hs_t.2 hc_t.1 hc_t.2
      have hsin2 : Real.sin (2 * t) = 2 * Real.sin t * Real.cos t := by
        simpa [two_mul] using Real.sin_two_mul t
      have hcos2 : Real.cos (2 * t) = 2 * Real.cos t ^ 2 - 1 := by
        simpa using Real.cos_two_mul t
      have hs_2t : (0.0871527613 : ℝ) < Real.sin (2 * t) ∧
          Real.sin (2 * t) < (0.0871563320 : ℝ) := by
        constructor
        · calc
            (0.0871527613 : ℝ) <
                2 * ((0.0436179103 : ℝ) * 0.9990478773) := by norm_num
            _ < 2 * (Real.sin t * Real.cos t) :=
              mul_lt_mul_of_pos_left hprod_t.1 (by norm_num)
            _ = Real.sin (2 * t) := by linarith only [hsin2]
        · calc
            Real.sin (2 * t) = 2 * (Real.sin t * Real.cos t) := by
              linarith only [hsin2]
            _ < 2 * ((0.0436196781 : ℝ) * 0.9990483155) :=
              mul_lt_mul_of_pos_left hprod_t.2 (by norm_num)
            _ < (0.0871563320 : ℝ) := by norm_num
      have hc_2t : (0.9961933222 : ℝ) < Real.cos (2 * t) ∧
          Real.cos (2 * t) < (0.9961950735 : ℝ) := by
        have hsquare_lower :
            (0.9990478773 : ℝ) ^ 2 < Real.cos t ^ 2 :=
          pow_lt_pow_left₀ hc_t.1 (by norm_num) (by norm_num)
        have hsquare_upper :
            Real.cos t ^ 2 < (0.9990483155 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hc_t.2 (by nlinarith only [hc_t.1]) (by norm_num)
        constructor
        · calc
            (0.9961933222 : ℝ) <
                2 * (0.9990478773 : ℝ) ^ 2 - 1 := by norm_num
            _ < 2 * Real.cos t ^ 2 - 1 :=
              sub_lt_sub_right
                (mul_lt_mul_of_pos_left hsquare_lower (by norm_num)) 1
            _ = Real.cos (2 * t) := hcos2.symm
        · calc
            Real.cos (2 * t) = 2 * Real.cos t ^ 2 - 1 := hcos2
            _ < 2 * (0.9990483155 : ℝ) ^ 2 - 1 :=
              sub_lt_sub_right
                (mul_lt_mul_of_pos_left hsquare_upper (by norm_num)) 1
            _ < (0.9961950735 : ℝ) := by norm_num
      have hprod_2t := mul_bounds (by norm_num : (0 : ℝ) ≤ 0.0871527613) (by norm_num)
        (by norm_num : (0 : ℝ) < 0.9961933222) hs_2t.1 hs_2t.2 hc_2t.1 hc_2t.2
      have hsin4 :
          Real.sin (4 * t) = 2 * Real.sin (2 * t) * Real.cos (2 * t) := by
        rw [show (4 : ℝ) * t = 2 * (2 * t) by ring, Real.sin_two_mul]
      have hcos4 : Real.cos (4 * t) = 2 * Real.cos (2 * t) ^ 2 - 1 := by
        rw [show (4 : ℝ) * t = 2 * (2 * t) by ring, Real.cos_two_mul]
      have hs_4t : (0.1736419976 : ℝ) < Real.sin (4 * t) ∧
          Real.sin (4 * t) < (0.1736494172 : ℝ) := by
        constructor
        · calc
            (0.1736419976 : ℝ) <
                2 * ((0.0871527613 : ℝ) * 0.9961933222) := by norm_num
            _ < 2 * (Real.sin (2 * t) * Real.cos (2 * t)) :=
              mul_lt_mul_of_pos_left hprod_2t.1 (by norm_num)
            _ = Real.sin (4 * t) := by linarith only [hsin4]
        · calc
            Real.sin (4 * t) =
                2 * (Real.sin (2 * t) * Real.cos (2 * t)) := by
              linarith only [hsin4]
            _ < 2 * ((0.0871563320 : ℝ) * 0.9961950735) :=
              mul_lt_mul_of_pos_left hprod_2t.2 (by norm_num)
            _ < (0.1736494172 : ℝ) := by norm_num
      have hc_4t : (0.9848022703 : ℝ) < Real.cos (4 * t) ∧
          Real.cos (4 * t) < (0.9848092490 : ℝ) := by
        have hsquare_lower :
            (0.9961933222 : ℝ) ^ 2 < Real.cos (2 * t) ^ 2 :=
          pow_lt_pow_left₀ hc_2t.1 (by norm_num) (by norm_num)
        have hsquare_upper :
            Real.cos (2 * t) ^ 2 < (0.9961950735 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hc_2t.2 (by nlinarith only [hc_2t.1]) (by norm_num)
        constructor
        · calc
            (0.9848022703 : ℝ) <
                2 * (0.9961933222 : ℝ) ^ 2 - 1 := by norm_num
            _ < 2 * Real.cos (2 * t) ^ 2 - 1 :=
              sub_lt_sub_right
                (mul_lt_mul_of_pos_left hsquare_lower (by norm_num)) 1
            _ = Real.cos (4 * t) := hcos4.symm
        · calc
            Real.cos (4 * t) = 2 * Real.cos (2 * t) ^ 2 - 1 := hcos4
            _ < 2 * (0.9961950735 : ℝ) ^ 2 - 1 :=
              sub_lt_sub_right
                (mul_lt_mul_of_pos_left hsquare_upper (by norm_num)) 1
            _ < (0.9848092490 : ℝ) := by norm_num
  
      have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      have hsqrt_bounds : (1.7320508 : ℝ) < Real.sqrt 3 ∧
          Real.sqrt 3 < (1.7320509 : ℝ) := by
        constructor <;> nlinarith only [hsqrt, hsqrt0]
      have hsqrtcos := mul_bounds (by norm_num : (0 : ℝ) ≤ 1.7320508) (by norm_num)
        (by norm_num : (0 : ℝ) < 0.9848022703)
        hsqrt_bounds.1 hsqrt_bounds.2 hc_4t.1 hc_4t.2
      have hincidence_formula :
          Real.sin (degreesToRadians 50) =
            Real.sqrt 3 / 2 * Real.cos (4 * t) -
              (1 / 2) * Real.sin (4 * t) := by
        rw [show degreesToRadians 50 = Real.pi / 3 - 4 * t by
            dsimp [degreesToRadians, t]
            ring,
          Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
      have hsin_incidence :
          (0.766039 : ℝ) < Real.sin (degreesToRadians 50) ∧
            Real.sin (degreesToRadians 50) < (0.766049 : ℝ) := by
        constructor
        · rw [hincidence_formula]
          calc
            (0.766039 : ℝ) <
                ((1.7320508 : ℝ) * 0.9848022703) / 2 -
                  (0.1736494172 : ℝ) / 2 := by norm_num
            _ < (Real.sqrt 3 * Real.cos (4 * t)) / 2 -
                  Real.sin (4 * t) / 2 :=
              sub_lt_sub
                (div_lt_div_of_pos_right hsqrtcos.1 (by norm_num))
                (div_lt_div_of_pos_right hs_4t.2 (by norm_num))
            _ = Real.sqrt 3 / 2 * Real.cos (4 * t) -
                  (1 / 2) * Real.sin (4 * t) := by ring
        · rw [hincidence_formula]
          calc
            Real.sqrt 3 / 2 * Real.cos (4 * t) -
                (1 / 2) * Real.sin (4 * t) =
                (Real.sqrt 3 * Real.cos (4 * t)) / 2 -
                  Real.sin (4 * t) / 2 := by ring
            _ < ((1.7320509 : ℝ) * 0.9848092490) / 2 -
                  (0.1736419976 : ℝ) / 2 :=
              sub_lt_sub
                (div_lt_div_of_pos_right hsqrtcos.2 (by norm_num))
                (div_lt_div_of_pos_right hs_4t.1 (by norm_num))
            _ < (0.766049 : ℝ) := by norm_num
      have hsin_setup :
          (0.766039 : ℝ) < Real.sin setup.incidenceAngleRadians ∧
            Real.sin setup.incidenceAngleRadians < (0.766049 : ℝ) := by
        rwa [h_incidence]
  
      have ray_identity {color : VisibleColor} (ray : PrismRayAngles color) (n : ℝ)
          (hair : setup.refractiveIndex .air color = 1)
          (hglass : setup.refractiveIndex .silicaFlintGlass color = n)
          (hlaws : SatisfiesPrismRayLaws setup ray) :
          (Real.sin ray.emergenceRadians +
              Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
            (3 / 4) * (n ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2) := by
        have hapex' : setup.apexAngleRadians = Real.pi / 3 := by
          rw [h_apex]
          unfold degreesToRadians
          ring
        have hfirst : Real.sin setup.incidenceAngleRadians =
            n * Real.sin ray.firstRefractionRadians := by
          simpa [hair, hglass] using hlaws.firstFaceSnell
        have hsecond : n * Real.sin ray.secondIncidenceRadians =
            Real.sin ray.emergenceRadians := by
          simpa [hair, hglass] using hlaws.secondFaceSnell
        have hangle : ray.secondIncidenceRadians =
            Real.pi / 3 - ray.firstRefractionRadians := by
          linarith [hlaws.prismAngleGeometry]
        rw [hangle, Real.sin_sub, Real.sin_pi_div_three,
          Real.cos_pi_div_three] at hsecond
        have hlinear :
            Real.sin ray.emergenceRadians +
                Real.sin setup.incidenceAngleRadians / 2 =
              (n * Real.sqrt 3 / 2) * Real.cos ray.firstRefractionRadians := by
          nlinarith only [hfirst, hsecond]
        calc
          (Real.sin ray.emergenceRadians +
              Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
              ((n * Real.sqrt 3 / 2) *
                Real.cos ray.firstRefractionRadians) ^ 2 :=
            congrArg (fun x : ℝ => x ^ 2) hlinear
          _ = (3 / 4) *
              (n ^ 2 * Real.cos ray.firstRefractionRadians ^ 2) := by
            rw [mul_pow, div_pow, mul_pow, hsqrt]
            ring
          _ = (3 / 4) *
              (n ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2) := by
            rw [hfirst]
            have htrig := Real.sin_sq_add_cos_sq ray.firstRefractionRadians
            have hcos :
                Real.cos ray.firstRefractionRadians ^ 2 =
                  1 - Real.sin ray.firstRefractionRadians ^ 2 := by
              nlinarith only [htrig]
            rw [hcos]
            ring
  
      have red_identity :
          (Real.sin redRay.emergenceRadians +
              Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
            (3 / 4) *
              ((1.62 : ℝ) ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2) :=
        ray_identity redRay 1.62 h_air_red h_glass_red h_red_laws
      have violet_identity :
          (Real.sin violetRay.emergenceRadians +
              Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
            (3 / 4) *
              ((1.66 : ℝ) ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2) :=
        ray_identity violetRay 1.66 h_air_violet h_glass_violet h_violet_laws

      /-
      The following earlier route bounded four absolute emergence angles.  The
      shorter proof below instead bounds `sin` and `cos` of the red emergence
      once and compares the two rays directly at the two rounding endpoints.
      have angle_lt_emergence {candidate emergence n upper : ℝ}
          (hc0 : 0 ≤ candidate) (hcle : candidate ≤ Real.pi / 2)
          (he0 : 0 ≤ emergence) (hele : emergence ≤ Real.pi / 2)
          (hid : (Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
            (3 / 4) * (n ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2))
          (hsin_upper : Real.sin candidate < upper)
          (hnum : (upper + (0.766051 : ℝ) / 2) ^ 2 <
            (3 / 4) * (n ^ 2 - (0.766051 : ℝ) ^ 2)) :
          candidate < emergence := by
        have hs0 : 0 ≤ Real.sin setup.incidenceAngleRadians := by
          nlinarith only [hsin_setup.1]
        have hcpi : candidate ≤ Real.pi :=
          hcle.trans (half_le_self Real.pi_nonneg)
        have hepi : emergence ≤ Real.pi :=
          hele.trans (half_le_self Real.pi_nonneg)
        have hc_mem : candidate ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans hc0, hcle⟩
        have he_mem : emergence ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans he0, hele⟩
        have hsc0 : 0 ≤ Real.sin candidate :=
          Real.sin_nonneg_of_nonneg_of_le_pi hc0 hcpi
        have hse0 : 0 ≤ Real.sin emergence :=
          Real.sin_nonneg_of_nonneg_of_le_pi he0 hepi
        have hsum :
            Real.sin candidate + Real.sin setup.incidenceAngleRadians / 2 <
              upper + (0.766051 : ℝ) / 2 := by
          nlinarith only [hsin_upper, hsin_setup.2]
        have hsum0 :
            0 ≤ Real.sin candidate + Real.sin setup.incidenceAngleRadians / 2 := by
          positivity
        have hsquare := pow_lt_pow_left₀ hsum hsum0 (by norm_num : (2 : ℕ) ≠ 0)
        have hsincsq :
            Real.sin setup.incidenceAngleRadians ^ 2 < (0.766051 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hsin_setup.2 hs0 (by norm_num)
        have hsq :
            (Real.sin candidate + Real.sin setup.incidenceAngleRadians / 2) ^ 2 <
              (Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2) ^ 2 := by
          nlinarith only [hsquare, hsincsq, hnum, hid]
        have habs := (sq_lt_sq.mp hsq)
        rw [abs_of_nonneg hsum0,
          abs_of_nonneg (add_nonneg hse0 (div_nonneg hs0 (by norm_num)))] at habs
        have hsine : Real.sin candidate < Real.sin emergence := by
          nlinarith only [habs]
        by_contra hce
        have hec : emergence ≤ candidate := le_of_not_gt hce
        have hsinle := Real.monotoneOn_sin he_mem hc_mem hec
        linarith only [hsine, hsinle]
  
      have emergence_lt_angle {candidate emergence n lower : ℝ}
          (hc0 : 0 ≤ candidate) (hcle : candidate ≤ Real.pi / 2)
          (he0 : 0 ≤ emergence) (hele : emergence ≤ Real.pi / 2)
          (hid : (Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
            (3 / 4) * (n ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2))
          (hsin_lower : lower < Real.sin candidate)
          (hlower0 : 0 ≤ lower + (0.766037 : ℝ) / 2)
          (hnum : (3 / 4) * (n ^ 2 - (0.766037 : ℝ) ^ 2) <
            (lower + (0.766037 : ℝ) / 2) ^ 2) :
          emergence < candidate := by
        have hs0 : 0 ≤ Real.sin setup.incidenceAngleRadians := by
          nlinarith only [hsin_setup.1]
        have hcpi : candidate ≤ Real.pi :=
          hcle.trans (half_le_self Real.pi_nonneg)
        have hepi : emergence ≤ Real.pi :=
          hele.trans (half_le_self Real.pi_nonneg)
        have hc_mem : candidate ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans hc0, hcle⟩
        have he_mem : emergence ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans he0, hele⟩
        have hsc0 : 0 ≤ Real.sin candidate :=
          Real.sin_nonneg_of_nonneg_of_le_pi hc0 hcpi
        have hse0 : 0 ≤ Real.sin emergence :=
          Real.sin_nonneg_of_nonneg_of_le_pi he0 hepi
        have hsum :
            lower + (0.766037 : ℝ) / 2 <
              Real.sin candidate + Real.sin setup.incidenceAngleRadians / 2 := by
          nlinarith only [hsin_lower, hsin_setup.1]
        have hsquare := pow_lt_pow_left₀ hsum hlower0 (by norm_num : (2 : ℕ) ≠ 0)
        have hsincsq :
            (0.766037 : ℝ) ^ 2 < Real.sin setup.incidenceAngleRadians ^ 2 :=
          pow_lt_pow_left₀ hsin_setup.1 (by norm_num) (by norm_num)
        have hsq :
            (Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2) ^ 2 <
              (Real.sin candidate + Real.sin setup.incidenceAngleRadians / 2) ^ 2 := by
          nlinarith only [hsquare, hsincsq, hnum, hid]
        have habs := (sq_lt_sq.mp hsq)
        rw [abs_of_nonneg (add_nonneg hse0 (div_nonneg hs0 (by norm_num))),
          abs_of_nonneg (add_nonneg hsc0 (div_nonneg hs0 (by norm_num)))] at habs
        have hsine : Real.sin emergence < Real.sin candidate := by
          nlinarith only [habs]
        by_contra hec
        have hce : candidate ≤ emergence := le_of_not_gt hec
        have hsinle := Real.monotoneOn_sin hc_mem he_mem hce
        linarith only [hsine, hsinle]
  
      have hsmall_red_lower := small_bounds
        (x := degreesToRadians 1.4429)
        (L := (0.0251826 : ℝ))
        (U := (0.0251835 : ℝ))
        (by
          set_option maxHeartbeats 1000000 in
            norm_num1)
        (by
          unfold degreesToRadians
          nlinarith only [hpi_lower])
        (by
          unfold degreesToRadians
          nlinarith only [hpi_upper])
        (by
          set_option maxHeartbeats 1000000 in
            norm_num1)
      have hs_red_lower :
          (0.0251794 : ℝ) < Real.sin (degreesToRadians 1.4429) ∧
            Real.sin (degreesToRadians 1.4429) < (0.0251814 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_red_lower.1, hsmall_red_lower.2.1]
      have hc_red_lower :
          (0.9996823 : ℝ) < Real.cos (degreesToRadians 1.4429) ∧
            Real.cos (degreesToRadians 1.4429) < (0.9996835 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_red_lower.2.2.1, hsmall_red_lower.2.2.2]
      have hprod_red_lower := mul_bounds
        (by norm_num : (0 : ℝ) ≤ 1.7320508) (by norm_num)
        (by norm_num : (0 : ℝ) < 0.9996823)
        hsqrt_bounds.1 hsqrt_bounds.2 hc_red_lower.1 hc_red_lower.2
      have hformula_red_lower :
          Real.sin (degreesToRadians 58.5571) =
            Real.sqrt 3 / 2 * Real.cos (degreesToRadians 1.4429) -
              (1 / 2) * Real.sin (degreesToRadians 1.4429) := by
        rw [show degreesToRadians 58.5571 =
            Real.pi / 3 - degreesToRadians 1.4429 by
              unfold degreesToRadians
              ring,
          Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
      have hz_red_lower :
          Real.sin (degreesToRadians 58.5571) < (0.8531617 : ℝ) := by
        rw [hformula_red_lower]
        calc
          Real.sqrt 3 / 2 * Real.cos (degreesToRadians 1.4429) -
                1 / 2 * Real.sin (degreesToRadians 1.4429) =
              (Real.sqrt 3 * Real.cos (degreesToRadians 1.4429)) / 2 -
                Real.sin (degreesToRadians 1.4429) / 2 := by ring
          _ < ((1.7320509 : ℝ) * 0.9996835) / 2 - 0.0251794 / 2 :=
            sub_lt_sub
              (div_lt_div_of_pos_right hprod_red_lower.2 zero_lt_two)
              (div_lt_div_of_pos_right hs_red_lower.1 zero_lt_two)
          _ < 0.8531617 := by norm_num1
  
      have hsmall_red_upper := small_bounds
        (x := degreesToRadians 1.4399)
        (L := (0.0251302 : ℝ))
        (U := (0.0251311 : ℝ))
        (by
          set_option maxHeartbeats 1000000 in
            norm_num1)
        (by
          unfold degreesToRadians
          nlinarith only [hpi_lower])
        (by
          unfold degreesToRadians
          nlinarith only [hpi_upper])
        (by norm_num1)
      have hs_red_upper :
          (0.0251270 : ℝ) < Real.sin (degreesToRadians 1.4399) ∧
            Real.sin (degreesToRadians 1.4399) < (0.0251290 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_red_upper.1, hsmall_red_upper.2.1]
      have hc_red_upper :
          (0.9996837 : ℝ) < Real.cos (degreesToRadians 1.4399) ∧
            Real.cos (degreesToRadians 1.4399) < (0.9996848 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_red_upper.2.2.1, hsmall_red_upper.2.2.2]
      have hprod_red_upper := mul_bounds
        (by norm_num : (0 : ℝ) ≤ 1.7320508) (by norm_num)
        (by norm_num : (0 : ℝ) < 0.9996837)
        hsqrt_bounds.1 hsqrt_bounds.2 hc_red_upper.1 hc_red_upper.2
      have hformula_red_upper :
          Real.sin (degreesToRadians 58.5601) =
            Real.sqrt 3 / 2 * Real.cos (degreesToRadians 1.4399) -
              (1 / 2) * Real.sin (degreesToRadians 1.4399) := by
        rw [show degreesToRadians 58.5601 =
            Real.pi / 3 - degreesToRadians 1.4399 by
              unfold degreesToRadians
              ring,
          Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
      have hz_red_upper :
          (0.8531869 : ℝ) < Real.sin (degreesToRadians 58.5601) := by
        rw [hformula_red_upper]
        calc
          (0.8531869 : ℝ) <
              (1.7320508 * 0.9996837) / 2 - 0.0251290 / 2 := by norm_num1
          _ < (Real.sqrt 3 * Real.cos (degreesToRadians 1.4399)) / 2 -
                Real.sin (degreesToRadians 1.4399) / 2 :=
            sub_lt_sub
              (div_lt_div_of_pos_right hprod_red_upper.1 zero_lt_two)
              (div_lt_div_of_pos_right hs_red_upper.2 zero_lt_two)
          _ = Real.sqrt 3 / 2 * Real.cos (degreesToRadians 1.4399) -
                1 / 2 * Real.sin (degreesToRadians 1.4399) := by ring
  
      have hsmall_violet_lower := small_bounds
        (x := degreesToRadians 3.1689)
        (L := (0.0553061 : ℝ))
        (U := (0.0553079 : ℝ))
        (by norm_num1)
        (by
          unfold degreesToRadians
          nlinarith only [hpi_lower])
        (by
          unfold degreesToRadians
          nlinarith only [hpi_upper])
        (by norm_num1)
      have hs_violet_lower :
          (0.0552773 : ℝ) < Real.sin (degreesToRadians 3.1689) ∧
            Real.sin (degreesToRadians 3.1689) < (0.0552803 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_violet_lower.1, hsmall_violet_lower.2.1]
      have hc_violet_lower :
          (0.9984700 : ℝ) < Real.cos (degreesToRadians 3.1689) ∧
            Real.cos (degreesToRadians 3.1689) < (0.9984712 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_violet_lower.2.2.1, hsmall_violet_lower.2.2.2]
      have hprod_violet_lower := mul_bounds
        (by norm_num : (0 : ℝ) ≤ 1.7320508) (by norm_num)
        (by norm_num : (0 : ℝ) < 0.9984700)
        hsqrt_bounds.1 hsqrt_bounds.2 hc_violet_lower.1 hc_violet_lower.2
      have hformula_violet_lower :
          Real.sin (degreesToRadians 63.1689) =
            Real.sqrt 3 / 2 * Real.cos (degreesToRadians 3.1689) +
              (1 / 2) * Real.sin (degreesToRadians 3.1689) := by
        rw [show degreesToRadians 63.1689 =
            Real.pi / 3 + degreesToRadians 3.1689 by
              unfold degreesToRadians
              ring,
          Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three]
      have hz_violet_lower :
          Real.sin (degreesToRadians 63.1689) < (0.8923417 : ℝ) := by
        rw [hformula_violet_lower]
        calc
          Real.sqrt 3 / 2 * Real.cos (degreesToRadians 3.1689) +
                1 / 2 * Real.sin (degreesToRadians 3.1689) =
              (Real.sqrt 3 * Real.cos (degreesToRadians 3.1689)) / 2 +
                Real.sin (degreesToRadians 3.1689) / 2 := by ring
          _ < ((1.7320509 : ℝ) * 0.9984712) / 2 + 0.0552803 / 2 :=
            add_lt_add
              (div_lt_div_of_pos_right hprod_violet_lower.2 zero_lt_two)
              (div_lt_div_of_pos_right hs_violet_lower.2 zero_lt_two)
          _ < 0.8923417 := by norm_num1
  
      have hsmall_violet_upper := small_bounds
        (x := degreesToRadians 3.1719)
        (L := (0.0553584 : ℝ))
        (U := (0.0553603 : ℝ))
        (by norm_num1)
        (by
          unfold degreesToRadians
          nlinarith only [hpi_lower])
        (by
          unfold degreesToRadians
          nlinarith only [hpi_upper])
        (by norm_num1)
      have hs_violet_upper :
          (0.0553296 : ℝ) < Real.sin (degreesToRadians 3.1719) ∧
            Real.sin (degreesToRadians 3.1719) < (0.0553326 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_violet_upper.1, hsmall_violet_upper.2.1]
      have hc_violet_upper :
          (0.9984671 : ℝ) < Real.cos (degreesToRadians 3.1719) ∧
            Real.cos (degreesToRadians 3.1719) < (0.9984683 : ℝ) := by
        constructor <;>
          nlinarith only [hsmall_violet_upper.2.2.1, hsmall_violet_upper.2.2.2]
      have hprod_violet_upper := mul_bounds
        (by norm_num : (0 : ℝ) ≤ 1.7320508) (by norm_num)
        (by norm_num : (0 : ℝ) < 0.9984671)
        hsqrt_bounds.1 hsqrt_bounds.2 hc_violet_upper.1 hc_violet_upper.2
      have hformula_violet_upper :
          Real.sin (degreesToRadians 63.1719) =
            Real.sqrt 3 / 2 * Real.cos (degreesToRadians 3.1719) +
              (1 / 2) * Real.sin (degreesToRadians 3.1719) := by
        rw [show degreesToRadians 63.1719 =
            Real.pi / 3 + degreesToRadians 3.1719 by
              unfold degreesToRadians
              ring,
          Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three]
      have hz_violet_upper :
          (0.8923626 : ℝ) < Real.sin (degreesToRadians 63.1719) := by
        rw [hformula_violet_upper]
        calc
          (0.8923626 : ℝ) <
              (1.7320508 * 0.9984671) / 2 + 0.0553296 / 2 := by norm_num1
          _ < (Real.sqrt 3 * Real.cos (degreesToRadians 3.1719)) / 2 +
                Real.sin (degreesToRadians 3.1719) / 2 :=
            add_lt_add
              (div_lt_div_of_pos_right hprod_violet_upper.1 zero_lt_two)
              (div_lt_div_of_pos_right hs_violet_upper.1 zero_lt_two)
          _ = Real.sqrt 3 / 2 * Real.cos (degreesToRadians 3.1719) +
                1 / 2 * Real.sin (degreesToRadians 3.1719) := by ring
  
      have hred_lower :
          degreesToRadians 58.5571 < redRay.emergenceRadians := by
        apply angle_lt_emergence
        · unfold degreesToRadians
          positivity
        · unfold degreesToRadians
          nlinarith [Real.pi_pos]
        · exact h_red_laws.emergence_nonneg
        · exact h_red_laws.emergence_le
        · exact red_identity
        · exact hz_red_lower
        · norm_num
      have hred_upper :
          redRay.emergenceRadians < degreesToRadians 58.5601 := by
        apply emergence_lt_angle
        · unfold degreesToRadians
          positivity
        · unfold degreesToRadians
          nlinarith [Real.pi_pos]
        · exact h_red_laws.emergence_nonneg
        · exact h_red_laws.emergence_le
        · exact red_identity
        · exact hz_red_upper
        · norm_num
        · norm_num
      have hviolet_lower :
          degreesToRadians 63.1689 < violetRay.emergenceRadians := by
        apply angle_lt_emergence
        · unfold degreesToRadians
          positivity
        · unfold degreesToRadians
          nlinarith [Real.pi_pos]
        · exact h_violet_laws.emergence_nonneg
        · exact h_violet_laws.emergence_le
        · exact violet_identity
        · exact hz_violet_lower
        · norm_num
      have hviolet_upper :
          violetRay.emergenceRadians < degreesToRadians 63.1719 := by
        apply emergence_lt_angle
        · unfold degreesToRadians
          positivity
        · unfold degreesToRadians
          nlinarith [Real.pi_pos]
        · exact h_violet_laws.emergence_nonneg
        · exact h_violet_laws.emergence_le
        · exact violet_identity
        · exact hz_violet_upper
        · norm_num
        · norm_num
  
      have hspread_bounds :
          degreesToRadians 4.6088 <
              violetRay.emergenceRadians - redRay.emergenceRadians ∧
            violetRay.emergenceRadians - redRay.emergenceRadians <
              degreesToRadians 4.6148 := by
        constructor
        · have hdiff :
              degreesToRadians 4.6088 =
                degreesToRadians 63.1689 - degreesToRadians 58.5601 := by
              unfold degreesToRadians
              ring
          rw [hdiff]
          linarith
        · have hdiff :
              degreesToRadians 4.6148 =
                degreesToRadians 63.1719 - degreesToRadians 58.5571 := by
              unfold degreesToRadians
              ring
          rw [hdiff]
          linarith
      -/

      have emergence_sin_gt {emergence n lower : ℝ}
          (hlower0 : 0 ≤ lower) (he0 : 0 ≤ emergence)
          (hele : emergence ≤ Real.pi / 2)
          (hid : (Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
            (3 / 4) * (n ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2))
          (hnum : (lower + (0.766049 : ℝ) / 2) ^ 2 <
            (3 / 4) * (n ^ 2 - (0.766049 : ℝ) ^ 2)) :
          lower < Real.sin emergence := by
        have hs0 : 0 ≤ Real.sin setup.incidenceAngleRadians := by
          nlinarith only [hsin_setup.1]
        have hse0 : 0 ≤ Real.sin emergence :=
          Real.sin_nonneg_of_nonneg_of_le_pi he0
            (hele.trans (half_le_self Real.pi_nonneg))
        by_contra h
        have hsinle : Real.sin emergence ≤ lower := le_of_not_gt h
        have hsumle :
            Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2 ≤
              lower + (0.766049 : ℝ) / 2 := by
          linarith only [hsinle, hsin_setup.2]
        have hsumsq := pow_le_pow_left₀
          (add_nonneg hse0 (div_nonneg hs0 (by norm_num))) hsumle 2
        have hsincsq :
            Real.sin setup.incidenceAngleRadians ^ 2 < (0.766049 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hsin_setup.2 hs0 (by norm_num)
        nlinarith only [hid, hnum, hsumsq, hsincsq]

      have emergence_sin_lt {emergence n upper : ℝ}
          (hupper0 : 0 ≤ upper) (he0 : 0 ≤ emergence)
          (hele : emergence ≤ Real.pi / 2)
          (hid : (Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2) ^ 2 =
            (3 / 4) * (n ^ 2 - Real.sin setup.incidenceAngleRadians ^ 2))
          (hnum : (3 / 4) * (n ^ 2 - (0.766039 : ℝ) ^ 2) <
            (upper + (0.766039 : ℝ) / 2) ^ 2) :
          Real.sin emergence < upper := by
        have hs0 : 0 ≤ Real.sin setup.incidenceAngleRadians := by
          nlinarith only [hsin_setup.1]
        have hse0 : 0 ≤ Real.sin emergence :=
          Real.sin_nonneg_of_nonneg_of_le_pi he0
            (hele.trans (half_le_self Real.pi_nonneg))
        by_contra h
        have hsinle : upper ≤ Real.sin emergence := le_of_not_gt h
        have hsumle :
            upper + (0.766039 : ℝ) / 2 ≤
              Real.sin emergence + Real.sin setup.incidenceAngleRadians / 2 := by
          linarith only [hsinle, hsin_setup.1]
        have hsumsq := pow_le_pow_left₀
          (add_nonneg hupper0 (by norm_num)) hsumle 2
        have hsincsq :
            (0.766039 : ℝ) ^ 2 < Real.sin setup.incidenceAngleRadians ^ 2 :=
          pow_lt_pow_left₀ hsin_setup.1 (by norm_num) (by norm_num)
        nlinarith only [hid, hnum, hsumsq, hsincsq]

      have hsin_red :
          (0.8531699 : ℝ) < Real.sin redRay.emergenceRadians ∧
            Real.sin redRay.emergenceRadians < (0.8531797 : ℝ) := by
        constructor
        · exact emergence_sin_gt
            (emergence := redRay.emergenceRadians) (n := 1.62)
            (lower := 0.8531699) (by norm_num)
            h_red_laws.emergence_nonneg h_red_laws.emergence_le
            red_identity (by norm_num)
        · exact emergence_sin_lt
            (emergence := redRay.emergenceRadians) (n := 1.62)
            (upper := 0.8531797) (by norm_num)
            h_red_laws.emergence_nonneg h_red_laws.emergence_le
            red_identity (by norm_num)

      have hsin_violet :
          (0.8923486 : ℝ) < Real.sin violetRay.emergenceRadians ∧
            Real.sin violetRay.emergenceRadians < (0.8923582 : ℝ) := by
        constructor
        · exact emergence_sin_gt
            (emergence := violetRay.emergenceRadians) (n := 1.66)
            (lower := 0.8923486) (by norm_num)
            h_violet_laws.emergence_nonneg h_violet_laws.emergence_le
            violet_identity (by norm_num)
        · exact emergence_sin_lt
            (emergence := violetRay.emergenceRadians) (n := 1.66)
            (upper := 0.8923582) (by norm_num)
            h_violet_laws.emergence_nonneg h_violet_laws.emergence_le
            violet_identity (by norm_num)

      have hcos_red_nonneg : 0 ≤ Real.cos redRay.emergenceRadians :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          ((neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans
            h_red_laws.emergence_nonneg)
          h_red_laws.emergence_le
      have htrig_red := Real.sin_sq_add_cos_sq redRay.emergenceRadians
      have hcos_red :
          (0.5216170 : ℝ) < Real.cos redRay.emergenceRadians ∧
            Real.cos redRay.emergenceRadians < (0.5216332 : ℝ) := by
        constructor
        · by_contra h
          have hcosle : Real.cos redRay.emergenceRadians ≤ (0.5216170 : ℝ) :=
            le_of_not_gt h
          have hcossq := pow_le_pow_left₀ hcos_red_nonneg hcosle 2
          have hsinsq := pow_lt_pow_left₀ hsin_red.2
            (by nlinarith only [hsin_red.1]) (by norm_num : (2 : ℕ) ≠ 0)
          nlinarith only [htrig_red, hcossq, hsinsq]
        · by_contra h
          have hcosle : (0.5216332 : ℝ) ≤ Real.cos redRay.emergenceRadians :=
            le_of_not_gt h
          have hcossq := pow_le_pow_left₀ (by norm_num) hcosle 2
          have hsinsq := pow_lt_pow_left₀ hsin_red.1 (by norm_num)
            (by norm_num : (2 : ℕ) ≠ 0)
          nlinarith only [htrig_red, hcossq, hsinsq]

      have hred_lt_pi_div_three :
          redRay.emergenceRadians < Real.pi / 3 := by
        have hsin_lt :
            Real.sin redRay.emergenceRadians < Real.sin (Real.pi / 3) := by
          rw [Real.sin_pi_div_three]
          nlinarith only [hsin_red.2, hsqrt_bounds.1]
        by_contra h
        have hle : Real.pi / 3 ≤ redRay.emergenceRadians := le_of_not_gt h
        have hmono := Real.monotoneOn_sin
          ⟨by nlinarith only [Real.pi_pos],
            by nlinarith only [Real.pi_pos]⟩
          ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans
              h_red_laws.emergence_nonneg,
            h_red_laws.emergence_le⟩ hle
        linarith only [hsin_lt, hmono]

      have hsmall_diff_lower := small_bounds
        (x := degreesToRadians 4.605)
        (L := (0.0803700 : ℝ))
        (U := (0.0803727 : ℝ))
        (by norm_num)
        (by
          unfold degreesToRadians
          nlinarith only [hpi_lower])
        (by
          unfold degreesToRadians
          nlinarith only [hpi_upper])
        (by norm_num)
      have hsin_diff_lower :
          Real.sin (degreesToRadians 4.605) < (0.0802884 : ℝ) := by
        nlinarith only [hsmall_diff_lower.2.1]
      have hcos_diff_lower :
          Real.cos (degreesToRadians 4.605) < (0.9967727 : ℝ) := by
        nlinarith only [hsmall_diff_lower.2.2.2]

      have hsmall_diff_upper := small_bounds
        (x := degreesToRadians 4.615)
        (L := (0.0805445 : ℝ))
        (U := (0.0805472 : ℝ))
        (by norm_num)
        (by
          unfold degreesToRadians
          nlinarith only [hpi_lower])
        (by
          unfold degreesToRadians
          nlinarith only [hpi_upper])
        (by norm_num)
      have hsin_diff_upper :
          (0.0804552 : ℝ) < Real.sin (degreesToRadians 4.615) := by
        nlinarith only [hsmall_diff_upper.1]
      have hcos_diff_upper :
          (0.9967538 : ℝ) < Real.cos (degreesToRadians 4.615) := by
        nlinarith only [hsmall_diff_upper.2.2.1]

      have hdiff_lower_pos : 0 < degreesToRadians 4.605 := by
        unfold degreesToRadians
        positivity
      have hdiff_lower_lt_pi_div_two :
          degreesToRadians 4.605 < Real.pi / 2 := by
        unfold degreesToRadians
        nlinarith only [Real.pi_pos]
      have hsin_diff_lower_pos : 0 < Real.sin (degreesToRadians 4.605) :=
        Real.sin_pos_of_pos_of_lt_pi hdiff_lower_pos
          (hdiff_lower_lt_pi_div_two.trans (half_lt_self Real.pi_pos))
      have hcos_diff_lower_pos : 0 < Real.cos (degreesToRadians 4.605) :=
        Real.cos_pos_of_mem_Ioo
          ⟨by nlinarith only [hdiff_lower_pos, Real.pi_pos],
            hdiff_lower_lt_pi_div_two⟩
      have hprod_red_cos_lower :
          Real.sin redRay.emergenceRadians * Real.cos (degreesToRadians 4.605) <
            (0.8531797 : ℝ) * 0.9967727 :=
        mul_lt_mul hsin_red.2 hcos_diff_lower.le hcos_diff_lower_pos (by norm_num)
      have hprod_cosred_sin_lower :
          Real.cos redRay.emergenceRadians * Real.sin (degreesToRadians 4.605) <
            (0.5216332 : ℝ) * 0.0802884 :=
        mul_lt_mul hcos_red.2 hsin_diff_lower.le hsin_diff_lower_pos (by norm_num)
      have hsin_at_lower :
          Real.sin (redRay.emergenceRadians + degreesToRadians 4.605) <
            Real.sin violetRay.emergenceRadians := by
        rw [Real.sin_add]
        nlinarith only
          [hprod_red_cos_lower, hprod_cosred_sin_lower, hsin_violet.1]

      have hprod_red_cos_upper :
          (0.8531699 : ℝ) * 0.9967538 <
            Real.sin redRay.emergenceRadians * Real.cos (degreesToRadians 4.615) :=
        mul_lt_mul hsin_red.1 hcos_diff_upper.le (by norm_num)
          (by nlinarith only [hsin_red.1])
      have hprod_cosred_sin_upper :
          (0.5216170 : ℝ) * 0.0804552 <
            Real.cos redRay.emergenceRadians * Real.sin (degreesToRadians 4.615) :=
        mul_lt_mul hcos_red.1 hsin_diff_upper.le (by norm_num) hcos_red_nonneg
      have hsin_at_upper :
          Real.sin violetRay.emergenceRadians <
            Real.sin (redRay.emergenceRadians + degreesToRadians 4.615) := by
        rw [Real.sin_add]
        nlinarith only
          [hprod_red_cos_upper, hprod_cosred_sin_upper, hsin_violet.2]

      have hred_add_lower_le :
          redRay.emergenceRadians + degreesToRadians 4.605 ≤ Real.pi / 2 := by
        unfold degreesToRadians
        nlinarith only [hred_lt_pi_div_three, Real.pi_pos]
      have hred_add_upper_le :
          redRay.emergenceRadians + degreesToRadians 4.615 ≤ Real.pi / 2 := by
        unfold degreesToRadians
        nlinarith only [hred_lt_pi_div_three, Real.pi_pos]
      have hred_add_lower_nonneg :
          0 ≤ redRay.emergenceRadians + degreesToRadians 4.605 := by
        exact add_nonneg h_red_laws.emergence_nonneg
          (by unfold degreesToRadians; positivity)
      have hred_add_upper_nonneg :
          0 ≤ redRay.emergenceRadians + degreesToRadians 4.615 := by
        exact add_nonneg h_red_laws.emergence_nonneg
          (by unfold degreesToRadians; positivity)

      have hspread_lower :
          degreesToRadians 4.605 <
            violetRay.emergenceRadians - redRay.emergenceRadians := by
        have hangle :
            redRay.emergenceRadians + degreesToRadians 4.605 <
              violetRay.emergenceRadians := by
          by_contra h
          have hle : violetRay.emergenceRadians ≤
              redRay.emergenceRadians + degreesToRadians 4.605 := le_of_not_gt h
          have hmono := Real.monotoneOn_sin
            ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans
                h_violet_laws.emergence_nonneg,
              h_violet_laws.emergence_le⟩
            ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans
                hred_add_lower_nonneg,
              hred_add_lower_le⟩ hle
          linarith only [hsin_at_lower, hmono]
        linarith
      have hspread_upper :
          violetRay.emergenceRadians - redRay.emergenceRadians <
            degreesToRadians 4.615 := by
        have hangle :
            violetRay.emergenceRadians <
              redRay.emergenceRadians + degreesToRadians 4.615 := by
          by_contra h
          have hle : redRay.emergenceRadians + degreesToRadians 4.615 ≤
              violetRay.emergenceRadians := le_of_not_gt h
          have hmono := Real.monotoneOn_sin
            ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans
                hred_add_upper_nonneg,
              hred_add_upper_le⟩
            ⟨(neg_nonpos.mpr (div_nonneg Real.pi_nonneg (by norm_num))).trans
                h_violet_laws.emergence_nonneg,
              h_violet_laws.emergence_le⟩ hle
          linarith only [hsin_at_upper, hmono]
        linarith

      have hspread_bounds :
          degreesToRadians 4.605 <
              violetRay.emergenceRadians - redRay.emergenceRadians ∧
            violetRay.emergenceRadians - redRay.emergenceRadians <
              degreesToRadians 4.615 :=
        ⟨hspread_lower, hspread_upper⟩

      rw [h_spread_figure]
      unfold angularSpreadRadians
      rw [h_violet_laws.deviationGeometry, h_red_laws.deviationGeometry]
      have hcancel :
          (setup.incidenceAngleRadians + violetRay.emergenceRadians -
                setup.apexAngleRadians) -
              (setup.incidenceAngleRadians + redRay.emergenceRadians -
                setup.apexAngleRadians) =
            violetRay.emergenceRadians - redRay.emergenceRadians := by
        ring
      rw [hcancel]
      change
        abs ((violetRay.emergenceRadians - redRay.emergenceRadians) -
            degreesToRadians 4.61) ≤ degreesToRadians 0.005
      rw [abs_le]
      constructor
      · calc
          -degreesToRadians 0.005 =
              degreesToRadians 4.605 - degreesToRadians 4.61 := by
                unfold degreesToRadians
                ring
          _ ≤ (violetRay.emergenceRadians - redRay.emergenceRadians) -
                degreesToRadians 4.61 :=
            sub_le_sub_right (le_of_lt hspread_bounds.1) _
      · calc
          (violetRay.emergenceRadians - redRay.emergenceRadians) -
                degreesToRadians 4.61 ≤
              degreesToRadians 4.615 - degreesToRadians 4.61 :=
            sub_le_sub_right (le_of_lt hspread_bounds.2) _
          _ = degreesToRadians 0.005 := by
            unfold degreesToRadians
            ring
  
end PhyXMiniProblems.Problem0008
