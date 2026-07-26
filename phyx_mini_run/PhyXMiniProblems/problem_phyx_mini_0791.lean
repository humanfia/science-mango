import Physlib.SpaceAndTime.Space.Module
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0791

/-!
# Scalar product of two vectors read from a polar diagram

The two arrows are modeled in Physlib's two-dimensional flat physical space.
`Space 2` comes with an arbitrary choice of origin and common length unit, as
well as a real inner product.  Thus the stated magnitudes are coordinate
readouts in that common unit and their inner product has the corresponding
squared unit.

The primary image places `A` at `53°` and `B` at `130°`, counterclockwise from
the positive x-axis.  It labels the angle between them by `phi`.  The recorded
multiple-choice answer `4.50` is a rounded decimal: the exact idealized value
is `20 * cos (77°)`, which is close to, but not definitionally equal to, `4.50`.
-/

/-- Physlib's flat two-dimensional space, with the figure's origin and common
unit chosen. -/
abbrev Plane : Type := Space 2

/-- The figure's positive x-axis unit vector, labelled `i-hat`. -/
def iHat : Plane := Space.basis (0 : Fin 2)

/-- The figure's positive y-axis unit vector, labelled `j-hat`. -/
def jHat : Plane := Space.basis (1 : Fin 2)

/-- Convert the degree readouts printed in the figure to radians. -/
def degrees (value : ℝ) : ℝ := value * Real.pi / 180

/-- A unit-direction expression at a counterclockwise bearing from `iHat`. -/
def directionAt (bearing : ℝ) : Plane :=
  Real.cos bearing • iHat + Real.sin bearing • jHat

/-- The named vector and angle quantities occurring in the diagram. -/
structure VectorDiagram where
  /-- Vector `A`, drawn with its tail at the coordinate origin. -/
  A : Plane
  /-- Vector `B`, drawn with its tail at the coordinate origin. -/
  B : Plane
  /-- The included angle labelled `phi` in the image, measured in radians. -/
  phi : ℝ

/-!
The fields below contain only stated magnitudes and primary-image readouts.
The polar-form fields retain which side of the x-axis each arrow occupies;
undirected angle equalities alone would lose that orientation information.
No scalar-product value or answer choice is included in this predicate.
-/
/-- The physical quantities and geometric readouts supplied by the problem. -/
structure MatchesProblemAndFigure (diagram : VectorDiagram) : Prop where
  /-- The stated magnitude `A = 4.00`. -/
  a_magnitude : ‖diagram.A‖ = 4
  /-- The stated magnitude `B = 5.00`. -/
  b_magnitude : ‖diagram.B‖ = 5
  /-- Image readout: `A` has magnitude 4 and counterclockwise bearing 53°. -/
  a_polar_form : diagram.A = (4 : ℝ) • directionAt (degrees 53)
  /-- Image readout: `B` has magnitude 5 and counterclockwise bearing 130°. -/
  b_polar_form : diagram.B = (5 : ℝ) • directionAt (degrees 130)
  /-- The 53° arc is the undirected angle from the positive x-axis to `A`. -/
  a_bearing :
    InnerProductGeometry.angle iHat diagram.A = degrees 53
  /-- The 130° arc is the undirected angle from the positive x-axis to `B`. -/
  b_bearing :
    InnerProductGeometry.angle iHat diagram.B = degrees 130
  /-- The symbol `phi` labels the included angle between `A` and `B`. -/
  phi_labels_included_angle :
    InnerProductGeometry.angle diagram.A diagram.B = diagram.phi

/-- The included angle obtained from the two image bearings is `130° - 53°`. -/
lemma includedAngle_isSeventySevenDegrees
    (diagram : VectorDiagram) (h : MatchesProblemAndFigure diagram) :
    diagram.phi = degrees 77 := by
  rw [← h.phi_labels_included_angle, h.a_polar_form, h.b_polar_form,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (by norm_num : (0 : ℝ) < 4),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (by norm_num : (0 : ℝ) < 5)]
  have norm_directionAt (t : ℝ) : ‖directionAt t‖ = 1 := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_two, directionAt, iHat, jHat, Space.basis_apply]
  have inner_directionAt (s t : ℝ) :
      inner ℝ (directionAt s) (directionAt t) = Real.cos (t - s) := by
    rw [Space.inner_apply]
    simp [Fin.sum_univ_two, directionAt, iHat, jHat, Space.basis_apply,
      Real.cos_sub]
    ring
  apply Real.strictAntiOn_cos.injOn
  · exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  · constructor
    · unfold degrees
      positivity
    · unfold degrees
      nlinarith [Real.pi_pos]
  rw [InnerProductGeometry.cos_angle, norm_directionAt, norm_directionAt,
    inner_directionAt]
  simp only [mul_one, div_one]
  congr 1
  unfold degrees
  ring

/-!
This is the exact scalar-product relation before decimal rounding.  Its
governing law is Mathlib's
`InnerProductGeometry.cos_angle_mul_norm_mul_norm`.
-/
/-- The exact idealized scalar product is `|A| |B| cos(phi)`. -/
lemma scalarProduct_exact
    (diagram : VectorDiagram) (h : MatchesProblemAndFigure diagram) :
    inner ℝ diagram.A diagram.B = 20 * Real.cos (degrees 77) := by
  calc
    inner ℝ diagram.A diagram.B =
        Real.cos (InnerProductGeometry.angle diagram.A diagram.B) *
          (‖diagram.A‖ * ‖diagram.B‖) :=
      (InnerProductGeometry.cos_angle_mul_norm_mul_norm diagram.A diagram.B).symm
    _ = 20 * Real.cos (degrees 77) := by
      rw [h.phi_labels_included_angle,
        includedAngle_isSeventySevenDegrees diagram h,
        h.a_magnitude, h.b_magnitude]
      ring

/-!
`4.50 = 9/2` is the displayed answer to two decimal places.  Being within
`1/200 = 0.005` is the strict error bound for unambiguous rounding to the
nearest hundredth.
-/
/-- The scalar product rounds to `4.50`, so the recorded answer is choice B. -/
theorem scalarProduct_roundsToFourPointFive
    (diagram : VectorDiagram) (h : MatchesProblemAndFigure diagram) :
    abs (inner ℝ diagram.A diagram.B - (9 / 2 : ℝ)) < (1 / 200 : ℝ) := by
  rw [scalarProduct_exact diagram h]
  -- The exact value of `sin (π / 16)`, together with Mathlib's certified
  -- fourth-order sine remainder, gives the modest bounds on `π` needed below.
  have ha_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have ha_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha_lower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith only [ha_nonneg, ha_sq]
  have ha_upper : Real.sqrt 2 < (1.41422 : ℝ) := by
    nlinarith only [ha_nonneg, ha_sq]
  have hb_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hb_sq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hb_lower : (1.8471 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hb_nonneg, hb_sq, ha_lower]
  have hb_upper : Real.sqrt (2 + Real.sqrt 2) < (1.84777 : ℝ) := by
    nlinarith only [hb_nonneg, hb_sq, ha_upper]
  have hs_pos : 0 < Real.sin (Real.pi / 16) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith only [Real.pi_pos]
  have hs_sq : Real.sin (Real.pi / 16) ^ 2 =
      (2 - Real.sqrt (2 + Real.sqrt 2)) / 4 := by
    have hsq := Real.sin_sq_pi_over_two_pow_succ 2
    norm_num [Real.sqrtTwoAddSeries] at hsq ⊢
    nlinarith only [hsq]
  have hs_lower : (0.19508 : ℝ) < Real.sin (Real.pi / 16) := by
    nlinarith only [hs_pos, hs_sq, hb_upper,
      sq_nonneg (Real.sin (Real.pi / 16) - 0.19508)]
  have hs_upper : Real.sin (Real.pi / 16) < (0.19552 : ℝ) := by
    nlinarith only [hs_pos, hs_sq, hb_lower,
      sq_nonneg (Real.sin (Real.pi / 16) - 0.19552)]
  have hsin_314_upper : Real.sin (3.14 / 16) < (0.19508 : ℝ) := by
    have hbound := Real.sin_bound (x := (3.14 : ℝ) / 16) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.14 / 16)] at hbound
    rcases abs_le.mp hbound with ⟨_, hupper⟩
    norm_num at hupper ⊢
    linarith only [hupper]
  have hsin_315_lower : (0.19552 : ℝ) < Real.sin (3.15 / 16) := by
    have hbound := Real.sin_bound (x := (3.15 : ℝ) / 16) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.15 / 16)] at hbound
    rcases abs_le.mp hbound with ⟨hlower, _⟩
    norm_num at hlower ⊢
    linarith only [hlower]
  have hpi_lower : (3.14 : ℝ) < Real.pi := by
    by_contra hpi
    have hpi_le : Real.pi ≤ (3.14 : ℝ) := le_of_not_gt hpi
    have hsin_mono :
        Real.sin (Real.pi / 16) ≤ Real.sin (3.14 / 16) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.one_le_pi_div_two]
      · nlinarith only [hpi_le]
    linarith only [hs_lower, hsin_mono, hsin_314_upper]
  have hpi_upper : Real.pi < (3.15 : ℝ) := by
    by_contra hpi
    have hpi_ge : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt hpi
    have hsin_mono :
        Real.sin (3.15 / 16) ≤ Real.sin (Real.pi / 16) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
      · nlinarith only [hpi_ge]
    linarith only [hsin_315_lower, hsin_mono, hs_upper]
  -- Use `13° = 15° - 2°`: the 15° values are exact radicals, and only
  -- the small 2° correction needs a Taylor estimate.
  have hsqrt_mul : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsin_fifteen :
      Real.sin (Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring,
      Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_six,
      Real.cos_pi_div_four, Real.sin_pi_div_six]
    nlinarith only [hsqrt_mul]
  have hcos_fifteen :
      Real.cos (Real.pi / 12) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
    rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring,
      Real.cos_sub, Real.cos_pi_div_four, Real.cos_pi_div_six,
      Real.sin_pi_div_four, Real.sin_pi_div_six]
    nlinarith only [hsqrt_mul]
  have hsix_nonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hsix_sq : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsix_lower : (2.44948 : ℝ) < Real.sqrt 6 := by
    nlinarith only [hsix_nonneg, hsix_sq]
  have hsix_upper : Real.sqrt 6 < (2.4495 : ℝ) := by
    nlinarith only [hsix_nonneg, hsix_sq]
  have hsin_fifteen_lower :
      (0.2588 : ℝ) < Real.sin (Real.pi / 12) := by
    rw [hsin_fifteen]
    nlinarith only [hsix_lower, ha_upper]
  have hsin_fifteen_upper :
      Real.sin (Real.pi / 12) < (0.25884 : ℝ) := by
    rw [hsin_fifteen]
    nlinarith only [hsix_upper, ha_lower]
  have hcos_fifteen_lower :
      (0.9659 : ℝ) < Real.cos (Real.pi / 12) := by
    rw [hcos_fifteen]
    nlinarith only [hsix_lower, ha_lower]
  have hcos_fifteen_upper :
      Real.cos (Real.pi / 12) < (0.96595 : ℝ) := by
    rw [hcos_fifteen]
    nlinarith only [hsix_upper, ha_upper]
  have hsin_fifteen_nonneg : 0 ≤ Real.sin (Real.pi / 12) :=
    (by norm_num : (0 : ℝ) ≤ 0.2588).trans hsin_fifteen_lower.le
  have hcos_fifteen_nonneg : 0 ≤ Real.cos (Real.pi / 12) :=
    (by norm_num : (0 : ℝ) ≤ 0.9659).trans hcos_fifteen_lower.le
  let delta : ℝ := Real.pi / 90
  let deltaLower : ℝ := (3.14 : ℝ) / 90
  let deltaUpper : ℝ := (3.15 : ℝ) / 90
  have hdelta_nonneg : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hdelta_lower : deltaLower < delta := by
    dsimp [deltaLower, delta]
    nlinarith only [hpi_lower]
  have hdelta_upper : delta < deltaUpper := by
    dsimp [delta, deltaUpper]
    nlinarith only [hpi_upper]
  have hdeltaUpper_one : deltaUpper ≤ 1 := by norm_num [deltaUpper]
  have hdelta_abs : |delta| ≤ 1 := by
    rw [abs_of_nonneg hdelta_nonneg]
    exact hdelta_upper.le.trans hdeltaUpper_one
  have hdelta_sq_upper : delta ^ 2 ≤ deltaUpper ^ 2 :=
    pow_le_pow_left₀ hdelta_nonneg hdelta_upper.le 2
  have hdelta_cube_upper : delta ^ 3 ≤ deltaUpper ^ 3 :=
    pow_le_pow_left₀ hdelta_nonneg hdelta_upper.le 3
  have hdelta_fourth_upper : delta ^ 4 ≤ deltaUpper ^ 4 :=
    pow_le_pow_left₀ hdelta_nonneg hdelta_upper.le 4
  have hsin_delta_bound := Real.sin_bound hdelta_abs
  have hcos_delta_bound := Real.cos_bound hdelta_abs
  rw [abs_of_nonneg hdelta_nonneg] at hsin_delta_bound hcos_delta_bound
  rcases abs_le.mp hsin_delta_bound with
    ⟨hsin_delta_error_lower, hsin_delta_error_upper⟩
  rcases abs_le.mp hcos_delta_bound with
    ⟨hcos_delta_error_lower, _hcos_delta_error_upper⟩
  have hsin_delta_lower : (0.03488 : ℝ) < Real.sin delta := by
    dsimp [deltaLower, deltaUpper] at hdelta_lower hdelta_cube_upper hdelta_fourth_upper
    nlinarith only [hdelta_lower, hdelta_cube_upper, hdelta_fourth_upper,
      hsin_delta_error_lower]
  have hsin_delta_upper : Real.sin delta < (0.035 : ℝ) := by
    have hdelta_cube_nonneg : 0 ≤ delta ^ 3 := by positivity
    dsimp [deltaUpper] at hdelta_upper hdelta_fourth_upper
    nlinarith only [hdelta_upper, hdelta_cube_nonneg, hdelta_fourth_upper,
      hsin_delta_error_upper]
  have hcos_delta_lower : (0.99938 : ℝ) < Real.cos delta := by
    dsimp [deltaUpper] at hdelta_sq_upper hdelta_fourth_upper
    nlinarith only [hdelta_sq_upper, hdelta_fourth_upper,
      hcos_delta_error_lower]
  have hsin_delta_nonneg : 0 ≤ Real.sin delta := by
    linarith only [hsin_delta_lower]
  have hsin_delta_pos : 0 < Real.sin delta := by
    linarith only [hsin_delta_lower]
  have hfirst_lower :
      (0.2588 : ℝ) * 0.99938 <
        Real.sin (Real.pi / 12) * Real.cos delta :=
    mul_lt_mul hsin_fifteen_lower hcos_delta_lower.le (by norm_num)
      hsin_fifteen_nonneg
  have hsecond_upper :
      Real.cos (Real.pi / 12) * Real.sin delta <
        (0.96595 : ℝ) * 0.035 :=
    mul_lt_mul hcos_fifteen_upper hsin_delta_upper.le hsin_delta_pos
      (by norm_num)
  have hfirst_upper :
      Real.sin (Real.pi / 12) * Real.cos delta < (0.25884 : ℝ) := by
    calc
      Real.sin (Real.pi / 12) * Real.cos delta ≤
          Real.sin (Real.pi / 12) * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one delta) hsin_fifteen_nonneg
      _ < (0.25884 : ℝ) := by simpa using hsin_fifteen_upper
  have hsecond_lower :
      (0.9659 : ℝ) * 0.03488 <
        Real.cos (Real.pi / 12) * Real.sin delta :=
    mul_lt_mul hcos_fifteen_lower hsin_delta_lower.le (by norm_num)
      hcos_fifteen_nonneg
  have hsin_thirteen_lower :
      (0.22475 : ℝ) < Real.sin (Real.pi / 12 - Real.pi / 90) := by
    rw [Real.sin_sub]
    change (0.22475 : ℝ) <
      Real.sin (Real.pi / 12) * Real.cos delta -
        Real.cos (Real.pi / 12) * Real.sin delta
    nlinarith only [hfirst_lower, hsecond_upper]
  have hsin_thirteen_upper :
      Real.sin (Real.pi / 12 - Real.pi / 90) < (0.22525 : ℝ) := by
    rw [Real.sin_sub]
    change
      Real.sin (Real.pi / 12) * Real.cos delta -
          Real.cos (Real.pi / 12) * Real.sin delta < (0.22525 : ℝ)
    nlinarith only [hfirst_upper, hsecond_lower]
  have hcos_seventy_seven :
      Real.cos (degrees 77) =
        Real.sin (Real.pi / 12 - Real.pi / 90) := by
    rw [show degrees 77 =
        Real.pi / 2 - (Real.pi / 12 - Real.pi / 90) by
      unfold degrees
      ring, Real.cos_pi_div_two_sub]
  rw [hcos_seventy_seven, abs_lt]
  constructor <;> nlinarith only [hsin_thirteen_lower, hsin_thirteen_upper]

end PhyXMiniProblems.ProblemPhyXMini0791
