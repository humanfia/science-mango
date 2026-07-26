import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0013

/-- A physical length, represented independently of the unit system used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The scalar value of a physical length when the chosen unit system is SI meters. -/
def valueInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The two optical media separated by the lower face of the DVD. -/
inductive OpticalMedium where
  | air
  | plastic
  deriving DecidableEq, Repr

/--
The physical quantities and figure labels in the symmetric DVD laser-beam cross-section.
The angles are real-valued radian readouts measured from the interface normal. The two
in-plastic angles retain the figure's left and right labels `theta_2` and `theta'_2`.
-/
structure DVDLaserSetup where
  /-- Approximate width of one spiral information track. -/
  trackWidth : LengthQuantity
  /-- Figure label `t`, the normal thickness of the transparent plastic. -/
  plasticThickness : LengthQuantity
  /-- Figure label `a`, the beam width at the information layer. -/
  focusedBeamWidth : LengthQuantity
  /-- Figure label `w`, the beam width where it enters the plastic. -/
  entranceBeamWidth : LengthQuantity
  /-- Figure label `b`, the lateral narrowing on either side of `a`. -/
  halfExcessWidth : LengthQuantity
  /-- Dimensionless refractive index of each optical medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Figure label `theta_1`, the edge-ray incidence angle in air. -/
  incidenceAngleRadians : ℝ
  /-- Figure label `theta_2`, the left edge-ray angle inside the plastic. -/
  leftPlasticAngleRadians : ℝ
  /-- Figure label `theta'_2`, the right edge-ray angle inside the plastic. -/
  rightPlasticAngleRadians : ℝ
  /-- Full apex angle of the converging cone before it enters the DVD. -/
  coneApexAngleRadians : ℝ
  /-- The plastic transmits the incident laser beam. -/
  plasticIsTransparent : Prop
  /-- The information layer is planar in the displayed cross-section. -/
  informationLayerIsPlanar : Prop
  /-- The cone axis is normal to the parallel plastic and information-layer faces. -/
  beamAxisIsNormalToLayers : Prop

/--
Snell's law at a planar interface. Refractive indices are dimensionless and angles are
radian magnitudes from the local normal.
-/
def SnellLawAtInterface
    (incidentIndex transmittedIndex incidentAngle transmittedAngle : ℝ) : Prop :=
  incidentIndex * Real.sin incidentAngle =
    transmittedIndex * Real.sin transmittedAngle

/--
Problem-statement and figure readouts. Lengths are read in SI meters, so the displayed
micrometer and millimeter values are converted exactly to powers of ten. The width
partition and cone-angle relations are geometric annotations from the symmetric figure;
neither states the requested numerical incidence angle.
-/
structure DVDLaserFigureReadouts (setup : DVDLaserSetup) : Prop where
  plastic_is_transparent : setup.plasticIsTransparent
  information_layer_is_planar : setup.informationLayerIsPlanar
  beam_axis_is_normal : setup.beamAxisIsNormalToLayers
  track_width_readout : valueInMeters setup.trackWidth = (1 : ℝ) / 10 ^ 6
  plastic_thickness_readout :
    valueInMeters setup.plasticThickness = (12 : ℝ) / 10 ^ 4
  focused_width_readout :
    valueInMeters setup.focusedBeamWidth = (1 : ℝ) / 10 ^ 6
  entrance_width_readout :
    valueInMeters setup.entranceBeamWidth = (7 : ℝ) / 10 ^ 4
  air_index_readout : setup.refractiveIndex .air = 1
  plastic_index_readout : setup.refractiveIndex .plastic = (31 : ℝ) / 20
  width_partition : ∀ units : UnitChoices,
    (setup.entranceBeamWidth units).val =
      (setup.focusedBeamWidth units).val +
        2 * (setup.halfExcessWidth units).val
  left_right_symmetry :
    setup.leftPlasticAngleRadians = setup.rightPlasticAngleRadians
  cone_apex_relation :
    setup.coneApexAngleRadians = 2 * setup.incidenceAngleRadians

/--
The governing geometrical-optics relations for the two edge rays. The right-triangle
equations express `b = t tan(theta_2)` in any chosen unit system, and the two Snell-law
fields describe refraction from air into the plastic. Acute-angle hypotheses select the
physical branches of the trigonometric equations.
-/
structure DVDLaserGoverningLaws (setup : DVDLaserSetup) : Prop where
  refractive_indices_positive :
    ∀ medium : OpticalMedium, 0 < setup.refractiveIndex medium
  incidence_angle_acute :
    setup.incidenceAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  left_plastic_angle_acute :
    setup.leftPlasticAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  right_plastic_angle_acute :
    setup.rightPlasticAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  left_edge_ray_geometry : ∀ units : UnitChoices,
    (setup.halfExcessWidth units).val =
      (setup.plasticThickness units).val *
        Real.tan setup.leftPlasticAngleRadians
  right_edge_ray_geometry : ∀ units : UnitChoices,
    (setup.halfExcessWidth units).val =
      (setup.plasticThickness units).val *
        Real.tan setup.rightPlasticAngleRadians
  left_edge_snell_law :
    SnellLawAtInterface
      (setup.refractiveIndex .air)
      (setup.refractiveIndex .plastic)
      setup.incidenceAngleRadians
      setup.leftPlasticAngleRadians
  right_edge_snell_law :
    SnellLawAtInterface
      (setup.refractiveIndex .air)
      (setup.refractiveIndex .plastic)
      setup.incidenceAngleRadians
      setup.rightPlasticAngleRadians

/-- The four incidence-angle choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The degree readout printed beside each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => (103 : ℝ) / 5
  | .B => (183 : ℝ) / 10
  | .C => (257 : ℝ) / 10
  | .D => (213 : ℝ) / 10

/-- Convert a real-valued degree readout to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/--
A radian angle rounds to a displayed one-decimal-place answer when it lies within
half of `0.1 degrees` of that choice's degree readout.
-/
def MatchesAnswerToNearestTenthDegree
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |angleRadians - degreesToRadians (answerAngleDegrees choice)| ≤
    degreesToRadians ((1 : ℝ) / 20)

/--
The incidence angle determined by the DVD dimensions, symmetric cone geometry, and
Snell's law rounds to answer choice C, `25.7 degrees`.

Blueprint label: `thm:physics:phyx_mini_0013:target`.
-/
theorem incidenceAngle_is_answer_C
    (setup : DVDLaserSetup)
    (_laws : DVDLaserGoverningLaws setup)
    (_figure : DVDLaserFigureReadouts setup) :
    MatchesAnswerToNearestTenthDegree setup.incidenceAngleRadians .C := by
  have hthickness := _figure.plastic_thickness_readout
  have hfocused := _figure.focused_width_readout
  have hentrance := _figure.entrance_width_readout
  simp only [valueInMeters] at hthickness hfocused hentrance
  have hpartition := _figure.width_partition UnitChoices.SI
  have hhalf :
      (setup.halfExcessWidth UnitChoices.SI).val =
        (699 : ℝ) / 2000000 := by
    norm_num at hfocused hentrance
    nlinarith
  have hgeometry := _laws.left_edge_ray_geometry UnitChoices.SI
  have htan :
      Real.tan setup.leftPlasticAngleRadians = (233 : ℝ) / 800 := by
    rw [hhalf, hthickness] at hgeometry
    norm_num at hgeometry ⊢
    linarith
  have hcospos :
      0 < Real.cos setup.leftPlasticAngleRadians := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [_laws.left_plastic_angle_acute.1, Real.pi_pos]
    · exact _laws.left_plastic_angle_acute.2
  have hsincos :
      Real.sin setup.leftPlasticAngleRadians =
        ((233 : ℝ) / 800) * Real.cos setup.leftPlasticAngleRadians := by
    rw [Real.tan_eq_sin_div_cos] at htan
    exact (div_eq_iff hcospos.ne').mp htan
  have hplastic_sin_sq :
      (694289 : ℝ) * Real.sin setup.leftPlasticAngleRadians ^ 2 = 54289 := by
    nlinarith [Real.sin_sq_add_cos_sq setup.leftPlasticAngleRadians]
  have hsnell := _laws.left_edge_snell_law
  simp only [SnellLawAtInterface, _figure.air_index_readout,
    _figure.plastic_index_readout] at hsnell
  have hincidence_sin_sq :
      (277715600 : ℝ) * Real.sin setup.incidenceAngleRadians ^ 2 =
        52171729 := by
    nlinarith
  have hincidence_sin_pos :
      0 < Real.sin setup.incidenceAngleRadians := by
    apply Real.sin_pos_of_pos_of_lt_pi _laws.incidence_angle_acute.1
    linarith [_laws.incidence_angle_acute.2, Real.pi_pos]
  have hincidence_sin_lower :
      (4333 : ℝ) / 10000 < Real.sin setup.incidenceAngleRadians := by
    nlinarith [sq_nonneg
      (Real.sin setup.incidenceAngleRadians - (4333 : ℝ) / 10000)]
  have hincidence_sin_upper :
      Real.sin setup.incidenceAngleRadians < (4339 : ℝ) / 10000 := by
    nlinarith [sq_nonneg
      (Real.sin setup.incidenceAngleRadians - (4339 : ℝ) / 10000)]
  have hsin_448 :
      Real.sin ((56 : ℝ) / 125) < (4333 : ℝ) / 10000 := by
    let y : ℝ := (56 : ℝ) / 375
    have hy : 0 ≤ y := by norm_num [y]
    have hyabs : |y| ≤ 1 := by
      rw [abs_of_nonneg hy]
      norm_num [y]
    have hb := Real.sin_bound hyabs
    rw [abs_of_nonneg hy, abs_le] at hb
    have hslo :
        y - y ^ 3 / 6 - y ^ 4 * (5 / 96) ≤ Real.sin y := by
      linarith [hb.1]
    have hlo :
        (0 : ℝ) ≤ y - y ^ 3 / 6 - y ^ 4 * (5 / 96) := by
      norm_num [y]
    have hpow :
        (y - y ^ 3 / 6 - y ^ 4 * (5 / 96)) ^ 3 ≤
          Real.sin y ^ 3 :=
      pow_le_pow_left₀ hlo hslo 3
    have htriple :
        Real.sin ((56 : ℝ) / 125) =
          3 * Real.sin y - 4 * Real.sin y ^ 3 := by
      rw [show (56 : ℝ) / 125 = 3 * y by norm_num [y],
        Real.sin_three_mul]
    rw [htriple]
    nlinarith
  have hsin_449 :
      (4339 : ℝ) / 10000 < Real.sin ((449 : ℝ) / 1000) := by
    let y : ℝ := (449 : ℝ) / 3000
    have hy : 0 ≤ y := by norm_num [y]
    have hyabs : |y| ≤ 1 := by
      rw [abs_of_nonneg hy]
      norm_num [y]
    have hb := Real.sin_bound hyabs
    rw [abs_of_nonneg hy, abs_le] at hb
    have hslo :
        y - y ^ 3 / 6 - y ^ 4 * (5 / 96) ≤ Real.sin y := by
      linarith [hb.1]
    have hshi :
        Real.sin y ≤ y - y ^ 3 / 6 + y ^ 4 * (5 / 96) := by
      linarith [hb.2]
    have hsin_nonneg : 0 ≤ Real.sin y := by
      have hlo :
          (0 : ℝ) ≤ y - y ^ 3 / 6 - y ^ 4 * (5 / 96) := by
        norm_num [y]
      linarith
    have hpow :
        Real.sin y ^ 3 ≤
          (y - y ^ 3 / 6 + y ^ 4 * (5 / 96)) ^ 3 :=
      pow_le_pow_left₀ hsin_nonneg hshi 3
    have htriple :
        Real.sin ((449 : ℝ) / 1000) =
          3 * Real.sin y - 4 * Real.sin y ^ 3 := by
      rw [show (449 : ℝ) / 1000 = 3 * y by norm_num [y],
        Real.sin_three_mul]
    rw [htriple]
    nlinarith
  have hincidence_lower :
      (56 : ℝ) / 125 ≤ setup.incidenceAngleRadians := by
    by_contra h
    have hlt :
        setup.incidenceAngleRadians < (56 : ℝ) / 125 :=
      lt_of_not_ge h
    have hsin_lt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := setup.incidenceAngleRadians) (y := (56 : ℝ) / 125)
      (by linarith [_laws.incidence_angle_acute.1, Real.pi_pos])
      (by nlinarith [Real.two_le_pi]) hlt
    linarith
  have hincidence_upper :
      setup.incidenceAngleRadians ≤ (449 : ℝ) / 1000 := by
    by_contra h
    have hlt :
        (449 : ℝ) / 1000 < setup.incidenceAngleRadians :=
      lt_of_not_ge h
    have hsin_lt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := (449 : ℝ) / 1000) (y := setup.incidenceAngleRadians)
      (by linarith [Real.pi_pos]) _laws.incidence_angle_acute.2.le hlt
    linarith
  -- The exact half-angle value at `π / 16`, together with the certified
  -- remainder in `Real.sin_bound`, supplies the modest decimal bounds on `π`
  -- needed to turn the rational radian bracket into a degree-rounding result.
  have hr2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2_lower : (1.41421 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr2_upper : Real.sqrt 2 < (1.414214 : ℝ) := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr3_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
  have hr3_sq :
      Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hr3_arg
  have hr3_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have hr3_lower :
      (1.8477581 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hr2_lower, hr3_sq, hr3_nonneg]
  have hr3_upper :
      Real.sqrt (2 + Real.sqrt 2) < (1.8477595 : ℝ) := by
    nlinarith only [hr2_upper, hr3_sq, hr3_nonneg]
  have hs_arg : 0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt 2) := by
    linarith only [hr3_upper]
  have hs_sq :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hs_arg
  have hs_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hs_lower :
      (0.39018 : ℝ) <
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [hr3_upper, hs_sq, hs_nonneg]
  have hs_upper :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
        (0.390182 : ℝ) := by
    nlinarith only [hr3_lower, hs_sq, hs_nonneg]
  have hsin_pi_lower :
      (0.19509 : ℝ) < Real.sin (Real.pi / 16) := by
    rw [Real.sin_pi_div_sixteen]
    linarith only [hs_lower]
  have hsin_pi_upper :
      Real.sin (Real.pi / 16) < (0.195091 : ℝ) := by
    rw [Real.sin_pi_div_sixteen]
    linarith only [hs_upper]
  let x : ℝ := Real.pi / 16
  have hx_nonneg : 0 ≤ x := by positivity
  have hx_le_quarter : x ≤ (1 / 4 : ℝ) := by
    dsimp [x]
    nlinarith only [Real.pi_le_four]
  have hx_abs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx_nonneg]
    linarith only [hx_le_quarter]
  have hsin_approx := Real.sin_bound hx_abs
  rw [abs_of_nonneg hx_nonneg] at hsin_approx
  have hsin_approx_lower := (abs_le.mp hsin_approx).1
  have hsin_approx_upper := (abs_le.mp hsin_approx).2
  have hpi_gt_31 : (3.1 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.1 : ℝ) := le_of_not_gt h
    have hx_le : x ≤ (3.1 : ℝ) / 16 := by
      dsimp [x]
      nlinarith only [hpi_le]
    have hxfourth : x ^ 4 ≤ ((3.1 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_le 4
    dsimp [x] at hsin_approx_upper hxfourth
    nlinarith only [hsin_pi_lower, hsin_approx_upper, hxfourth,
      hpi_le, sq_nonneg (Real.pi / 16)]
  have hpi_lower : (3.139 : ℝ) < Real.pi := by
    have hx_lower : (3.1 : ℝ) / 16 ≤ x := by
      dsimp [x]
      nlinarith only [hpi_gt_31.le]
    have hxcube : ((3.1 : ℝ) / 16) ^ 3 ≤ x ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx_lower 3
    by_contra h
    have hpi_le : Real.pi ≤ (3.139 : ℝ) := le_of_not_gt h
    have hx_le : x ≤ (3.139 : ℝ) / 16 := by
      dsimp [x]
      nlinarith only [hpi_le]
    have hxfourth : x ^ 4 ≤ ((3.139 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_le 4
    dsimp [x] at hsin_approx_upper hxcube hxfourth
    nlinarith only [hsin_pi_lower, hsin_approx_upper, hxcube,
      hxfourth, hpi_le]
  have hpi_lt_32 : Real.pi < (3.2 : ℝ) := by
    have hxcube : x ^ 3 ≤ (1 / 4 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hx_nonneg hx_le_quarter 3
    have hxfourth : x ^ 4 ≤ (1 / 4 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_le_quarter 4
    by_contra h
    have hpi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [x] at hsin_approx_lower hxcube hxfourth
    nlinarith only [hsin_pi_upper, hsin_approx_lower, hxcube,
      hxfourth, hpi_ge]
  have hx_le_32 : x ≤ (3.2 : ℝ) / 16 := by
    dsimp [x]
    nlinarith only [hpi_lt_32.le]
  have hpi_lt_315 : Real.pi < (3.15 : ℝ) := by
    have hxcube : x ^ 3 ≤ ((3.2 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hx_nonneg hx_le_32 3
    have hxfourth : x ^ 4 ≤ ((3.2 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_le_32 4
    by_contra h
    have hpi_ge : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [x] at hsin_approx_lower hxcube hxfourth
    nlinarith only [hsin_pi_upper, hsin_approx_lower, hxcube,
      hxfourth, hpi_ge]
  have hx_le_315 : x ≤ (3.15 : ℝ) / 16 := by
    dsimp [x]
    nlinarith only [hpi_lt_315.le]
  have hpi_lt_3145 : Real.pi < (3.145 : ℝ) := by
    have hxcube : x ^ 3 ≤ ((3.15 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hx_nonneg hx_le_315 3
    have hxfourth : x ^ 4 ≤ ((3.15 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_le_315 4
    by_contra h
    have hpi_ge : (3.145 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [x] at hsin_approx_lower hxcube hxfourth
    nlinarith only [hsin_pi_upper, hsin_approx_lower, hxcube,
      hxfourth, hpi_ge]
  have hpi_upper : Real.pi < (3.143 : ℝ) := by
    have hx_le : x ≤ (3.145 : ℝ) / 16 := by
      dsimp [x]
      nlinarith only [hpi_lt_3145.le]
    have hxcube : x ^ 3 ≤ ((3.145 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hx_nonneg hx_le 3
    have hxfourth : x ^ 4 ≤ ((3.145 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_le 4
    by_contra h
    have hpi_ge : (3.143 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [x] at hsin_approx_lower hxcube hxfourth
    nlinarith only [hsin_pi_upper, hsin_approx_lower, hxcube,
      hxfourth, hpi_ge]
  simp only [MatchesAnswerToNearestTenthDegree, answerAngleDegrees,
    degreesToRadians]
  rw [abs_le]
  constructor <;>
    nlinarith only [hincidence_lower, hincidence_upper, hpi_lower, hpi_upper]

end PhyXMiniProblems.ProblemPhyXMini0013
