import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0095

open Dimension

/-!
# Estimating the refractive index of water from an apparent line shift

A line drawn beneath a glass is viewed obliquely through the water.  The
primary figure labels the apparent horizontal shift by `s`, the horizontal run
of the actual in-water ray by `d`, and the water depth by `H`.  The in-water
and emergent angles from the vertical surface normal are `θ_a` and `θ_b`.

Physical lengths are represented by Physlib dimensionful quantities.  Their
SI projections are used together only in homogeneous equations and ratios.
Angles are real-valued radian readouts, and refractive indices are
dimensionless real readouts.
-/

/-- A signed physical length with a real-valued carrier. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The two homogeneous optical media on the depicted light path. -/
inductive OpticalMedium where
  | water
  | air
  deriving DecidableEq, Repr

/-- The local shape used for the water--air interface in the ray model. -/
inductive InterfaceModel where
  | planar
  | curved
  deriving DecidableEq, Repr

/--
The physical quantities and categorical labels in the primary ray diagram.

`apparentShift` is the labeled distance `s` from the image of the line to the
drawn line. `waterHorizontalRun` is the labeled distance `d` from the drawn
line to the foot of the surface-crossing normal. `waterDepth` is `H`.
`waterAngleRadians` and `airAngleRadians` are respectively the figure labels
`θ_a` and `θ_b`, both measured from a vertical normal.
-/
structure LineShiftRefractionSetup where
  apparentShift : LengthQuantity
  waterHorizontalRun : LengthQuantity
  waterDepth : LengthQuantity
  waterAngleRadians : ℝ
  airAngleRadians : ℝ
  refractiveIndexDimensionless : OpticalMedium → ℝ
  lineSourceMedium : OpticalMedium
  observerMedium : OpticalMedium
  interfaceModel : InterfaceModel

/--
The categorical labels and calibrated ambient-air value shown or implied by
the primary figure.  This contains no numerical value for the water index.
-/
structure MatchesWaterGlassFigure
    (setup : LineShiftRefractionSetup) : Prop where
  source_line_is_under_water : setup.lineSourceMedium = .water
  observer_is_in_air : setup.observerMedium = .air
  locally_planar_surface : setup.interfaceModel = .planar
  ambient_air_index : setup.refractiveIndexDimensionless .air = 1

/--
Positive length and refractive-index readouts and the acute physical branches
of the two normal angles.  The inequality between the angles records the
bending away from the normal on emergence from water into air.
-/
structure HasPhysicalRefractionConfiguration
    (setup : LineShiftRefractionSetup) : Prop where
  apparent_shift_positive : 0 < lengthInMeters setup.apparentShift
  water_horizontal_run_positive :
    0 < lengthInMeters setup.waterHorizontalRun
  water_depth_positive : 0 < lengthInMeters setup.waterDepth
  refractive_indices_positive :
    ∀ medium, 0 < setup.refractiveIndexDimensionless medium
  water_angle_acute :
    setup.waterAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  air_angle_acute :
    setup.airAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  bends_away_from_normal :
    setup.waterAngleRadians < setup.airAngleRadians

/--
The two right-triangle relations read from the dashed normals in the figure.
The actual in-water ray has horizontal run `d`; extending the air ray backward
to the apparent line gives horizontal run `d + s` over the same height `H`.
-/
def SatisfiesLineShiftGeometry
    (setup : LineShiftRefractionSetup) : Prop :=
  lengthInMeters setup.waterDepth * Real.tan setup.waterAngleRadians =
      lengthInMeters setup.waterHorizontalRun ∧
    lengthInMeters setup.waterDepth * Real.tan setup.airAngleRadians =
      lengthInMeters setup.waterHorizontalRun +
        lengthInMeters setup.apparentShift

/-- Snell's law at the water--air surface, `n_w sin θ_a = n_a sin θ_b`. -/
def SatisfiesWaterToAirSnellLaw
    (setup : LineShiftRefractionSetup) : Prop :=
  setup.refractiveIndexDimensionless .water *
      Real.sin setup.waterAngleRadians =
    setup.refractiveIndexDimensionless .air *
      Real.sin setup.airAngleRadians

/--
Conservative scale readouts from the supplied raster diagram.  They express
only ratios of the three labeled physical lengths, so the statement is
independent of the common length unit.  The visible endpoints give roughly
`s / d = 0.47` and `H / d = 2.15`; the intervals allow drawing and pixel
uncertainty.  No refractive-index value occurs here.
-/
structure MatchesPrimaryFigureScaleReadouts
    (setup : LineShiftRefractionSetup) : Prop where
  shift_lower_bound :
    (45 : ℝ) / 100 * lengthInMeters setup.waterHorizontalRun ≤
      lengthInMeters setup.apparentShift
  shift_upper_bound :
    lengthInMeters setup.apparentShift ≤
      (48 : ℝ) / 100 * lengthInMeters setup.waterHorizontalRun
  depth_lower_bound :
    (21 : ℝ) / 10 * lengthInMeters setup.waterHorizontalRun ≤
      lengthInMeters setup.waterDepth
  depth_upper_bound :
    lengthInMeters setup.waterDepth ≤
      (22 : ℝ) / 10 * lengthInMeters setup.waterHorizontalRun

/-- Labels of the four multiple-choice answers in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless refractive-index estimate printed beside each choice. -/
def answerRefractiveIndex : AnswerChoice → ℝ
  | .A => (13 : ℝ) / 10
  | .B => (21 : ℝ) / 10
  | .C => (16 : ℝ) / 10
  | .D => (19 : ℝ) / 10

/--
A choice is the unique closest displayed value to a dimensionless estimate.
This generic comparison does not designate any problem-specific answer.
-/
def IsUniqueClosestAnswer
    (estimate : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |estimate - answerRefractiveIndex choice| <
      |estimate - answerRefractiveIndex other|

/--
The measured geometry, planar-ray relations, and Snell's law estimate the
water refractive index to the displayed precision as `1.3`; this is uniquely
closest to answer choice A.

This formalizes `thm:physics:phyx_mini_0095:target`.
-/
theorem waterRefractiveIndex_estimate_is_answer_A
    (setup : LineShiftRefractionSetup)
    (_figure : MatchesWaterGlassFigure setup)
    (_physical : HasPhysicalRefractionConfiguration setup)
    (_scale : MatchesPrimaryFigureScaleReadouts setup)
    (_geometry : SatisfiesLineShiftGeometry setup)
    (_snell : SatisfiesWaterToAirSnellLaw setup) :
    |setup.refractiveIndexDimensionless .water -
        answerRefractiveIndex .A| < (1 : ℝ) / 20 ∧
      IsUniqueClosestAnswer
        (setup.refractiveIndexDimensionless .water) .A := by
  let d := lengthInMeters setup.waterHorizontalRun
  let s := lengthInMeters setup.apparentShift
  let h := lengthInMeters setup.waterDepth
  let a := setup.waterAngleRadians
  let b := setup.airAngleRadians
  let n := setup.refractiveIndexDimensionless .water

  have hd : 0 < d := by
    simpa [d] using _physical.water_horizontal_run_positive
  have hn : 0 < n := by
    simpa [n] using _physical.refractive_indices_positive .water
  have ha_mem : a ∈ Set.Ioo 0 (Real.pi / 2) := by
    simpa [a] using _physical.water_angle_acute
  have hb_mem : b ∈ Set.Ioo 0 (Real.pi / 2) := by
    simpa [b] using _physical.air_angle_acute
  have ha_cos_pos : 0 < Real.cos a := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [ha_mem.1, Real.pi_pos]
    · exact ha_mem.2
  have hb_cos_pos : 0 < Real.cos b := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [hb_mem.1, Real.pi_pos]
    · exact hb_mem.2

  have hgeometry_a : h * Real.tan a = d := by
    simpa [SatisfiesLineShiftGeometry, h, a, d] using _geometry.1
  have hgeometry_b : h * Real.tan b = d + s := by
    simpa [SatisfiesLineShiftGeometry, h, b, d, s] using _geometry.2
  have htan_cos_a : Real.tan a * Real.cos a = Real.sin a := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt ha_cos_pos]
  have htan_cos_b : Real.tan b * Real.cos b = Real.sin b := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hb_cos_pos]
  have hsin_cos_a : h * Real.sin a = d * Real.cos a := by
    calc
      h * Real.sin a = h * (Real.tan a * Real.cos a) := by
        rw [htan_cos_a]
      _ = (h * Real.tan a) * Real.cos a := by ring
      _ = d * Real.cos a := by rw [hgeometry_a]
  have hsin_cos_b : h * Real.sin b = (d + s) * Real.cos b := by
    calc
      h * Real.sin b = h * (Real.tan b * Real.cos b) := by
        rw [htan_cos_b]
      _ = (h * Real.tan b) * Real.cos b := by ring
      _ = (d + s) * Real.cos b := by rw [hgeometry_b]

  have hsin_sq_a :
      (h ^ 2 + d ^ 2) * Real.sin a ^ 2 = d ^ 2 := by
    calc
      (h ^ 2 + d ^ 2) * Real.sin a ^ 2 =
          (h * Real.sin a) ^ 2 + d ^ 2 * Real.sin a ^ 2 := by ring
      _ = (d * Real.cos a) ^ 2 + d ^ 2 * Real.sin a ^ 2 := by
        rw [hsin_cos_a]
      _ = d ^ 2 * (Real.sin a ^ 2 + Real.cos a ^ 2) := by ring
      _ = d ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hsin_sq_b :
      (h ^ 2 + (d + s) ^ 2) * Real.sin b ^ 2 = (d + s) ^ 2 := by
    calc
      (h ^ 2 + (d + s) ^ 2) * Real.sin b ^ 2 =
          (h * Real.sin b) ^ 2 + (d + s) ^ 2 * Real.sin b ^ 2 := by ring
      _ = ((d + s) * Real.cos b) ^ 2 +
          (d + s) ^ 2 * Real.sin b ^ 2 := by
        rw [hsin_cos_b]
      _ = (d + s) ^ 2 * (Real.sin b ^ 2 + Real.cos b ^ 2) := by ring
      _ = (d + s) ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

  have hsnell : n * Real.sin a = Real.sin b := by
    simpa [SatisfiesWaterToAirSnellLaw, n, a, b,
      _figure.ambient_air_index] using _snell
  have hsnell_sq : n ^ 2 * Real.sin a ^ 2 = Real.sin b ^ 2 := by
    calc
      n ^ 2 * Real.sin a ^ 2 = (n * Real.sin a) ^ 2 := by ring
      _ = Real.sin b ^ 2 := by rw [hsnell]
  have hindex_identity :
      n ^ 2 * d ^ 2 * (h ^ 2 + (d + s) ^ 2) =
        (d + s) ^ 2 * (h ^ 2 + d ^ 2) := by
    calc
      n ^ 2 * d ^ 2 * (h ^ 2 + (d + s) ^ 2) =
          n ^ 2 * ((h ^ 2 + d ^ 2) * Real.sin a ^ 2) *
            (h ^ 2 + (d + s) ^ 2) := by rw [hsin_sq_a]
      _ = (h ^ 2 + d ^ 2) *
            (n ^ 2 * Real.sin a ^ 2) *
            (h ^ 2 + (d + s) ^ 2) := by ring
      _ = (h ^ 2 + d ^ 2) * Real.sin b ^ 2 *
            (h ^ 2 + (d + s) ^ 2) := by rw [hsnell_sq]
      _ = (h ^ 2 + d ^ 2) *
            ((h ^ 2 + (d + s) ^ 2) * Real.sin b ^ 2) := by ring
      _ = (d + s) ^ 2 * (h ^ 2 + d ^ 2) := by rw [hsin_sq_b]; ring

  let z := (d + s) / d
  let y := h / d
  have hz_lower : (29 : ℝ) / 20 ≤ z := by
    apply (le_div_iff₀ hd).2
    have hscale := _scale.shift_lower_bound
    change (45 : ℝ) / 100 * d ≤ s at hscale
    nlinarith
  have hz_upper : z ≤ (37 : ℝ) / 25 := by
    apply (div_le_iff₀ hd).2
    have hscale := _scale.shift_upper_bound
    change s ≤ (48 : ℝ) / 100 * d at hscale
    nlinarith
  have hy_lower : (21 : ℝ) / 10 ≤ y := by
    apply (le_div_iff₀ hd).2
    simpa [h, d] using _scale.depth_lower_bound
  have hy_upper : y ≤ (11 : ℝ) / 5 := by
    apply (div_le_iff₀ hd).2
    have hscale := _scale.depth_upper_bound
    change h ≤ (22 : ℝ) / 10 * d at hscale
    nlinarith
  have hz_pos : 0 < z := by nlinarith [hz_lower]
  have hy_pos : 0 < y := by nlinarith [hy_lower]
  have hz_sq_lower : ((29 : ℝ) / 20) ^ 2 ≤ z ^ 2 := by
    nlinarith only [hz_lower]
  have hz_sq_upper : z ^ 2 ≤ ((37 : ℝ) / 25) ^ 2 := by
    nlinarith only [hz_upper, hz_pos]
  have hy_sq_lower : ((21 : ℝ) / 10) ^ 2 ≤ y ^ 2 := by
    nlinarith only [hy_lower]
  have hy_sq_upper : y ^ 2 ≤ ((11 : ℝ) / 5) ^ 2 := by
    nlinarith only [hy_upper, hy_pos]

  have hnormalized :
      n ^ 2 * (y ^ 2 + z ^ 2) = z ^ 2 * (y ^ 2 + 1) := by
    dsimp [y, z]
    field_simp [ne_of_gt hd]
    ring_nf at hindex_identity ⊢
    exact hindex_identity

  have hupper_mono_z :
      0 ≤ (((37 : ℝ) / 25) ^ 2 - z ^ 2) * (400 * y ^ 2 - 329) := by
    apply mul_nonneg (sub_nonneg.mpr hz_sq_upper)
    nlinarith only [hy_sq_lower]
  have hupper_mono_y :
      0 ≤ (((11 : ℝ) / 5) ^ 2 - y ^ 2) *
        (400 * ((37 : ℝ) / 25) ^ 2 - 729) := by
    apply mul_nonneg (sub_nonneg.mpr hy_sq_upper)
    norm_num
  have hupper_polynomial :
      400 * z ^ 2 * (y ^ 2 + 1) <
        729 * (y ^ 2 + z ^ 2) := by
    nlinarith only [hupper_mono_z, hupper_mono_y]

  have hlower_mono_z :
      0 ≤ (z ^ 2 - ((29 : ℝ) / 20) ^ 2) * (16 * y ^ 2 - 9) := by
    apply mul_nonneg (sub_nonneg.mpr hz_sq_lower)
    nlinarith only [hy_sq_lower]
  have hlower_mono_y :
      0 ≤ (y ^ 2 - ((21 : ℝ) / 10) ^ 2) *
        (16 * ((29 : ℝ) / 20) ^ 2 - 25) := by
    apply mul_nonneg (sub_nonneg.mpr hy_sq_lower)
    norm_num
  have hlower_polynomial :
      25 * (y ^ 2 + z ^ 2) <
        16 * z ^ 2 * (y ^ 2 + 1) := by
    nlinarith only [hlower_mono_z, hlower_mono_y]

  have hdenominator : 0 < y ^ 2 + z ^ 2 := by
    nlinarith only [sq_nonneg y, pow_pos hz_pos 2]
  have hn_sq_lower : ((5 : ℝ) / 4) ^ 2 < n ^ 2 := by
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hdenominator)
    rw [hnormalized]
    nlinarith only [hlower_polynomial]
  have hn_sq_upper : n ^ 2 < ((27 : ℝ) / 20) ^ 2 := by
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hdenominator)
    rw [hnormalized]
    nlinarith only [hupper_polynomial]
  have hn_lower : (5 : ℝ) / 4 < n := by
    nlinarith only [hn, hn_sq_lower]
  have hn_upper : n < (27 : ℝ) / 20 := by
    nlinarith only [hn, hn_sq_upper]
  have hclose : |n - (13 : ℝ) / 10| < (1 : ℝ) / 20 := by
    rw [abs_lt]
    constructor <;> nlinarith only [hn_lower, hn_upper]

  change |n - answerRefractiveIndex .A| < (1 : ℝ) / 20 ∧
    IsUniqueClosestAnswer n .A
  constructor
  · simpa [answerRefractiveIndex] using hclose
  · unfold IsUniqueClosestAnswer
    intro other hother
    cases other with
    | A => exact (hother rfl).elim
    | B =>
        simp only [answerRefractiveIndex]
        rw [abs_of_nonpos (by nlinarith only [hn_upper] :
          n - (21 : ℝ) / 10 ≤ 0)]
        nlinarith only [hclose, hn_upper]
    | C =>
        simp only [answerRefractiveIndex]
        rw [abs_of_nonpos (by nlinarith only [hn_upper] :
          n - (16 : ℝ) / 10 ≤ 0)]
        nlinarith only [hclose, hn_upper]
    | D =>
        simp only [answerRefractiveIndex]
        rw [abs_of_nonpos (by nlinarith only [hn_upper] :
          n - (19 : ℝ) / 10 ≤ 0)]
        nlinarith only [hclose, hn_upper]

end PhyXMiniProblems.ProblemPhyXMini0095
