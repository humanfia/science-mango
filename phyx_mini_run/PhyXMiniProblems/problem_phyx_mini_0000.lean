import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Optics.Basic

namespace PhyXMiniProblems.ProblemPhyXMini0000

/-- The three optical media, in their top-to-bottom order in the figure. -/
inductive OpticalMedium where
  | air
  | linseedOil
  | water
  deriving DecidableEq, Repr

/-- The two parallel material interfaces shown in the figure. -/
inductive RefractionInterface where
  | airLinseedOil
  | linseedOilWater
  deriving DecidableEq, Repr

/-- Labels for the dashed normals through the two refraction points. -/
inductive NormalLabel where
  | N
  | NPrime
  deriving DecidableEq, Repr

/-- The three segments of the single light path, one in each medium. -/
inductive RaySegment where
  | inAir
  | inLinseedOil
  | inWater
  deriving DecidableEq, Repr

def RefractionInterface.incidentMedium : RefractionInterface → OpticalMedium
  | .airLinseedOil => .air
  | .linseedOilWater => .linseedOil

def RefractionInterface.transmittedMedium : RefractionInterface → OpticalMedium
  | .airLinseedOil => .linseedOil
  | .linseedOilWater => .water

def RefractionInterface.incidentRay : RefractionInterface → RaySegment
  | .airLinseedOil => .inAir
  | .linseedOilWater => .inLinseedOil

def RefractionInterface.transmittedRay : RefractionInterface → RaySegment
  | .airLinseedOil => .inLinseedOil
  | .linseedOilWater => .inWater

def RefractionInterface.normal : RefractionInterface → NormalLabel
  | .airLinseedOil => .N
  | .linseedOilWater => .NPrime

/-- Physical data attached to the three-layer refraction diagram.

Refractive indices are dimensionless scalar readouts. Angles are physical
angles modulo a full turn, represented by Mathlib's `Real.Angle`.
-/
structure ThreeLayerRefractionSetup where
  refractiveIndexDimensionless : OpticalMedium → ℝ
  angleToNormal : RaySegment → NormalLabel → Real.Angle

/-- Convert a numerical degree reading into a physical angle. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- The representative of an acute physical angle, expressed in degrees. -/
noncomputable def degreeReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- Refraction angles in this diagram lie between the ray and its normal. -/
def IsPhysicalRefractionAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal ≤ Real.pi / 2

/-- The dimensionless refractive index is physically positive in every layer. -/
def HasPositiveRefractiveIndices (setup : ThreeLayerRefractionSetup) : Prop :=
  ∀ medium, 0 < setup.refractiveIndexDimensionless medium

/-- Snell's law at one of the two interfaces in the diagram. -/
def SatisfiesSnellLawAt
    (setup : ThreeLayerRefractionSetup)
    (interface : RefractionInterface) : Prop :=
  setup.refractiveIndexDimensionless interface.incidentMedium *
      Real.Angle.sin (setup.angleToNormal interface.incidentRay interface.normal) =
    setup.refractiveIndexDimensionless interface.transmittedMedium *
      Real.Angle.sin (setup.angleToNormal interface.transmittedRay interface.normal)

/-- The angle labelled `θ` in the air layer. -/
def theta (setup : ThreeLayerRefractionSetup) : Real.Angle :=
  setup.angleToNormal .inAir .N

/-- The angle labelled `φ₁`, measured from normal `N` in the oil layer. -/
def phiOne (setup : ThreeLayerRefractionSetup) : Real.Angle :=
  setup.angleToNormal .inLinseedOil .N

/-- The requested angle `θ'`, measured from normal `N'` in the water layer. -/
def thetaPrime (setup : ThreeLayerRefractionSetup) : Real.Angle :=
  setup.angleToNormal .inWater .NPrime

/-- Parallel interfaces make the oil ray have the same angle to `N` and `N'`. -/
def HasParallelInterfaceGeometry (setup : ThreeLayerRefractionSetup) : Prop :=
  phiOne setup = setup.angleToNormal .inLinseedOil .NPrime

/-- The four numerical answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

def answerInDegrees : AnswerChoice → ℝ
  | .A => 28.5
  | .B => 30.4
  | .C => 22.3
  | .D => 31.1

/-- A displayed one-decimal-place choice matches an angle when their degree
readouts differ by at most half of one tenth of a degree. -/
def MatchesAnswerToNearestTenth
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreeReadout angle - answerInDegrees choice| ≤ 0.05

/-- The given `20.0°` oil angle transfers from `N` to `N'` because the two
interfaces, and hence their normals, are parallel. -/
lemma oil_angle_at_lower_interface
    (setup : ThreeLayerRefractionSetup)
    (h_phiOne : phiOne setup = degrees 20.0)
    (h_parallel : HasParallelInterfaceGeometry setup) :
    setup.angleToNormal .inLinseedOil .NPrime = degrees 20.0 := by
  exact h_parallel.symm.trans h_phiOne

/-- In the depicted air--linseed-oil--water system, Snell's law at the lower
interface makes the requested water angle match answer C, `22.3°`. The water
index `1.333` is the standard material-table readout implicit in the label
"Water"; the tolerance records that the choices are displayed to one decimal
place. -/
theorem thetaPrime_matches_choice_C
    (setup : ThreeLayerRefractionSetup)
    (h_indices_positive : HasPositiveRefractiveIndices setup)
    (h_linseedOil_index : setup.refractiveIndexDimensionless .linseedOil = 1.48)
    (h_water_index : setup.refractiveIndexDimensionless .water = 1.333)
    (h_phiOne : phiOne setup = degrees 20.0)
    (h_parallel : HasParallelInterfaceGeometry setup)
    (h_snell : ∀ interface, SatisfiesSnellLawAt setup interface)
    (h_thetaPrime_physical : IsPhysicalRefractionAngle (thetaPrime setup)) :
    MatchesAnswerToNearestTenth (thetaPrime setup) .C := by
    have h_oil := oil_angle_at_lower_interface setup h_phiOne h_parallel
    have hsnell := h_snell .linseedOilWater
    simp only [SatisfiesSnellLawAt, RefractionInterface.incidentMedium,
      RefractionInterface.transmittedMedium, RefractionInterface.incidentRay,
      RefractionInterface.transmittedRay, RefractionInterface.normal,
      h_linseedOil_index, h_water_index] at hsnell
    rw [h_oil] at hsnell
    change (1.48 : ℝ) * Real.Angle.sin (degrees 20.0) =
      1.333 * Real.Angle.sin (thetaPrime setup) at hsnell
    simp only [degrees, Real.Angle.sin_coe] at hsnell
    norm_num at hsnell
    rw [← Real.Angle.sin_toReal (thetaPrime setup)] at hsnell
    have hsnell' : (37 / 25 : ℝ) * Real.sin (Real.pi / 9) =
        (1333 / 1000 : ℝ) * Real.sin (thetaPrime setup).toReal := by
      convert hsnell using 1
      all_goals ring_nf
  
    have hsin_pi32_bounds :
        (0.09801 : ℝ) < Real.sin (Real.pi / 32) ∧
          Real.sin (Real.pi / 32) < (0.09802 : ℝ) := by
      clear h_indices_positive hsnell' hsnell h_oil h_thetaPrime_physical
        h_snell h_parallel h_phiOne h_water_index h_linseedOil_index
      have hr2_lower : (1.41421 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hr2_upper : Real.sqrt 2 < (1.41422 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hr3_lower :
          (1.847757 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num at ⊢
        linarith
      have hr3_upper :
          Real.sqrt (2 + Real.sqrt 2) < (1.847762 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num at ⊢
        linarith
      have hr4_lower :
          (1.961570 : ℝ) <
            Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num at ⊢
        linarith
      have hr4_upper :
          Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
            (1.961572 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num at ⊢
        linarith
      have hs_lower :
          (0.19603 : ℝ) <
            Real.sqrt
              (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num at ⊢
        linarith
      have hs_upper :
          Real.sqrt
              (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) <
            (0.19604 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num at ⊢
        linarith
      rw [Real.sin_pi_div_thirty_two]
      constructor <;> linarith

    have hpi_bounds :
        (3.141 : ℝ) < Real.pi ∧ Real.pi < (3.142 : ℝ) := by
      clear h_indices_positive hsnell' hsnell h_oil h_thetaPrime_physical
        h_snell h_parallel h_phiOne h_water_index h_linseedOil_index
      let x : ℝ := Real.pi / 32
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        positivity
      have hx3_nonneg : 0 ≤ x ^ 3 := pow_nonneg hx_nonneg _
      have hx_le_eighth : x ≤ (1 / 8 : ℝ) := by
        dsimp [x]
        linarith [Real.pi_le_four]
      have hx_abs : |x| ≤ 1 := by
        rw [abs_of_nonneg hx_nonneg]
        linarith
      have hsin_approx := Real.sin_bound hx_abs
      rw [abs_of_nonneg hx_nonneg] at hsin_approx
      have happrox_lower := (abs_le.mp hsin_approx).1
      have happrox_upper := (abs_le.mp hsin_approx).2
      constructor
      · by_contra h
        have hx_upper : x ≤ (3.141 / 32 : ℝ) := by
          dsimp [x]
          linarith
        have hx_upper' : x ≤ (1 / 10 : ℝ) := by
          linarith
        have hx4_upper : x ^ 4 ≤ (1 / 10 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hx_nonneg hx_upper' 4
        have hx_lower : (0.097 : ℝ) ≤ x := by
          by_contra hx
          have hx' : x < (0.097 : ℝ) := lt_of_not_ge hx
          have hsin_lower := hsin_pi32_bounds.1
          change Real.sin x > (0.09801 : ℝ) at hsin_lower
          norm_num at hx4_upper
          linarith
        have hx3_lower : (0.097 : ℝ) ^ 3 ≤ x ^ 3 :=
          pow_le_pow_left₀ (by norm_num) hx_lower 3
        have hsin_lower := hsin_pi32_bounds.1
        change Real.sin x > (0.09801 : ℝ) at hsin_lower
        norm_num at hx3_lower hx4_upper
        linarith
      · by_contra h
        have hx_lower : (3.142 / 32 : ℝ) ≤ x := by
          dsimp [x]
          linarith
        have hx_upper : x ≤ (0.099 : ℝ) := by
          by_contra hx
          have hx' : (0.099 : ℝ) < x := lt_of_not_ge hx
          have hx3_upper : x ^ 3 ≤ (1 / 8 : ℝ) ^ 3 :=
            pow_le_pow_left₀ hx_nonneg hx_le_eighth 3
          have hx4_upper : x ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
            pow_le_pow_left₀ hx_nonneg hx_le_eighth 4
          have hsin_upper := hsin_pi32_bounds.2
          change Real.sin x < (0.09802 : ℝ) at hsin_upper
          norm_num at hx3_upper hx4_upper
          linarith
        have hx3_upper : x ^ 3 ≤ (0.099 : ℝ) ^ 3 :=
          pow_le_pow_left₀ hx_nonneg hx_upper 3
        have hx4_upper : x ^ 4 ≤ (0.099 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hx_nonneg hx_upper 4
        have hsin_upper := hsin_pi32_bounds.2
        change Real.sin x < (0.09802 : ℝ) at hsin_upper
        norm_num at hx3_upper hx4_upper
        linarith
  
    have hoil_sine_bounds :
        (0.342 : ℝ) < Real.sin (Real.pi / 9) ∧
          Real.sin (Real.pi / 9) < (0.3421 : ℝ) := by
      clear h_indices_positive hsnell' hsnell h_oil h_thetaPrime_physical
        h_snell h_parallel h_phiOne h_water_index h_linseedOil_index
        hsin_pi32_bounds hpi_bounds
      let s := Real.sin (Real.pi / 9)
      have hs_nonneg : 0 ≤ s :=
        Real.sin_nonneg_of_nonneg_of_le_pi
          (by positivity) (by linarith [Real.pi_pos])
      have hs_le_half : s ≤ (1 / 2 : ℝ) := by
        rw [show s = Real.sin (Real.pi / 9) by rfl,
          ← Real.sin_pi_div_six]
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      have hs_sq : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hs_nonneg hs_le_half 2
      norm_num at hs_sq
      have hr3_lower : (1.73205 : ℝ) < Real.sqrt 3 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hr3_upper : Real.sqrt 3 < (1.73206 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have htriple := Real.sin_three_mul (Real.pi / 9)
      rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring,
        Real.sin_pi_div_three] at htriple
      change Real.sqrt 3 / 2 = 3 * s - 4 * s ^ 3 at htriple
      constructor
      · by_contra h
        have hs_le : s ≤ (0.342 : ℝ) := le_of_not_gt h
        have hcoeff :
            0 ≤ 3 - 4 * ((0.342 : ℝ) ^ 2 + 0.342 * s + s ^ 2) := by
          have hmul :
            (0.342 : ℝ) * s ≤ 0.342 * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hs_le_half (by norm_num)
          norm_num at hmul ⊢
          linarith
        have hprod := mul_nonneg (sub_nonneg.mpr hs_le) hcoeff
        ring_nf at hprod
        linarith
      · by_contra h
        have hle : (0.3421 : ℝ) ≤ s := le_of_not_gt h
        have hcoeff :
            0 ≤ 3 - 4 * (s ^ 2 + s * (0.3421 : ℝ) + 0.3421 ^ 2) := by
          have hmul :
            s * (0.3421 : ℝ) ≤ (1 / 2 : ℝ) * 0.3421 :=
          mul_le_mul_of_nonneg_right hs_le_half (by norm_num)
          norm_num at hmul ⊢
          linarith
        have hprod := mul_nonneg (sub_nonneg.mpr hle) hcoeff
        ring_nf at hprod
        linarith
  
    have hendpoint_sine_bounds :
        Real.sin (89 * Real.pi / 720) < (0.379 : ℝ) ∧
          (0.37995 : ℝ) < Real.sin (149 * Real.pi / 1200) := by
      clear h_indices_positive hsnell' hsnell h_oil h_thetaPrime_physical
        h_snell h_parallel h_phiOne h_water_index h_linseedOil_index
        hsin_pi32_bounds hoil_sine_bounds
      constructor
      · let y : ℝ := 89 * Real.pi / 1440
        have hy_nonneg : 0 ≤ y := by
          dsimp [y]
          positivity
        have hy_lower : (0.194 : ℝ) ≤ y := by
          dsimp [y]
          linarith [hpi_bounds.1]
        have hy_upper : y ≤ (0.1942 : ℝ) := by
          dsimp [y]
          linarith [hpi_bounds.2]
        have hy_abs : |y| ≤ 1 := by
          rw [abs_of_nonneg hy_nonneg]
          linarith
        have hsin_approx := Real.sin_bound hy_abs
        have hcos_approx := Real.cos_bound hy_abs
        rw [abs_of_nonneg hy_nonneg] at hsin_approx hcos_approx
        have hsin_approx_upper := (abs_le.mp hsin_approx).2
        have hcos_approx_upper := (abs_le.mp hcos_approx).2
        have hy2_lower : (0.194 : ℝ) ^ 2 ≤ y ^ 2 :=
          pow_le_pow_left₀ (by norm_num) hy_lower 2
        have hy3_lower : (0.194 : ℝ) ^ 3 ≤ y ^ 3 :=
          pow_le_pow_left₀ (by norm_num) hy_lower 3
        have hy4_upper : y ^ 4 ≤ (0.195 : ℝ) ^ 4 := by
          apply pow_le_pow_left₀ hy_nonneg _ 4
          linarith
        norm_num at hy2_lower hy3_lower hy4_upper
        have hsin_upper : Real.sin y < (0.1931 : ℝ) := by
          linarith
        have hcos_upper : Real.cos y < (0.98127 : ℝ) := by
          linarith
        have hsin_nonneg : 0 ≤ Real.sin y :=
          Real.sin_nonneg_of_nonneg_of_le_pi hy_nonneg
            (by dsimp [y]; linarith [Real.pi_pos])
        have hmul_le :
            Real.sin y * Real.cos y ≤ Real.sin y * (0.98127 : ℝ) :=
          mul_le_mul_of_nonneg_left hcos_upper.le hsin_nonneg
        have hmul_lt :
            Real.sin y * (0.98127 : ℝ) < 0.1931 * 0.98127 :=
          mul_lt_mul_of_pos_right hsin_upper (by norm_num)
        norm_num at hmul_lt
        calc
          Real.sin (89 * Real.pi / 720) =
              2 * Real.sin y * Real.cos y := by
            rw [show 89 * Real.pi / 720 = 2 * y by
              dsimp [y]
              ring, Real.sin_two_mul]
          _ < 0.379 := by
            linarith
      · let y : ℝ := 149 * Real.pi / 2400
        have hy_nonneg : 0 ≤ y := by
          dsimp [y]
          positivity
        have hy_lower : (0.195 : ℝ) < y := by
          dsimp [y]
          linarith [hpi_bounds.1]
        have hy_upper : y < (0.1951 : ℝ) := by
          dsimp [y]
          linarith [hpi_bounds.2]
        have hy_abs : |y| ≤ 1 := by
          rw [abs_of_nonneg hy_nonneg]
          linarith
        have hsin_approx := Real.sin_bound hy_abs
        have hcos_approx := Real.cos_bound hy_abs
        rw [abs_of_nonneg hy_nonneg] at hsin_approx hcos_approx
        have hsin_approx_lower := (abs_le.mp hsin_approx).1
        have hcos_approx_lower := (abs_le.mp hcos_approx).1
        have hy2_upper : y ^ 2 ≤ (0.1951 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hy_nonneg hy_upper.le 2
        have hy3_upper : y ^ 3 ≤ (0.1951 : ℝ) ^ 3 :=
          pow_le_pow_left₀ hy_nonneg hy_upper.le 3
        have hy4_upper : y ^ 4 ≤ (0.1951 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hy_nonneg hy_upper.le 4
        norm_num at hy2_upper hy3_upper hy4_upper
        have hsin_lower : (0.19368 : ℝ) < Real.sin y := by
          linarith
        have hcos_lower : (0.98089 : ℝ) < Real.cos y := by
          linarith
        have hmul_one :
            (0.19368 : ℝ) * Real.cos y < Real.sin y * Real.cos y :=
          mul_lt_mul_of_pos_right hsin_lower (by linarith)
        have hmul_two :
            (0.19368 : ℝ) * 0.98089 < 0.19368 * Real.cos y :=
          mul_lt_mul_of_pos_left hcos_lower (by norm_num)
        norm_num at hmul_two
        calc
          (0.37995 : ℝ) < 2 * Real.sin y * Real.cos y := by
            linarith
          _ = Real.sin (149 * Real.pi / 1200) := by
            rw [show 149 * Real.pi / 1200 = 2 * y by
              dsimp [y]
              ring, Real.sin_two_mul]
  
    have htheta_sine_bounds :
        (0.3797 : ℝ) < Real.sin (thetaPrime setup).toReal ∧
          Real.sin (thetaPrime setup).toReal < (0.3799 : ℝ) := by
      constructor <;> linarith [hoil_sine_bounds.1, hoil_sine_bounds.2]
    have hsin_lower :
        Real.sin (89 * Real.pi / 720) <
          Real.sin (thetaPrime setup).toReal := by
      linarith [hendpoint_sine_bounds.1, htheta_sine_bounds.1]
    have hsin_upper :
        Real.sin (thetaPrime setup).toReal <
          Real.sin (149 * Real.pi / 1200) := by
      linarith [htheta_sine_bounds.2, hendpoint_sine_bounds.2]
  
    rcases h_thetaPrime_physical with ⟨htheta_nonneg, htheta_le⟩
    have htheta_bounds :
        89 * Real.pi / 720 < (thetaPrime setup).toReal ∧
          (thetaPrime setup).toReal < 149 * Real.pi / 1200 := by
      constructor
      · by_contra h
        have htheta_upper :
            (thetaPrime setup).toReal ≤ 89 * Real.pi / 720 :=
          le_of_not_gt h
        have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := (thetaPrime setup).toReal)
          (y := 89 * Real.pi / 720)
          (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])
          htheta_upper
        linarith
      · by_contra h
        have htheta_lower :
            149 * Real.pi / 1200 ≤ (thetaPrime setup).toReal :=
          le_of_not_gt h
        have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := 149 * Real.pi / 1200)
          (y := (thetaPrime setup).toReal)
          (by linarith [Real.pi_pos])
          htheta_le
          htheta_lower
        linarith
  
    have hreadout_lower :
        (22.25 : ℝ) ≤ degreeReadout (thetaPrime setup) := by
      apply (le_div_iff₀ Real.pi_pos).2
      linarith [htheta_bounds.1]
    have hreadout_upper :
        degreeReadout (thetaPrime setup) ≤ (22.35 : ℝ) := by
      apply (div_le_iff₀ Real.pi_pos).2
      linarith [htheta_bounds.2]
    change |degreeReadout (thetaPrime setup) - 22.3| ≤ 0.05
    rw [abs_le]
    constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0000
