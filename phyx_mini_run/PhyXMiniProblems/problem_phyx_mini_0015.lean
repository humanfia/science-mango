import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0015

open Dimension

/-- A physical length, independent of the unit system used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The numerical value of a physical length when SI meters are selected. -/
def valueInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The two optical media on opposite sides of the calm pool surface. -/
inductive OpticalRegion where
  | poolWater
  | ambientAir
  deriving DecidableEq, Repr

/--
The physical and figure-derived data that stay fixed while the candidate pool
depth varies. The raft diameter is dimensionful; refractive indices are
dimensionless material readouts. The four propositions retain the shape,
alignment, opacity, and calm-surface conditions stated in the problem.
-/
structure PoolRaftSetup where
  /-- Figure label `d`, the full diameter of the surface raft. -/
  raftDiameter : LengthQuantity
  /-- Dimensionless refractive index on each side of the water surface. -/
  refractiveIndex : OpticalRegion → ℝ
  raftIsCircular : Prop
  raftIsOpaque : Prop
  waterSurfaceIsCalmAndHorizontal : Prop
  jewelIsDirectlyBelowRaftCenter : Prop

/--
A radial cross-section of a ray emitted by the jewel and reaching the water
surface. Both angles are in radians and measured from the surface normal.
`surfaceRadiusMeters` is the horizontal distance from the raft center to the
emergence point; the azimuth is irrelevant because the raft is circular.
-/
structure JewelSurfaceRay where
  incidenceAngleRadians : ℝ
  refractionAngleRadians : ℝ
  surfaceRadiusMeters : ℝ

/-- Physical incidence/refraction angles, including the limiting grazing ray. -/
def IsAcuteOrCriticalAngle (angleRadians : ℝ) : Prop :=
  angleRadians ∈ Set.Icc 0 (Real.pi / 2)

/-- Snell's law at the horizontal water--air interface. -/
def SatisfiesSnellLaw
    (setup : PoolRaftSetup) (ray : JewelSurfaceRay) : Prop :=
  setup.refractiveIndex .poolWater * Real.sin ray.incidenceAngleRadians =
    setup.refractiveIndex .ambientAir * Real.sin ray.refractionAngleRadians

/--
The right-triangle geometry of a straight ray from a jewel at vertical depth
`h` to its radial point of incidence on the surface.
-/
def SatisfiesJewelRayGeometry
    (depth : LengthQuantity) (ray : JewelSurfaceRay) : Prop :=
  ray.surfaceRadiusMeters =
    valueInMeters depth * Real.tan ray.incidenceAngleRadians

/--
A ray that can emerge from the jewel into the air according to geometrical
optics. This combines angle ranges, Snell's law, and the figure's radial
right-triangle relation, but says nothing about whether the requested depth is
maximal or which numerical answer is correct.
-/
def IsEscapingRayFromJewel
    (setup : PoolRaftSetup)
    (depth : LengthQuantity)
    (ray : JewelSurfaceRay) : Prop :=
  setup.waterSurfaceIsCalmAndHorizontal ∧
    setup.jewelIsDirectlyBelowRaftCenter ∧
    IsAcuteOrCriticalAngle ray.incidenceAngleRadians ∧
    IsAcuteOrCriticalAngle ray.refractionAngleRadians ∧
    0 ≤ ray.surfaceRadiusMeters ∧
    SatisfiesSnellLaw setup ray ∧
    SatisfiesJewelRayGeometry depth ray

/--
For a centered circular opaque raft, an emergent ray is intercepted exactly
when its radial surface point lies no farther out than the raft radius.
-/
def RaftBlocksRay (setup : PoolRaftSetup) (ray : JewelSurfaceRay) : Prop :=
  setup.raftIsCircular ∧
    setup.raftIsOpaque ∧
    ray.surfaceRadiusMeters ≤ valueInMeters setup.raftDiameter / 2

/--
At figure depth `h`, the jewel is unseen from above the water when every ray
that can refract into the air meets the opaque raft. This quantifies over all
external observers implicitly through all possible emergent rays.
-/
def JewelRemainsUnseenAtDepth
    (setup : PoolRaftSetup) (depth : LengthQuantity) : Prop :=
  0 < valueInMeters depth ∧
    ∀ ray : JewelSurfaceRay,
      IsEscapingRayFromJewel setup depth ray → RaftBlocksRay setup ray

/--
The critical incidence angle for water-to-air transmission: the limiting
refracted ray is tangent to the surface, so its refracted sine is one. This is
a governing-law relation, not an assumption about the maximum pool depth.
-/
def SatisfiesWaterAirCriticalAngleLaw
    (setup : PoolRaftSetup) (criticalAngleRadians : ℝ) : Prop :=
  criticalAngleRadians ∈ Set.Ioo 0 (Real.pi / 2) ∧
    setup.refractiveIndex .poolWater * Real.sin criticalAngleRadians =
      setup.refractiveIndex .ambientAir

/-- The four depth choices printed with the problem, in meters. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The scalar meter readout attached to each displayed answer choice. -/
def answerDepthMeters : AnswerChoice → ℝ
  | .A => 3.50
  | .B => 3.00
  | .C => 2.00
  | .D => 2.50

/-- A depth agrees with a two-decimal-place choice to the nearest `0.01 m`. -/
def MatchesAnswerToNearestHundredth
    (depth : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |valueInMeters depth - answerDepthMeters choice| ≤ 0.005

/--
For a centered circular raft of diameter `4.54 m` on calm water, using the
standard geometrical-optics approximation `n_water = 4/3` and `n_air = 1`,
there is a maximum positive figure depth `h` at which every escaping ray from
the jewel is covered by the raft. At the limiting escape-cone ray,
`h * tan(theta_c) = d/2`, and the resulting depth rounds to answer choice C,
`2.00 m`.

This is the formalization of `thm:physics:phyx_mini_0015:target`.
-/
theorem problem_phyx_mini_0015
    (setup : PoolRaftSetup)
    (criticalAngleRadians : ℝ)
    (h_raft_is_circular : setup.raftIsCircular)
    (h_raft_is_opaque : setup.raftIsOpaque)
    (h_surface_is_calm : setup.waterSurfaceIsCalmAndHorizontal)
    (h_jewel_centered : setup.jewelIsDirectlyBelowRaftCenter)
    (h_diameter_positive : 0 < valueInMeters setup.raftDiameter)
    (h_diameter_readout : valueInMeters setup.raftDiameter = 4.54)
    (h_refractive_indices_positive :
      ∀ region, 0 < setup.refractiveIndex region)
    (h_water_refractive_index :
      setup.refractiveIndex .poolWater = 4 / 3)
    (h_air_refractive_index : setup.refractiveIndex .ambientAir = 1)
    (h_critical_angle :
      SatisfiesWaterAirCriticalAngleLaw setup criticalAngleRadians) :
    ∃ maximumDepth : LengthQuantity,
      JewelRemainsUnseenAtDepth setup maximumDepth ∧
      (∀ depth : LengthQuantity,
        JewelRemainsUnseenAtDepth setup depth →
          valueInMeters depth ≤ valueInMeters maximumDepth) ∧
      valueInMeters maximumDepth * Real.tan criticalAngleRadians =
        valueInMeters setup.raftDiameter / 2 ∧
      MatchesAnswerToNearestHundredth maximumDepth .C := by
  rcases h_critical_angle with ⟨h_critical_mem, h_critical_law⟩
  have h_critical_pos : 0 < criticalAngleRadians := h_critical_mem.1
  have h_critical_lt : criticalAngleRadians < Real.pi / 2 :=
    h_critical_mem.2
  have h_tan_pos : 0 < Real.tan criticalAngleRadians :=
    Real.tan_pos_of_pos_of_lt_pi_div_two h_critical_pos h_critical_lt
  have h_sin_critical : Real.sin criticalAngleRadians = (3 : ℝ) / 4 := by
    rw [h_water_refractive_index, h_air_refractive_index] at h_critical_law
    norm_num at h_critical_law ⊢
    linarith
  have h_tan_sq :
      Real.tan criticalAngleRadians ^ 2 = (9 : ℝ) / 7 := by
    have h_cos_sq :
        Real.cos criticalAngleRadians ^ 2 = (7 : ℝ) / 16 := by
      nlinarith [Real.sin_sq_add_cos_sq criticalAngleRadians]
    rw [Real.tan_eq_sin_div_cos, div_pow, h_sin_critical, h_cos_sq]
    norm_num
  let maximumDepth : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨valueInMeters setup.raftDiameter /
          (2 * Real.tan criticalAngleRadians)⟩ : WithDim L𝓭 ℝ)
  have h_maximum_value :
      valueInMeters maximumDepth =
        valueInMeters setup.raftDiameter /
          (2 * Real.tan criticalAngleRadians) := by
    simp [maximumDepth, valueInMeters,
      CarriesDimension.toDimensionful_apply_apply]
  have h_maximum_positive : 0 < valueInMeters maximumDepth := by
    rw [h_maximum_value]
    exact div_pos h_diameter_positive (mul_pos (by norm_num) h_tan_pos)
  have h_boundary :
      valueInMeters maximumDepth * Real.tan criticalAngleRadians =
        valueInMeters setup.raftDiameter / 2 := by
    rw [h_maximum_value]
    field_simp [ne_of_gt h_tan_pos]
  refine ⟨maximumDepth, ?_, ?_, h_boundary, ?_⟩
  · refine ⟨h_maximum_positive, ?_⟩
    intro ray h_ray
    rcases h_ray with
      ⟨_, _, h_incidence_mem, _, _, h_snell, h_geometry⟩
    rcases h_incidence_mem with ⟨h_incidence_nonneg, h_incidence_le⟩
    have h_sin_incidence_le :
        Real.sin ray.incidenceAngleRadians ≤
          Real.sin criticalAngleRadians := by
      norm_num [SatisfiesSnellLaw, h_water_refractive_index,
        h_air_refractive_index] at h_snell
      rw [h_sin_critical]
      nlinarith [Real.sin_le_one ray.refractionAngleRadians]
    have h_incidence_le_critical :
        ray.incidenceAngleRadians ≤ criticalAngleRadians := by
      exact
        (Real.strictMonoOn_sin.le_iff_le
          ⟨by linarith [Real.pi_pos], h_incidence_le⟩
          ⟨by linarith [Real.pi_pos], le_of_lt h_critical_lt⟩).mp
          h_sin_incidence_le
    have h_tan_incidence_le :
        Real.tan ray.incidenceAngleRadians ≤
          Real.tan criticalAngleRadians := by
      exact Real.strictMonoOn_tan.monotoneOn
        ⟨by linarith [Real.pi_pos],
          lt_of_le_of_lt h_incidence_le_critical h_critical_lt⟩
        ⟨by linarith [Real.pi_pos], h_critical_lt⟩
        h_incidence_le_critical
    refine ⟨h_raft_is_circular, h_raft_is_opaque, ?_⟩
    rw [h_geometry]
    calc
      valueInMeters maximumDepth *
            Real.tan ray.incidenceAngleRadians ≤
          valueInMeters maximumDepth *
            Real.tan criticalAngleRadians :=
        mul_le_mul_of_nonneg_left h_tan_incidence_le
          h_maximum_positive.le
      _ = valueInMeters setup.raftDiameter / 2 := h_boundary
  · intro depth h_unseen
    rcases h_unseen with ⟨h_depth_positive, h_all_rays_blocked⟩
    let criticalRay : JewelSurfaceRay :=
      { incidenceAngleRadians := criticalAngleRadians
        refractionAngleRadians := Real.pi / 2
        surfaceRadiusMeters :=
          valueInMeters depth * Real.tan criticalAngleRadians }
    have h_critical_ray_escapes :
        IsEscapingRayFromJewel setup depth criticalRay := by
      refine ⟨h_surface_is_calm, h_jewel_centered, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨h_critical_pos.le, h_critical_lt.le⟩
      · exact ⟨by positivity, le_rfl⟩
      · exact mul_nonneg h_depth_positive.le h_tan_pos.le
      · simpa [SatisfiesSnellLaw, criticalRay] using h_critical_law
      · simp [SatisfiesJewelRayGeometry, criticalRay]
    have h_critical_ray_blocked :=
      h_all_rays_blocked criticalRay h_critical_ray_escapes
    have h_depth_times_tan_le :
        valueInMeters depth * Real.tan criticalAngleRadians ≤
          valueInMeters setup.raftDiameter / 2 := by
      exact h_critical_ray_blocked.2.2
    exact le_of_mul_le_mul_right (by
      calc
        valueInMeters depth * Real.tan criticalAngleRadians ≤
            valueInMeters setup.raftDiameter / 2 := h_depth_times_tan_le
        _ = valueInMeters maximumDepth *
            Real.tan criticalAngleRadians := h_boundary.symm) h_tan_pos
  · have h_maximum_times_tan :
        valueInMeters maximumDepth * Real.tan criticalAngleRadians =
          2.27 := by
      rw [h_boundary, h_diameter_readout]
      norm_num
    have h_maximum_sq :
        valueInMeters maximumDepth ^ 2 = (360703 : ℝ) / 90000 := by
      have h_squared :=
        congrArg (fun x : ℝ => x ^ 2) h_maximum_times_tan
      rw [mul_pow, h_tan_sq] at h_squared
      norm_num at h_squared ⊢
      nlinarith
    change |valueInMeters maximumDepth - 2.00| ≤ 0.005
    rw [abs_le]
    constructor <;> norm_num <;>
      nlinarith [sq_nonneg (valueInMeters maximumDepth - 2),
        sq_nonneg (valueInMeters maximumDepth + 2)]

end PhyXMiniProblems.ProblemPhyXMini0015
