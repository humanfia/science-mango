import Physlib.Units.WithDim.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0021

/-!
# Total internal reflection in a parallel four-layer stack

The figure contains four horizontal optical layers with successively smaller
dimensionless refractive indices `1.60`, `1.40`, `1.20`, and `1.00`. Physlib's
`WithDim` tags each index measurement with the dimensionless physical
dimension `(1 : Dimension)`, while `refractiveIndexReadout` is its real scalar
projection. Every angle below is a real-valued radian readout measured from
the dashed normal to the relevant interface.

Strict total internal reflection has no least incident angle: it begins just
above the critical angle. Accordingly, the question's “minimum” is modeled as
the greatest lower bound of the incident angles that cause strict total
internal reflection.
-/

/-- The four physical media, ordered from the top of the figure downward. -/
inductive OpticalLayer where
  | index160
  | index140
  | index120
  | index100
  deriving DecidableEq, Repr

/--
The material and geometry data of the slab stack. `refractiveIndex` is a
dimensionless measurement for each physical layer. Parallel horizontal
interfaces give all three dashed normals in the figure a common direction.
-/
structure ParallelLayerStack where
  refractiveIndex : OpticalLayer → WithDim (1 : Dimension) ℝ
  refractiveIndex_pos : ∀ layer, 0 < (refractiveIndex layer).val
  interfacesAreParallelAndHorizontal : Prop

/-- The real, dimensionless scalar projection of a layer's refractive index. -/
def refractiveIndexReadout
    (setup : ParallelLayerStack) (layer : OpticalLayer) : ℝ :=
  (setup.refractiveIndex layer).val

/--
The part of a ray that reaches the final `1.20`--`1.00` interface through the
three upper layers. `thetaOneRadians` is the figure label `θ₁`.
-/
structure UpperStackRay where
  thetaOneRadians : ℝ
  angleInIndex140Radians : ℝ
  angleInIndex120Radians : ℝ

/--
A possible continuation into the bottom `n = 1.00` medium. Its angle is the
figure label `θ₂`. Under strict total internal reflection no physically
admissible extension of this kind satisfies Snell's law.
-/
structure TransmittedExtension where
  thetaTwoRadians : ℝ

/-- Convert a scalar radian angle readout to degrees. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- A normal-relative angle on the physical incident/transmitted branch. -/
def IsPhysicalRayAngle (angleRadians : ℝ) : Prop :=
  angleRadians ∈ Set.Icc 0 (Real.pi / 2)

/-- All three angles of a ray reaching the final interface are physical. -/
def HasPhysicalUpperAngles (ray : UpperStackRay) : Prop :=
  IsPhysicalRayAngle ray.thetaOneRadians ∧
    IsPhysicalRayAngle ray.angleInIndex140Radians ∧
    IsPhysicalRayAngle ray.angleInIndex120Radians

/--
Snell's law at the first two interfaces. Since the interfaces are parallel,
the refracted angle at one face is the incidence angle at the next face.
-/
def SatisfiesUpperInterfaceSnellLaws
    (setup : ParallelLayerStack) (ray : UpperStackRay) : Prop :=
  refractiveIndexReadout setup .index160 * Real.sin ray.thetaOneRadians =
      refractiveIndexReadout setup .index140 *
        Real.sin ray.angleInIndex140Radians ∧
    refractiveIndexReadout setup .index140 *
        Real.sin ray.angleInIndex140Radians =
      refractiveIndexReadout setup .index120 *
        Real.sin ray.angleInIndex120Radians

/-- Snell's law for a proposed transmitted ray at the final interface. -/
def SatisfiesFinalInterfaceSnellLaw
    (setup : ParallelLayerStack)
    (ray : UpperStackRay)
    (extension : TransmittedExtension) : Prop :=
  refractiveIndexReadout setup .index120 *
      Real.sin ray.angleInIndex120Radians =
    refractiveIndexReadout setup .index100 *
      Real.sin extension.thetaTwoRadians

/-
Strict total internal reflection at the `1.20`--`1.00` interface: no
transmitted angle on the physical branch can obey Snell's law.
-/
def HasTotalInternalReflectionAtFinalInterface
    (setup : ParallelLayerStack) (ray : UpperStackRay) : Prop :=
  ¬ ∃ extension : TransmittedExtension,
      IsPhysicalRayAngle extension.thetaTwoRadians ∧
        SatisfiesFinalInterfaceSnellLaw setup ray extension

/-
The set of top-layer incident angles `θ₁` whose rays traverse the first two
interfaces and then undergo strict total internal reflection at the last one.
This definition contains only geometry, physical angle ranges, and Snell's
law; it does not contain the requested critical-angle formula.
-/
def IncidentAnglesProducingFinalTIR
    (setup : ParallelLayerStack) : Set ℝ :=
  {thetaOneRadians | ∃ ray : UpperStackRay,
    ray.thetaOneRadians = thetaOneRadians ∧
      setup.interfacesAreParallelAndHorizontal ∧
      HasPhysicalUpperAngles ray ∧
      SatisfiesUpperInterfaceSnellLaws setup ray ∧
      HasTotalInternalReflectionAtFinalInterface setup ray}

/-- Exact material and geometry readouts shown in the four-layer figure. -/
structure MatchesProblemFigure (setup : ParallelLayerStack) : Prop where
  interfaces : setup.interfacesAreParallelAndHorizontal
  topIndex : refractiveIndexReadout setup .index160 = 1.60
  secondIndex : refractiveIndexReadout setup .index140 = 1.40
  thirdIndex : refractiveIndexReadout setup .index120 = 1.20
  bottomIndex : refractiveIndexReadout setup .index100 = 1.00

/-- The four multiple-choice labels printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The degree readout displayed beside each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 30.6
  | .B => 26.2
  | .C => 38.7
  | .D => 36.1

/-- Agreement with a one-decimal-place answer to the nearest tenth degree. -/
def MatchesAnswerToNearestTenth
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |radiansToDegrees angleRadians - answerAngleDegrees choice| ≤ 0.05

/-
The two upper Snell equations imply conservation of `n * sin θ` from the top
`1.60` layer to the `1.20` layer incident on the final interface.
-/
lemma upper_stack_snell_invariant
    (setup : ParallelLayerStack)
    (ray : UpperStackRay)
    (hSnell : SatisfiesUpperInterfaceSnellLaws setup ray) :
    refractiveIndexReadout setup .index160 * Real.sin ray.thetaOneRadians =
      refractiveIndexReadout setup .index120 *
        Real.sin ray.angleInIndex120Radians := by
  exact hSnell.1.trans hSnell.2

/-
For the pictured parallel stack, the greatest lower bound of incident angles
that produce strict total internal reflection at the `1.20`--`1.00` boundary
is `arcsin (1.00 / 1.60) = arcsin (5/8)`. In degrees it rounds to `38.7°`,
answer choice C.

This is the formalization of `thm:physics:phyx_mini_0021:target`.
-/
theorem problem_phyx_mini_0021
    (setup : ParallelLayerStack)
    (figure : MatchesProblemFigure setup) :
    ∃ thresholdIncidentAngleRadians : ℝ,
      IsGLB
          (IncidentAnglesProducingFinalTIR setup)
          thresholdIncidentAngleRadians ∧
        thresholdIncidentAngleRadians = Real.arcsin ((5 : ℝ) / 8) ∧
        MatchesAnswerToNearestTenth thresholdIncidentAngleRadians .C := by
  have hmem_iff (θ : ℝ) :
      θ ∈ IncidentAnglesProducingFinalTIR setup ↔
        IsPhysicalRayAngle θ ∧
          (5 : ℝ) / 8 < Real.sin θ ∧ Real.sin θ ≤ (3 : ℝ) / 4 := by
    constructor
    · rintro ⟨ray, rfl, _hParallel, hPhysical, hSnell, hTIR⟩
      simp only [HasPhysicalUpperAngles, IsPhysicalRayAngle, Set.mem_Icc] at hPhysical
      have hInvariant := upper_stack_snell_invariant setup ray hSnell
      rw [figure.topIndex, figure.thirdIndex] at hInvariant
      have hzero_mem :
          (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have hthird_mem :
          ray.angleInIndex120Radians ∈
            Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        exact ⟨by linarith [hPhysical.2.2.1],
          by linarith [hPhysical.2.2.2]⟩
      have hsin_third_nonneg :
          0 ≤ Real.sin ray.angleInIndex120Radians := by
        simpa using
          Real.monotoneOn_sin hzero_mem hthird_mem hPhysical.2.2.1
      have hsin_top_le : Real.sin ray.thetaOneRadians ≤ (3 : ℝ) / 4 := by
        have hsin_third_le := Real.sin_le_one ray.angleInIndex120Radians
        norm_num at hInvariant
        nlinarith
      have hsin_top_gt : (5 : ℝ) / 8 < Real.sin ray.thetaOneRadians := by
        by_contra hnot
        have hsin_top_le_critical :
            Real.sin ray.thetaOneRadians ≤ (5 : ℝ) / 8 :=
          le_of_not_gt hnot
        have htransmitted_nonneg :
            0 ≤ (6 : ℝ) / 5 * Real.sin ray.angleInIndex120Radians := by
          positivity
        have htransmitted_le :
            (6 : ℝ) / 5 * Real.sin ray.angleInIndex120Radians ≤ 1 := by
          norm_num at hInvariant
          nlinarith
        apply hTIR
        refine
          ⟨⟨Real.arcsin
              ((6 : ℝ) / 5 * Real.sin ray.angleInIndex120Radians)⟩,
            ?_, ?_⟩
        · exact
            ⟨Real.arcsin_nonneg.2 htransmitted_nonneg,
              Real.arcsin_le_pi_div_two _⟩
        · unfold SatisfiesFinalInterfaceSnellLaw
          rw [figure.thirdIndex, figure.bottomIndex]
          rw [Real.sin_arcsin (by linarith) htransmitted_le]
          norm_num
      exact ⟨hPhysical.1, hsin_top_gt, hsin_top_le⟩
    · rintro ⟨hPhysical, hsin_top_gt, hsin_top_le⟩
      simp only [IsPhysicalRayAngle, Set.mem_Icc] at hPhysical
      have htop_mem :
          θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        exact ⟨by linarith [hPhysical.1], by linarith [hPhysical.2]⟩
      have hzero_mem :
          (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have hsin_top_nonneg : 0 ≤ Real.sin θ := by
        simpa using Real.monotoneOn_sin hzero_mem htop_mem hPhysical.1
      have harg140_nonneg : 0 ≤ (8 : ℝ) / 7 * Real.sin θ := by
        positivity
      have harg140_le : (8 : ℝ) / 7 * Real.sin θ ≤ 1 := by
        nlinarith
      have harg120_nonneg : 0 ≤ (4 : ℝ) / 3 * Real.sin θ := by
        positivity
      have harg120_le : (4 : ℝ) / 3 * Real.sin θ ≤ 1 := by
        nlinarith
      let ray : UpperStackRay :=
        { thetaOneRadians := θ
          angleInIndex140Radians :=
            Real.arcsin ((8 : ℝ) / 7 * Real.sin θ)
          angleInIndex120Radians :=
            Real.arcsin ((4 : ℝ) / 3 * Real.sin θ) }
      refine ⟨ray, rfl, figure.interfaces, ?_, ?_, ?_⟩
      · exact
          ⟨hPhysical,
            ⟨Real.arcsin_nonneg.2 harg140_nonneg,
              Real.arcsin_le_pi_div_two _⟩,
            ⟨Real.arcsin_nonneg.2 harg120_nonneg,
              Real.arcsin_le_pi_div_two _⟩⟩
      · unfold SatisfiesUpperInterfaceSnellLaws
        rw [figure.topIndex, figure.secondIndex, figure.thirdIndex]
        change
          (1.60 : ℝ) * Real.sin θ =
              (1.40 : ℝ) *
                Real.sin
                  (Real.arcsin ((8 : ℝ) / 7 * Real.sin θ)) ∧
            (1.40 : ℝ) *
                Real.sin
                  (Real.arcsin ((8 : ℝ) / 7 * Real.sin θ)) =
              (1.20 : ℝ) *
                Real.sin
                  (Real.arcsin ((4 : ℝ) / 3 * Real.sin θ))
        rw [Real.sin_arcsin (by linarith) harg140_le,
          Real.sin_arcsin (by linarith) harg120_le]
        constructor <;> ring
      · unfold HasTotalInternalReflectionAtFinalInterface
        rintro ⟨extension, hExtensionPhysical, hFinalSnell⟩
        unfold SatisfiesFinalInterfaceSnellLaw at hFinalSnell
        rw [figure.thirdIndex, figure.bottomIndex] at hFinalSnell
        change
          (1.20 : ℝ) *
              Real.sin
                (Real.arcsin ((4 : ℝ) / 3 * Real.sin θ)) =
            (1.00 : ℝ) * Real.sin extension.thetaTwoRadians at hFinalSnell
        rw [Real.sin_arcsin (by linarith) harg120_le] at hFinalSnell
        have hsin_extension_le :=
          Real.sin_le_one extension.thetaTwoRadians
        norm_num at hFinalSnell
        nlinarith
  let critical : ℝ := Real.arcsin ((5 : ℝ) / 8)
  let upperEndpoint : ℝ := Real.arcsin ((3 : ℝ) / 4)
  have hcritical_nonneg : 0 ≤ critical := by
    exact Real.arcsin_nonneg.2 (by norm_num)
  have hcritical_le : critical ≤ Real.pi / 2 :=
    Real.arcsin_le_pi_div_two _
  have hupper_le : upperEndpoint ≤ Real.pi / 2 :=
    Real.arcsin_le_pi_div_two _
  have hcritical_lt_upper : critical < upperEndpoint := by
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hcritical_mem :
      critical ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact ⟨by linarith, hcritical_le⟩
  have hupper_mem :
      upperEndpoint ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact ⟨by
      have : 0 ≤ upperEndpoint :=
        Real.arcsin_nonneg.2 (by norm_num)
      linarith [Real.pi_pos], hupper_le⟩
  refine ⟨critical, ?_, rfl, ?_⟩
  · constructor
    · intro θ hθ
      have hθ_data := (hmem_iff θ).1 hθ
      have hθ_mem :
          θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        exact ⟨by linarith [hθ_data.1.1],
          by linarith [hθ_data.1.2]⟩
      have hsin_critical :
          Real.sin critical = (5 : ℝ) / 8 := by
        exact Real.sin_arcsin (by norm_num) (by norm_num)
      have : critical < θ := by
        rw [← Real.strictMonoOn_sin.lt_iff_lt hcritical_mem hθ_mem]
        rw [hsin_critical]
        exact hθ_data.2.1
      exact this.le
    · intro lower hlower
      by_contra hnot
      have hcritical_lt_lower : critical < lower := lt_of_not_ge hnot
      let θ : ℝ := (critical + min lower upperEndpoint) / 2
      have hcritical_lt_min :
          critical < min lower upperEndpoint :=
        lt_min hcritical_lt_lower hcritical_lt_upper
      have hcritical_lt_theta : critical < θ := by
        dsimp [θ]
        linarith
      have htheta_lt_lower : θ < lower := by
        have hmin_le_lower : min lower upperEndpoint ≤ lower :=
          min_le_left _ _
        dsimp [θ]
        linarith
      have htheta_le_upper : θ ≤ upperEndpoint := by
        have hmin_le_upper : min lower upperEndpoint ≤ upperEndpoint :=
          min_le_right _ _
        dsimp [θ]
        linarith
      have htheta_nonneg : 0 ≤ θ := hcritical_nonneg.trans hcritical_lt_theta.le
      have htheta_le_pi_div_two : θ ≤ Real.pi / 2 :=
        htheta_le_upper.trans hupper_le
      have htheta_mem :
          θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        exact ⟨by linarith [Real.pi_pos], htheta_le_pi_div_two⟩
      have hsin_critical :
          Real.sin critical = (5 : ℝ) / 8 := by
        exact Real.sin_arcsin (by norm_num) (by norm_num)
      have hsin_upper :
          Real.sin upperEndpoint = (3 : ℝ) / 4 := by
        exact Real.sin_arcsin (by norm_num) (by norm_num)
      have hsin_theta_gt : (5 : ℝ) / 8 < Real.sin θ := by
        rw [← hsin_critical]
        exact
          Real.strictMonoOn_sin hcritical_mem htheta_mem
            hcritical_lt_theta
      have hsin_theta_le : Real.sin θ ≤ (3 : ℝ) / 4 := by
        rw [← hsin_upper]
        exact
          Real.monotoneOn_sin htheta_mem hupper_mem htheta_le_upper
      have hθ_set : θ ∈ IncidentAnglesProducingFinalTIR setup :=
        (hmem_iff θ).2
          ⟨⟨htheta_nonneg, htheta_le_pi_div_two⟩,
            hsin_theta_gt, hsin_theta_le⟩
      exact (not_le_of_gt htheta_lt_lower) (hlower hθ_set)
  · have cos_double_bounds (x l u l' u' : ℝ)
        (hl : 0 ≤ l) (hnextl : l' ≤ 2 * l ^ 2 - 1)
        (hnextu : 2 * u ^ 2 - 1 ≤ u')
        (hlower : l ≤ Real.cos x) (hupper : Real.cos x ≤ u) :
        l' ≤ Real.cos (2 * x) ∧ Real.cos (2 * x) ≤ u' := by
      rw [Real.cos_two_mul]
      constructor
      · have hprod : 0 ≤ (Real.cos x - l) * (Real.cos x + l) :=
          mul_nonneg (sub_nonneg.mpr hlower) (by linarith)
        nlinarith
      · have hprod : 0 ≤ (u - Real.cos x) * (u + Real.cos x) :=
          mul_nonneg (sub_nonneg.mpr hupper) (by nlinarith)
        nlinarith
    have hpi_lower : (3141 : ℝ) / 1000 < Real.pi := by
      let y : ℝ := (3141 : ℝ) / 2000 / 64
      have hbound := Real.cos_bound (x := y) (by
        dsimp [y]
        norm_num)
      have habs := abs_le.mp hbound
      have h0l :
          (99969889832021 : ℝ) / 100000000000000 ≤ Real.cos y := by
        dsimp [y] at habs ⊢
        norm_num at habs ⊢
        linarith
      have h0u :
          Real.cos y ≤ (99969893609141 : ℝ) / 100000000000000 := by
        dsimp [y] at habs ⊢
        norm_num at habs ⊢
        linarith
      obtain ⟨h1l, h1u⟩ := cos_double_bounds y
        ((99969889832021 : ℝ) / 100000000000000)
        ((99969893609141 : ℝ) / 100000000000000)
        ((99879577460528 : ℝ) / 100000000000000)
        ((99879592564460 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h0l h0u
      obtain ⟨h2l, h2u⟩ := cos_double_bounds (2 * y)
        ((99879577460528 : ℝ) / 100000000000000)
        ((99879592564460 : ℝ) / 100000000000000)
        ((99518599873872 : ℝ) / 100000000000000)
        ((99518660216851 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h1l h1u
      obtain ⟨h3l, h3u⟩ := cos_double_bounds (2 * (2 * y))
        ((99518599873872 : ℝ) / 100000000000000)
        ((99518660216851 : ℝ) / 100000000000000)
        ((98079034417116 : ℝ) / 100000000000000)
        ((98079274627141 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h2l h2u
      obtain ⟨h4l, h4u⟩ := cos_double_bounds (2 * (2 * (2 * y)))
        ((98079034417116 : ℝ) / 100000000000000)
        ((98079274627141 : ℝ) / 100000000000000)
        ((92389939843876 : ℝ) / 100000000000000)
        ((92390882227723 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h3l h3u
      obtain ⟨h5l, h5u⟩ := cos_double_bounds (2 * (2 * (2 * (2 * y))))
        ((92389939843876 : ℝ) / 100000000000000)
        ((92390882227723 : ℝ) / 100000000000000)
        ((70718019687100 : ℝ) / 100000000000000)
        ((70721502376340 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h4l h4u
      obtain ⟨h6l, _h6u⟩ :=
        cos_double_bounds (2 * (2 * (2 * (2 * (2 * y)))))
          ((70718019687100 : ℝ) / 100000000000000)
          ((70721502376340 : ℝ) / 100000000000000)
          ((20766169301 : ℝ) / 100000000000000)
          ((30617967334 : ℝ) / 100000000000000)
          (by norm_num) (by norm_num) (by norm_num) h5l h5u
      have hcos_pos : 0 < Real.cos ((3141 : ℝ) / 2000) := by
        dsimp [y] at h6l
        norm_num at h6l ⊢
        linarith
      by_contra hnot
      have hpi_le : Real.pi ≤ (3141 : ℝ) / 1000 :=
        le_of_not_gt hnot
      have hcos_nonpos :
          Real.cos ((3141 : ℝ) / 2000) ≤ 0 := by
        apply Real.cos_nonpos_of_pi_div_two_le_of_le
        · linarith
        · linarith [Real.two_le_pi]
      linarith
    have hpi_upper : Real.pi < (3142 : ℝ) / 1000 := by
      let y : ℝ := (3142 : ℝ) / 2000 / 64
      have hbound := Real.cos_bound (x := y) (by
        dsimp [y]
        norm_num)
      have habs := abs_le.mp hbound
      have h0l :
          (99969870655421 : ℝ) / 100000000000000 ≤ Real.cos y := by
        dsimp [y] at habs ⊢
        norm_num at habs ⊢
        linarith
      have h0u :
          Real.cos y ≤ (99969874437353 : ℝ) / 100000000000000 := by
        dsimp [y] at habs ⊢
        norm_num at habs ⊢
        linarith
      obtain ⟨h1l, h1u⟩ := cos_double_bounds y
        ((99969870655421 : ℝ) / 100000000000000)
        ((99969874437353 : ℝ) / 100000000000000)
        ((99879500777232 : ℝ) / 100000000000000)
        ((99879515900403 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h0l h0u
      obtain ⟨h2l, h2u⟩ := cos_double_bounds (2 * y)
        ((99879500777232 : ℝ) / 100000000000000)
        ((99879515900403 : ℝ) / 100000000000000)
        ((99518293510181 : ℝ) / 100000000000000)
        ((99518353929978 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h1l h1u
      obtain ⟨h3l, h3u⟩ := cos_double_bounds (2 * (2 * y))
        ((99518293510181 : ℝ) / 100000000000000)
        ((99518353929978 : ℝ) / 100000000000000)
        ((98077814863570 : ℝ) / 100000000000000)
        ((98078055378648 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h2l h2u
      obtain ⟨h4l, h4u⟩ := cos_double_bounds (2 * (2 * (2 * y)))
        ((98077814863570 : ℝ) / 100000000000000)
        ((98078055378648 : ℝ) / 100000000000000)
        ((92385155368254 : ℝ) / 100000000000000)
        ((92386098937143 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h3l h3u
      obtain ⟨h5l, h5u⟩ := cos_double_bounds (2 * (2 * (2 * (2 * y))))
        ((92385155368254 : ℝ) / 100000000000000)
        ((92386098937143 : ℝ) / 100000000000000)
        ((70700338648328 : ℝ) / 100000000000000)
        ((70703825536472 : ℝ) / 100000000000000)
        (by norm_num) (by norm_num) (by norm_num) h4l h4u
      obtain ⟨_h6l, h6u⟩ :=
        cos_double_bounds (2 * (2 * (2 * (2 * (2 * y)))))
          ((70700338648328 : ℝ) / 100000000000000)
          ((70703825536472 : ℝ) / 100000000000000)
          ((-29242300235 : ℝ) / 100000000000000)
          ((-19381090162 : ℝ) / 100000000000000)
          (by norm_num) (by norm_num) (by norm_num) h5l h5u
      have hcos_neg : Real.cos ((3142 : ℝ) / 2000) < 0 := by
        dsimp [y] at h6u
        norm_num at h6u ⊢
        linarith
      by_contra hnot
      have hpi_ge : (3142 : ℝ) / 1000 ≤ Real.pi :=
        le_of_not_gt hnot
      have hcos_nonneg :
          0 ≤ Real.cos ((3142 : ℝ) / 2000) := by
        apply Real.cos_nonneg_of_mem_Icc
        constructor
        · linarith [Real.pi_pos]
        · linarith
      linarith
    have hsin_lower_endpoint :
        Real.sin ((773 : ℝ) * Real.pi / 3600) < (5 : ℝ) / 8 := by
      let δ : ℝ := (173 : ℝ) * Real.pi / 3600
      let r : ℝ := (60377 : ℝ) / 400000
      let q : ℝ := (271783 : ℝ) / 1800000
      have hr_le_delta : r ≤ δ := by
        dsimp [r, δ]
        nlinarith only [hpi_lower]
      have hdelta_le_q : δ ≤ q := by
        dsimp [δ, q]
        nlinarith only [hpi_upper]
      have hdelta_mem :
          δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [δ]
        constructor <;> nlinarith only [Real.pi_pos]
      have hq_mem :
          q ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [q]
        constructor
        · nlinarith only [Real.pi_pos]
        · nlinarith only [Real.two_le_pi]
      have hsin_delta_le : Real.sin δ ≤ Real.sin q :=
        Real.monotoneOn_sin hdelta_mem hq_mem hdelta_le_q
      have hcos_delta_le : Real.cos δ ≤ Real.cos r := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        · dsimp [r]
          norm_num
        · dsimp [δ]
          nlinarith only [Real.pi_pos]
        · exact hr_le_delta
      have hsin_q_bound := abs_le.mp
        (Real.sin_bound (x := q) (by
          dsimp [q]
          norm_num))
      have hcos_r_bound := abs_le.mp
        (Real.cos_bound (x := r) (by
          dsimp [r]
          norm_num))
      have hsin_q_upper :
          Real.sin q ≤ (150443909 : ℝ) / 1000000000 := by
        dsimp [q] at hsin_q_bound ⊢
        norm_num at hsin_q_bound ⊢
        linarith
      have hcos_r_upper :
          Real.cos r ≤ (988635218 : ℝ) / 1000000000 := by
        dsimp [r] at hcos_r_bound ⊢
        norm_num at hcos_r_bound ⊢
        linarith
      have hsqrt_upper : Real.sqrt 3 ≤ (1733 : ℝ) / 1000 := by
        exact ((Real.sqrt_lt (by norm_num) (by norm_num)).2
          (by norm_num)).le
      have hsin_delta_nonneg : 0 ≤ Real.sin δ := by
        have hzero_mem :
            (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith only [Real.pi_pos]
        simpa using Real.monotoneOn_sin hzero_mem hdelta_mem (by
          dsimp [δ]
          positivity)
      have hproduct :
          Real.sqrt 3 * Real.sin δ ≤
            ((1733 : ℝ) / 1000) *
              ((150443909 : ℝ) / 1000000000) :=
        mul_le_mul hsqrt_upper
          (hsin_delta_le.trans hsin_q_upper)
          hsin_delta_nonneg (by norm_num)
      rw [show
        (773 : ℝ) * Real.pi / 3600 = Real.pi / 6 + δ by
          dsimp [δ]
          ring,
        Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
      nlinarith
    have hsin_upper_endpoint :
        (5 : ℝ) / 8 < Real.sin ((31 : ℝ) * Real.pi / 144) := by
      let δ : ℝ := (7 : ℝ) * Real.pi / 144
      let r : ℝ := (2443 : ℝ) / 16000
      let q : ℝ := (10997 : ℝ) / 72000
      have hr_le_delta : r ≤ δ := by
        dsimp [r, δ]
        nlinarith only [hpi_lower]
      have hdelta_le_q : δ ≤ q := by
        dsimp [δ, q]
        nlinarith only [hpi_upper]
      have hr_mem :
          r ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [r]
        constructor
        · nlinarith only [Real.pi_pos]
        · nlinarith only [Real.two_le_pi]
      have hdelta_mem :
          δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [δ]
        constructor <;> nlinarith only [Real.pi_pos]
      have hsin_r_le : Real.sin r ≤ Real.sin δ :=
        Real.monotoneOn_sin hr_mem hdelta_mem hr_le_delta
      have hcos_q_le : Real.cos q ≤ Real.cos δ := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        · dsimp [δ]
          positivity
        · dsimp [q]
          nlinarith only [Real.two_le_pi]
        · exact hdelta_le_q
      have hsin_r_bound := abs_le.mp
        (Real.sin_bound (x := r) (by
          dsimp [r]
          norm_num))
      have hcos_q_bound := abs_le.mp
        (Real.cos_bound (x := q) (by
          dsimp [q]
          norm_num))
      have hsin_r_lower :
          (152065912 : ℝ) / 1000000000 ≤ Real.sin r := by
        dsimp [r] at hsin_r_bound ⊢
        norm_num at hsin_r_bound ⊢
        linarith
      have hcos_q_lower :
          (988307495 : ℝ) / 1000000000 ≤ Real.cos q := by
        dsimp [q] at hcos_q_bound ⊢
        norm_num at hcos_q_bound ⊢
        linarith
      have hsqrt_lower : (1732 : ℝ) / 1000 ≤ Real.sqrt 3 := by
        exact ((Real.lt_sqrt (by norm_num)).2 (by norm_num)).le
      have hproduct :
          ((1732 : ℝ) / 1000) *
              ((152065912 : ℝ) / 1000000000) ≤
            Real.sqrt 3 * Real.sin δ :=
        mul_le_mul hsqrt_lower
          (hsin_r_lower.trans hsin_r_le)
          (by norm_num) (Real.sqrt_nonneg _)
      rw [show
        (31 : ℝ) * Real.pi / 144 = Real.pi / 6 + δ by
          dsimp [δ]
          ring,
        Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
      nlinarith
    have hsin_critical :
        Real.sin critical = (5 : ℝ) / 8 := by
      exact Real.sin_arcsin (by norm_num) (by norm_num)
    have hlower_angle_mem :
        (773 : ℝ) * Real.pi / 3600 ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
    have hupper_angle_mem :
        (31 : ℝ) * Real.pi / 144 ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
    have hlower_angle_lt :
        (773 : ℝ) * Real.pi / 3600 < critical := by
      rw [← Real.strictMonoOn_sin.lt_iff_lt hlower_angle_mem hcritical_mem]
      rw [hsin_critical]
      exact hsin_lower_endpoint
    have hcritical_lt_upper_angle :
        critical < (31 : ℝ) * Real.pi / 144 := by
      rw [← Real.strictMonoOn_sin.lt_iff_lt hcritical_mem hupper_angle_mem]
      rw [hsin_critical]
      exact hsin_upper_endpoint
    have hdegree_lower :
        (773 : ℝ) / 20 < radiansToDegrees critical := by
      unfold radiansToDegrees
      apply (lt_div_iff₀ Real.pi_pos).2
      nlinarith
    have hdegree_upper :
        radiansToDegrees critical < (155 : ℝ) / 4 := by
      unfold radiansToDegrees
      apply (div_lt_iff₀ Real.pi_pos).2
      nlinarith
    unfold MatchesAnswerToNearestTenth
    change |radiansToDegrees critical - (38.7 : ℝ)| ≤ (0.05 : ℝ)
    rw [abs_le]
    constructor <;> norm_num at hdegree_lower hdegree_upper ⊢ <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0021
