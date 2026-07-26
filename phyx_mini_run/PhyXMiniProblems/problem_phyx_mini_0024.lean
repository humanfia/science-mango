import Physlib.SpaceAndTime.Space.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0024

/--
Positions in the top-view plane of the enclosure.  `Space 2` is PhysLean's
flat physical space with coordinates in an arbitrary, but fixed, length unit.
-/
abbrev OpticalPoint := Space 2

/-- Displacement and ray-direction vectors in the top-view plane. -/
abbrev OpticalVector := EuclideanSpace ℝ (Fin 2)

/--
The direction subspace tangent to either horizontal mirror of the square.
Reflection of a ray direction in this subspace is specular reflection at a
horizontal mirror.
-/
def horizontalMirrorTangent : Submodule ℝ OpticalVector where
  carrier := {v | v 1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a 1 = 0 at ha
    change b 1 = 0 at hb
    change a 1 + b 1 = 0
    rw [ha, hb]
    simp
  smul_mem' := by
    intro c a ha
    change a 1 = 0 at ha
    change c * a 1 = 0
    rw [ha]
    simp

/--
The direction subspace tangent to either vertical mirror of the square.
Reflection of a ray direction in this subspace is specular reflection at a
vertical mirror.
-/
def verticalMirrorTangent : Submodule ℝ OpticalVector where
  carrier := {v | v 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a 0 = 0 at ha
    change b 0 = 0 at hb
    change a 0 + b 0 = 0
    rw [ha, hb]
    simp
  smul_mem' := by
    intro c a ha
    change a 0 = 0 at ha
    change c * a 0 = 0
    rw [ha]
    simp

/-- The unit travel direction of a nondegenerate straight ray segment. -/
def unitDirection (start finish : OpticalPoint) : OpticalVector :=
  (‖finish -ᵥ start‖)⁻¹ • (finish -ᵥ start)

/--
The law of specular reflection at a plane mirror: the outgoing unit direction
is the reflection of the incoming unit direction in the mirror's tangent
subspace.  The inequalities exclude degenerate incoming and outgoing legs.
-/
def SpecularReflectionAt
    (mirrorTangent : Submodule ℝ OpticalVector) [CompleteSpace mirrorTangent]
    (previous hit next : OpticalPoint) : Prop :=
  previous ≠ hit ∧ hit ≠ next ∧
    mirrorTangent.reflection (unitDirection previous hit) =
      unitDirection hit next

/--
A point lies strictly inside the square enclosure.  `sideLength` is its
positive coordinate readout in the fixed length unit carried by `Space 2`.
-/
def InOpenSquare (sideLength : ℝ) (p : OpticalPoint) : Prop :=
  0 < p 0 ∧ p 0 < sideLength ∧ 0 < p 1 ∧ p 1 < sideLength

/--
Except for its endpoints, a ray leg stays inside the enclosure.  Thus no
unlisted mirror is struck between the two consecutive labelled contacts.
-/
def OpenSegmentInside
    (sideLength : ℝ) (start finish : OpticalPoint) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 →
    InOpenSquare sideLength ((t • (finish -ᵥ start)) +ᵥ start)

/-- The relative interior of the right-hand mirror in the figure. -/
def OnRightMirror (sideLength : ℝ) (p : OpticalPoint) : Prop :=
  p 0 = sideLength ∧ 0 < p 1 ∧ p 1 < sideLength

/-- The relative interior of the top mirror in the figure. -/
def OnTopMirror (sideLength : ℝ) (p : OpticalPoint) : Prop :=
  p 1 = sideLength ∧ 0 < p 0 ∧ p 0 < sideLength

/-- The relative interior of the left-hand mirror in the figure. -/
def OnLeftMirror (sideLength : ℝ) (p : OpticalPoint) : Prop :=
  p 0 = 0 ∧ 0 < p 1 ∧ p 1 < sideLength

/-- The small aperture at the midpoint of the bottom mirror. -/
def bottomCenterAperture (sideLength : ℝ) : OpticalPoint :=
  ⟨![sideLength / 2, 0]⟩

/-- The inward-pointing normal to the bottom mirror at the aperture. -/
def inwardNormalAtAperture : OpticalVector :=
  !₂[0, 1]

/--
The four labelled contacts of the ray route seen in the figure.  The ray
starts at `aperture`, then meets `rightHit`, `topHit`, and `leftHit`, before
returning to `aperture`.
-/
structure ThreeMirrorRayRoute where
  aperture : OpticalPoint
  rightHit : OpticalPoint
  topHit : OpticalPoint
  leftHit : OpticalPoint

/--
The entry angle `θ`, in radians, measured between the ray inside the enclosure
and the inward normal to the mirror containing the aperture.
-/
def entryAngle (route : ThreeMirrorRayRoute) : ℝ :=
  InnerProductGeometry.angle
    (unitDirection route.aperture route.rightHit)
    inwardNormalAtAperture

/--
A ray entering through the midpoint aperture of a square enclosure, reflecting
once in order from the right, top, and left plane mirrors, and then returning
through the same aperture must enter at `π / 4` radians, i.e. `45°` (answer
choice C).

The open-segment hypotheses record that these are the only three mirror hits;
the three `SpecularReflectionAt` hypotheses are the governing optical law.
Neither group assumes the value of the entry angle.

Blueprint: `thm:physics:phyx_mini_0024:target`.
-/
theorem entryAngle_eq_pi_div_four
    (sideLength : ℝ) (route : ThreeMirrorRayRoute)
    (hSideLength : 0 < sideLength)
    (hAperture : route.aperture = bottomCenterAperture sideLength)
    (hRight : OnRightMirror sideLength route.rightHit)
    (hTop : OnTopMirror sideLength route.topHit)
    (hLeft : OnLeftMirror sideLength route.leftHit)
    (hLeg₀ : OpenSegmentInside sideLength route.aperture route.rightHit)
    (hLeg₁ : OpenSegmentInside sideLength route.rightHit route.topHit)
    (hLeg₂ : OpenSegmentInside sideLength route.topHit route.leftHit)
    (hLeg₃ : OpenSegmentInside sideLength route.leftHit route.aperture)
    (hReflectRight :
      SpecularReflectionAt verticalMirrorTangent
        route.aperture route.rightHit route.topHit)
    (hReflectTop :
      SpecularReflectionAt horizontalMirrorTangent
        route.rightHit route.topHit route.leftHit)
    (hReflectLeft :
      SpecularReflectionAt verticalMirrorTangent
        route.topHit route.leftHit route.aperture) :
    entryAngle route = Real.pi / 4 := by
  let e₀ : OpticalVector := !₂[1, 0]
  let e₁ : OpticalVector := !₂[0, 1]
  have vector_eq_components (v : OpticalVector) :
      v = v 0 • e₀ + v 1 • e₁ := by
    ext i
    fin_cases i <;> simp [e₀, e₁]
  have e₀_vertical_orthogonal : e₀ ∈ verticalMirrorTangentᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    change v 0 = 0 at hv
    simp [PiLp.inner_apply, e₀, hv, Fin.sum_univ_two]
  have e₁_vertical : e₁ ∈ verticalMirrorTangent := by
    change e₁ 0 = 0
    simp [e₁]
  have e₀_horizontal : e₀ ∈ horizontalMirrorTangent := by
    change e₀ 1 = 0
    simp [e₀]
  have e₁_horizontal_orthogonal : e₁ ∈ horizontalMirrorTangentᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    change v 1 = 0 at hv
    simp [PiLp.inner_apply, e₁, hv, Fin.sum_univ_two]
  have vertical_reflection (v : OpticalVector) :
      verticalMirrorTangent.reflection v =
        (-v 0) • e₀ + v 1 • e₁ := by
    calc
      verticalMirrorTangent.reflection v =
          verticalMirrorTangent.reflection (v 0 • e₀ + v 1 • e₁) := by
            rw [← vector_eq_components v]
      _ = (-v 0) • e₀ + v 1 • e₁ := by
        rw [map_add, map_smul, map_smul,
          Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
            e₀_vertical_orthogonal,
          Submodule.reflection_mem_subspace_eq_self e₁_vertical]
        simp
  have horizontal_reflection (v : OpticalVector) :
      horizontalMirrorTangent.reflection v =
        v 0 • e₀ + (-v 1) • e₁ := by
    calc
      horizontalMirrorTangent.reflection v =
          horizontalMirrorTangent.reflection (v 0 • e₀ + v 1 • e₁) := by
            rw [← vector_eq_components v]
      _ = v 0 • e₀ + (-v 1) • e₁ := by
        rw [map_add, map_smul, map_smul,
          Submodule.reflection_mem_subspace_eq_self e₀_horizontal,
          Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
            e₁_horizontal_orthogonal]
        simp
  rcases hRight with ⟨hRight₀, hRight₁_pos, hRight₁_lt⟩
  rcases hTop with ⟨hTop₁, hTop₀_pos, hTop₀_lt⟩
  rcases hLeft with ⟨hLeft₀, hLeft₁_pos, hLeft₁_lt⟩
  rcases hReflectRight with ⟨hApertureRight_ne, hRightTop_ne, hReflectRight⟩
  rcases hReflectTop with ⟨_, hTopLeft_ne, hReflectTop⟩
  rcases hReflectLeft with ⟨_, hLeftAperture_ne, hReflectLeft⟩
  have hAperture₀ : route.aperture 0 = sideLength / 2 := by
    rw [hAperture]
    simp [bottomCenterAperture]
  have hAperture₁ : route.aperture 1 = 0 := by
    rw [hAperture]
    simp [bottomCenterAperture]
  let k₀ : ℝ := ‖route.rightHit -ᵥ route.aperture‖⁻¹
  let k₁ : ℝ := ‖route.topHit -ᵥ route.rightHit‖⁻¹
  let k₂ : ℝ := ‖route.leftHit -ᵥ route.topHit‖⁻¹
  let k₃ : ℝ := ‖route.aperture -ᵥ route.leftHit‖⁻¹
  have k₀_pos : 0 < k₀ := by
    exact inv_pos.mpr (norm_pos_iff.mpr
      (vsub_ne_zero.mpr hApertureRight_ne.symm))
  have k₁_pos : 0 < k₁ := by
    exact inv_pos.mpr (norm_pos_iff.mpr
      (vsub_ne_zero.mpr hRightTop_ne.symm))
  have k₂_pos : 0 < k₂ := by
    exact inv_pos.mpr (norm_pos_iff.mpr
      (vsub_ne_zero.mpr hTopLeft_ne.symm))
  have k₃_pos : 0 < k₃ := by
    exact inv_pos.mpr (norm_pos_iff.mpr
      (vsub_ne_zero.mpr hLeftAperture_ne.symm))
  have hRightReflect₀ :=
    congrArg (fun v : OpticalVector => v 0) hReflectRight
  have hRightReflect₁ :=
    congrArg (fun v : OpticalVector => v 1) hReflectRight
  have hTopReflect₀ :=
    congrArg (fun v : OpticalVector => v 0) hReflectTop
  have hTopReflect₁ :=
    congrArg (fun v : OpticalVector => v 1) hReflectTop
  have hLeftReflect₀ :=
    congrArg (fun v : OpticalVector => v 0) hReflectLeft
  have hLeftReflect₁ :=
    congrArg (fun v : OpticalVector => v 1) hReflectLeft
  simp [vertical_reflection, unitDirection, hAperture₀, hAperture₁,
    hRight₀, Space.vsub_apply, e₀, e₁] at hRightReflect₀
  simp [vertical_reflection, unitDirection, hAperture₀, hAperture₁,
    hRight₀, hTop₁, Space.vsub_apply, e₀, e₁] at hRightReflect₁
  simp [horizontal_reflection, unitDirection, hRight₀, hTop₁,
    hLeft₀, Space.vsub_apply, e₀, e₁] at hTopReflect₀
  simp [horizontal_reflection, unitDirection, hRight₀, hTop₁,
    Space.vsub_apply, e₀, e₁] at hTopReflect₁
  simp [vertical_reflection, unitDirection, hAperture₀,
    hTop₁, hLeft₀, Space.vsub_apply, e₀, e₁] at hLeftReflect₀
  simp [vertical_reflection, unitDirection, hAperture₁,
    hTop₁, hLeft₀, Space.vsub_apply, e₀, e₁] at hLeftReflect₁
  change -(k₀ * (sideLength - sideLength / 2)) =
    k₁ * (route.topHit 0 - sideLength) at hRightReflect₀
  change k₀ * route.rightHit 1 =
    k₁ * (sideLength - route.rightHit 1) at hRightReflect₁
  change k₁ * (route.topHit 0 - sideLength) =
    -(k₂ * route.topHit 0) at hTopReflect₀
  change -(k₁ * (sideLength - route.rightHit 1)) =
    k₂ * (route.leftHit 1 - sideLength) at hTopReflect₁
  change k₂ * route.topHit 0 =
    k₃ * (sideLength / 2) at hLeftReflect₀
  change k₂ * (route.leftHit 1 - sideLength) =
    -(k₃ * route.leftHit 1) at hLeftReflect₁
  have equation₀ :
      k₁ * (route.topHit 0 - sideLength) =
        -(k₀ * (sideLength / 2)) := by
    nlinarith only [hRightReflect₀]
  have equation₁ :
      k₁ * (sideLength - route.rightHit 1) =
        k₀ * route.rightHit 1 := by
    exact hRightReflect₁.symm
  have equation₂ :
      k₂ * route.topHit 0 =
        k₁ * (sideLength - route.topHit 0) := by
    nlinarith only [hTopReflect₀]
  have equation₃ :
      k₂ * (sideLength - route.leftHit 1) =
        k₁ * (sideLength - route.rightHit 1) := by
    nlinarith only [hTopReflect₁]
  have equation₄ :
      k₃ * (sideLength / 2) =
        k₂ * route.topHit 0 := by
    exact hLeftReflect₀.symm
  have equation₅ :
      k₃ * route.leftHit 1 =
        k₂ * (sideLength - route.leftHit 1) := by
    nlinarith only [hLeftReflect₁]
  have k₃_eq_k₀ : k₃ = k₀ := by
    nlinarith only [equation₀, equation₂, equation₄, hSideLength]
  have hLeft₁_eq_right₁ : route.leftHit 1 = route.rightHit 1 := by
    apply mul_left_cancel₀ (ne_of_gt k₀_pos)
    calc
      k₀ * route.leftHit 1 = k₃ * route.leftHit 1 := by rw [k₃_eq_k₀]
      _ = k₂ * (sideLength - route.leftHit 1) := equation₅
      _ = k₁ * (sideLength - route.rightHit 1) := equation₃
      _ = k₀ * route.rightHit 1 := equation₁
  have k₁_eq_k₂ : k₁ = k₂ := by
    have hFactor : sideLength - route.rightHit 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr hRight₁_lt)
    have hMul :
        k₂ * (sideLength - route.rightHit 1) =
          k₁ * (sideLength - route.rightHit 1) := by
      simpa [hLeft₁_eq_right₁] using equation₃
    exact (mul_right_cancel₀ hFactor hMul).symm
  have hTop₀_eq_half : route.topHit 0 = sideLength / 2 := by
    have hMul :
        k₁ * route.topHit 0 =
          k₁ * (sideLength - route.topHit 0) := by
      rw [k₁_eq_k₂] at equation₂
      simpa [k₁_eq_k₂] using equation₂
    have hCoordinate :=
      mul_left_cancel₀ (ne_of_gt k₁_pos) hMul
    linarith
  have k₁_eq_k₀ : k₁ = k₀ := by
    have hFactor : sideLength / 2 ≠ 0 := ne_of_gt (by positivity)
    have hMul : k₁ * (sideLength / 2) = k₀ * (sideLength / 2) := by
      rw [hTop₀_eq_half] at equation₀
      nlinarith only [equation₀]
    exact mul_right_cancel₀ hFactor hMul
  have hRight₁_eq_half : route.rightHit 1 = sideLength / 2 := by
    have hMul :
        k₀ * (sideLength - route.rightHit 1) =
          k₀ * route.rightHit 1 := by
      rw [k₁_eq_k₀] at equation₁
      exact equation₁
    have hCoordinate :=
      mul_left_cancel₀ (ne_of_gt k₀_pos) hMul
    linarith
  have hInitialDisplacement :
      route.rightHit -ᵥ route.aperture =
        (sideLength / 2) • (e₀ + e₁) := by
    ext i
    fin_cases i
    · simp [Space.vsub_apply, hRight₀, hAperture₀, e₀, e₁]
      ring
    · simp [Space.vsub_apply, hRight₁_eq_half, hAperture₁, e₀, e₁]
  have hInitialDirection :
      unitDirection route.aperture route.rightHit =
        (k₀ * (sideLength / 2)) • (e₀ + e₁) := by
    change k₀ • (route.rightHit -ᵥ route.aperture) =
      (k₀ * (sideLength / 2)) • (e₀ + e₁)
    rw [hInitialDisplacement, smul_smul]
  have hScale_pos : 0 < k₀ * (sideLength / 2) :=
    mul_pos k₀_pos (by positivity)
  rw [entryAngle]
  change InnerProductGeometry.angle
    (unitDirection route.aperture route.rightHit) e₁ = Real.pi / 4
  rw [hInitialDirection,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hScale_pos]
  rw [InnerProductGeometry.angle]
  simp [PiLp.inner_apply, EuclideanSpace.norm_eq, Fin.sum_univ_two, e₀, e₁]
  have hSqrtPos : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hSqrtInv : (√(2 : ℝ))⁻¹ = √2 / 2 := by
    field_simp [ne_of_gt hSqrtPos]
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (1 + 1 : ℝ) = 2 by norm_num, hSqrtInv,
    ← Real.cos_pi_div_four]
  exact Real.arccos_cos (by positivity) (by nlinarith only [Real.pi_pos])

end PhyXMiniProblems.ProblemPhyXMini0024
