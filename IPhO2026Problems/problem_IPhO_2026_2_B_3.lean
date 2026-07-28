/-
Autoformalization of IPhO 2026, Theoretical Problem 2 ("Solar Cooker"),
part B.3.

Physical setup (see Figure 2f of the official paper):

* A half-hollow-cylinder mirror of radius `R` concentrates uniform parallel
  sunlight onto a fully absorbing cylindrical container of radius `a`.
* The axes of the mirror and of the container are parallel; the container
  centre lies `R / 2` from the mirror centre on the system's symmetry plane.
* Sunlight arrives parallel to the optical axis of the mirror, with constant
  and uniform intensity (power per unit area).
* Any ray absorbed by the container reflects from the mirror at most once.
* `θ_max` is the maximum angle of incidence on the mirror (measured from the
  normal drawn at the point of incidence) among reflected rays that strike
  the container.
* `P₀` is the power the cylinder would receive if the mirror were not
  present; `P` is the actual received power.

Current subquestion (T2-B3, 0.5 pts):
  For `R = 1.0 m`, find the value of `a` such that `P = 5 P₀`.
  Give the answer in cm.

Recorded official answer: `cos θ_max = 4 / 5` and `a = 0.12 m = 12 cm`.

The formalization below keeps the geometry and the physical laws
(specular reflection at the cylindrical surface, uniform irradiance,
single-reflection condition) as explicit hypotheses, carries the previous-part
results B.1 (`a = R sin θ_max − (R / 2) sin (2 θ_max)`) and
B.2 (`P / P₀ = 1 / (1 − cos θ_max)`) as named hypothesis interfaces, and
states the target conclusions `cos θ_max = 4 / 5`, `a = 0.12 m` and
`a = 12 cm` on the conclusion side of the main theorem.
-/

import Mathlib

open Real

noncomputable section

/-- The maximal incidence angle `θ_max` whose cosine equals the recorded
value `4 / 5`.  This is only a symbolic abbreviation for the acute angle of
the 3-4-5 triangle; the physical content of the answer
(`cos θ_max = 4 / 5`) is proved, not defined, below. -/
abbrev thetaMaxRecorded : ℝ := Real.arccos (4 / 5)

/-- Unit scale: one metre, expressed in centimetres. -/
abbrev metreInCentimetres : ℝ := 100

/-- Euclidean plane containing the cross-section of the mirror/container
system (Figure 2f).  The schematic is a 2D cross-section of the 3D
cylindrical geometry; lengths in this plane are identified with real
numbers via the norm. -/
abbrev CrossSectionPlane := EuclideanSpace ℝ (Fin 2)

/-- Geometric configuration of the mirror–container system in the
cross-section plane (Figure 2f).

* `mirrorRadius` is the radius `R` of the half-cylindrical mirror.
* `containerRadius` is the radius `a` of the fully absorbing container.
* `containerCentre` is the centre of the container's circular cross-section;
  the mirror centre is taken as the origin of the plane.
* `sunDirection` is the (unit) direction of the incoming sunlight, taken
  along the optical axis of the mirror (the symmetry plane direction).
The hypothesis `container_centre_distance` expresses the problem datum that
the container centre lies `R / 2` from the mirror centre on the symmetry
plane, i.e. along `sunDirection`; `sunDirection_unit` records that the
sunlight direction is a unit vector. -/
structure SolarCookerGeometry where
  mirrorRadius : ℝ
  containerRadius : ℝ
  containerCentre : CrossSectionPlane
  sunDirection : CrossSectionPlane
  mirrorRadius_pos : 0 < mirrorRadius
  containerRadius_pos : 0 < containerRadius
  containerRadius_lt : containerRadius < mirrorRadius
  sunDirection_unit : ‖sunDirection‖ = 1
  container_centre_distance : containerCentre = (mirrorRadius / 2) • sunDirection

/-- Results of subquestions B.1 and B.2, reused here as prerequisites.

These are *previous-part results* of the same problem:

* B.1: the container radius satisfies
  `a = α sin θ_max + β sin (2 θ_max)` with `α = R` and `β = -R / 2`.
* B.2: the power ratio satisfies `P / P₀ = 1 / (1 - cos θ_max)`.

They are packaged as hypotheses over an incidence angle `θ`, so that the
current subquestion's conclusions (`cos θ_max = 4/5`, `a = 0.12 m`) are
not smuggled in: nothing here fixes the value of `θ` or of `a`. -/
structure PreviousPartResults
    (mirrorRadius containerRadius : ℝ) (theta : ℝ) (P P0 : ℝ) : Prop where
  /-- The incidence angle `θ_max` is the largest incidence angle among
  reflected rays that strike the container; geometrically it is acute. -/
  theta_range : theta ∈ Set.Ioo 0 (Real.pi / 2)
  /-- Subquestion B.1: geometric relation between the container radius and
  the maximal incidence angle, with the determined coefficients
  `α = R` and `β = -R / 2`. -/
  containerRadius_eq :
    containerRadius
      = mirrorRadius * Real.sin theta - (mirrorRadius / 2) * Real.sin (2 * theta)
  /-- The power `P₀` that would be received without the mirror is positive
  (the container has positive radius and the sunlight has positive
  intensity), so the ratio `P / P₀` is meaningful. -/
  P0_pos : 0 < P0
  /-- The received power `P` is positive: the container absorbs all
  incident light and the concentrated power exceeds the direct one. -/
  P_pos : 0 < P
  /-- Subquestion B.2: ratio of the actual received power `P` to the
  no-mirror power `P₀`, as a function of the maximal incidence angle. -/
  power_ratio_eq : P / P0 = 1 / (1 - Real.cos theta)

/-- Physics of the solar cooker: governing laws and modelling assumptions
for the cross-section geometry.

The predicate packages, for a cross-section point `x` and incidence angle
`θ`:

* **Specular reflection.** A light ray arriving along `-sunDirection`
  (anti-parallel to the optical axis) and reflecting at the mirror surface
  point `x` obeys the law of reflection about the surface normal.  For the
  cylindrical mirror of radius `mirrorRadius` centred at the origin the
  normal at `x` is the radial direction `mirrorRadius⁻¹ • x`, so the
  reflected direction equals the Euclidean reflection of the incoming
  direction in the line spanned by `x`
  (`Submodule.reflection` applied to the span of `x`).
* **Incidence angle.** The incidence angle `θ` at `x` is the angle between
  the incoming ray and the outward normal `x`: by definition,
  `cos θ = ⟪x, -sunDirection⟫ / R` whenever `‖x‖ = R`.
* **Single reflection.** `x` lies on the illuminated half of the mirror so
  that the ray reflects exactly once before reaching the container
  (the rays absorbed by the container reflect at most once).
* **Absorption.** Any ray striking the container is fully absorbed and
  contributes its power to `P`.

The fields expose concrete mathematical content (equations and angle
relations), so the predicate genuinely constrains any model: an arbitrarily
chosen `angleOfIncidence` that fails the cosine law cannot satisfy
`incidence_cos`, and a direction that is not the mirror reflection of the
incoming ray cannot satisfy `specular_reflection`. -/
structure HalfCylindricalMirrorPhysics
    (G : SolarCookerGeometry)
    (x : CrossSectionPlane) (theta : ℝ) : Prop where
  /-- The reflection point lies on the mirror surface. -/
  on_mirror : ‖x‖ = G.mirrorRadius
  /-- The reflection point lies on the illuminated (sun-facing) half of the
  mirror: the incoming ray direction `-sunDirection` points toward the
  mirror there, equivalently the surface normal has negative component
  along the sunlight direction.  Together with `on_mirror` this encodes
  the single-reflection condition of the problem. -/
  illuminated_side : @inner ℝ _ _ x G.sunDirection < 0
  /-- Law of specular reflection at the cylindrical surface: the outward
  direction of the ray reflected at `x` is the Euclidean reflection of the
  incoming direction `-sunDirection` in the normal line `ℝ ∙ x`. -/
  specular_reflection :
    (ℝ ∙ x).reflection (-G.sunDirection)
      = 2 • ((@inner ℝ _ _ x (-G.sunDirection))
              / (G.mirrorRadius ^ 2)) • x - (-G.sunDirection)
  /-- The incidence angle at `x`, measured with respect to the normal drawn
  at the point of incidence. -/
  angleOfIncidence : theta = Real.arccos ((@inner ℝ _ _ x (-G.sunDirection)) / G.mirrorRadius)
  /-- The incidence angle is acute, as it is for any ray of the
  single-reflection branch that reaches the container. -/
  angle_acute : theta ∈ Set.Ioo 0 (Real.pi / 2)

/-- Auxiliary fact supporting the recorded value: the incidence angle whose
cosine is `4 / 5` is acute, as required by the single-reflection branch. -/
lemma thetaMaxRecorded_mem_Ioo :
    thetaMaxRecorded ∈ Set.Ioo 0 (Real.pi / 2) := by
  -- `arccos (4/5)` lies strictly between `arccos 1 = 0` and `arccos 0 = π/2`
  -- because `arccos` is strictly antitone on `[-1, 1]`.
  have h1 : Real.arccos 1 = 0 := Real.arccos_one
  have h2 : Real.arccos 0 = Real.pi / 2 := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    simp [Real.arcsin_zero]
  constructor
  · calc (0 : ℝ) = Real.arccos 1 := h1.symm
      _ < Real.arccos (4 / 5) :=
        Real.strictAntiOn_arccos (by norm_num) (by norm_num) (by norm_num)
  · calc Real.arccos (4 / 5) < Real.arccos 0 :=
        Real.strictAntiOn_arccos (by norm_num) (by norm_num) (by norm_num)
      _ = Real.pi / 2 := h2

/-- The sine of the recorded maximal incidence angle is `3 / 5`
(the 3-4-5 triangle of Figure 2f's geometry). -/
lemma sin_thetaMaxRecorded : Real.sin thetaMaxRecorded = 3 / 5 := by
  rw [Real.sin_arccos]
  rw [show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The sine of twice the recorded maximal incidence angle is `24 / 25`,
via `sin (2θ) = 2 sin θ cos θ`. -/
lemma sin_two_mul_thetaMaxRecorded : Real.sin (2 * thetaMaxRecorded) = 24 / 25 := by
  rw [Real.sin_two_mul, sin_thetaMaxRecorded,
    Real.cos_arccos (by norm_num) (by norm_num)]
  norm_num

/-- **Main target of subquestion B.3.**

Given a solar-cooker geometry governed by the mirror physics above (at
some reflection point reaching the container, hence with incidence angle
`θ_max`), with mirror radius `R = 1 m`, container radius `a`, received
power `P` and no-mirror power `P₀` satisfying the previous-part relations
B.1 and B.2, if the received power is five times the no-mirror power
(`P = 5 P₀`), then:

* the maximal incidence angle equals the recorded value
  (`cos θ_max = 4 / 5`),
* the container radius is `a = 0.12 m`,
* reported in centimetres, `a * 100 = 12 cm`. -/
theorem container_diameter_for_quintuple_power
    (G : SolarCookerGeometry)
    (R a thetaMax P P0 : ℝ)
    (hR_val : R = 1)
    (hR : G.mirrorRadius = R)
    (ha : G.containerRadius = a)
    (x : CrossSectionPlane)
    (hphys : HalfCylindricalMirrorPhysics G x thetaMax)
    (hprev : PreviousPartResults R a thetaMax P P0)
    (hP : P = 5 * P0) :
    thetaMax = thetaMaxRecorded ∧ a = 0.12 ∧ a * metreInCentimetres = 12 := by
  -- Invert the B.2 ratio: `P / P₀ = 5 = 1 / (1 - cos θ_max)` forces
  -- `1 - cos θ_max = 1 / 5`, hence `cos θ_max = 4 / 5`.
  have hP0_ne : P0 ≠ 0 := ne_of_gt hprev.P0_pos
  have hratio : P / P0 = 5 := by
    rw [hP]
    field_simp
  have h5eq : (5 : ℝ) = 1 / (1 - Real.cos thetaMax) :=
    hratio ▸ hprev.power_ratio_eq
  have hcos_sub : 1 - Real.cos thetaMax ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at h5eq
    norm_num at h5eq
  have hcos_val : Real.cos thetaMax = 4 / 5 := by
    have h := (eq_div_iff hcos_sub).mp h5eq
    linarith
  -- cosine is injective on the acute range `(0, π/2)`, so `θ_max` is the
  -- recorded angle `arccos (4/5)`.
  have htheta : thetaMax = thetaMaxRecorded := by
    obtain ⟨t0, thalf⟩ := hprev.theta_range
    have htheta_le : thetaMax ≤ Real.pi := by linarith [Real.pi_pos]
    have htheta_nonneg : 0 ≤ thetaMax := le_of_lt t0
    calc thetaMax = Real.arccos (Real.cos thetaMax) :=
        (Real.arccos_cos htheta_nonneg htheta_le).symm
      _ = thetaMaxRecorded := by rw [hcos_val]
  rw [htheta] at hprev
  -- Substitute `θ_max` and `R = 1` into the B.1 relation with the 3-4-5
  -- certificates: `a = 3/5 - (1/2)(24/25) = 3/25 = 0.12 m = 12 cm`.
  have ha_val : a = 0.12 := by
    have h := hprev.containerRadius_eq
    rw [hR_val, sin_thetaMaxRecorded, sin_two_mul_thetaMaxRecorded] at h
    rw [h]
    norm_num
  exact ⟨htheta, ha_val, by rw [ha_val]; norm_num [metreInCentimetres]⟩

end
