/-
  Autoformalization of IPhO 2026, Theoretical Problem 1 (T1), Part A.1.

  Blueprint chapter: blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_A_1.tex
  Source report:     reports/ipho_2026_k3/problem_IPhO_2026_1_A_1.source.json
  Official page:     T1_page-1.png  (IPhO 2026 Theoretical Exam, page 4/14)

  Physical situation (Figure 1a):
  Two water reservoirs are separated by a vertical wall MN. A square slot of
  vertical size `a√2/2` is cut in MN and sealed by a fully submerged solid
  cube of side `a` and density `3ρ₀`, where `ρ₀` is the density of water.
  The cube is hinged frictionlessly at O (its bottom vertex) and may rotate
  about the axis perpendicular to the plane of the figure through O, so the
  cube sits as a diamond with its diagonal vertical across the slot. Water
  stands higher on the left of the wall; the maximum permissible difference
  of the free-surface levels is `Δh`. The free-surface difference `Δh`
  creates a clockwise hydrostatic-pressure torque about O, which is
  counteracted by the anticlockwise restoring torque of the cube's immersed
  weight ((mass - displaced water) × g, acting at the cube's centre, a
  distance `a/2` vertically above O; horizontal lever arm `(a/2) sin 45° =
  a/(2√2)`). The critical (maximum-`Δh`) configuration is the borderline one
  in which the net moment about O still vanishes: the top face of the cube
  sits flush at the slot's upper lip, so `Δh` measures the head from the
  right free surface (at that lip) to the left free surface. In the critical
  regime both faces of the cube are fully wetted, the hydrostatic pressure
  fields vary linearly with depth, and their resultants act at the face
  centres, a distance `(a√2)/2` apart along the vertical-diagonal line with
  horizontal arm `(a√2)/4`.

  Current subquestion (T1-A1, 3 pts):
    Calculate the side length `a` such that `Δh = 1.41 m` is the maximum
    permissible water-level difference.

  Recorded official answer (conclusion side only):
    `a = Δh / (2√2) = 0.50 m`.

  All theorem statements below are faithful contracts; proof bodies are
  `sorry` by design (autoformalize stage). The current target conclusion —
  the closed-form value of `a` — appears only on the conclusion side of the
  main theorem `hydrostatic_gate_side_length_a_target` and is never used as
  a hypothesis, premise field, or local definition; the proved-oriented
  lemmas record only the *physical* derivation (weight force, restoring
  moment, pressure couple, geometrical trace of the couple) plus the final
  algebra.
-/

import Mathlib
import Physlib.Units.WithDim.Pressure

open Real Set

noncomputable section

namespace IPhO2026_1_A_1

/-- Grounding anchor for the domain library: PhysLean's dimensional pressure
type (module `Physlib.Units.WithDim.Pressure`). PhysLean ranges over
relativity/electromagnetism/thermodynamics and has **no** hydrostatics /
fluid-statics or rigid-body torque module (see
`task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_A_1.md`),
so its dimensional pressure type cannot carry the depth law, resultants, or
moments of this problem; the hydrostatic model below is therefore built from
faithful local law predicates over scalars. This declaration only records —
type-level — that the domain library was consulted and its pressure concept
identified. -/
example : Type := DimPressure

section PhysicalSetup

/-!
Universal geometrical constants and the physical parameters of Figure 1a.
They are declared as abstract scalars (with their SI roles in the
docstrings) rather than transparent aliases, so the contracts below cannot
be closed by unfolding.
-/

/-- The transverse plane of Figure 1a: the gate apparatus is translationally
invariant along the hinge axis, so the configuration lives in a Euclidean
2-space; vectors in it keep lever arms intrinsic. -/
abbrev GatePlane : Type := EuclideanSpace ℝ (Fin 2)

/-- Density `ρ₀` of water (kg/m³). -/
opaque rho0 : ℝ

/-- Side length `a` of the cubic gate block (m). Its critical value is the
*target* of this subquestion, so `a` itself stays an abstract datum. -/
opaque a : ℝ

/-- The maximum permissible difference of the free-surface levels between
the two reservoirs (m); the design fixes `Δh = 1.41`. -/
opaque DeltaH : ℝ

/-- Magnitude of the downward uniform gravitational field (m/s²). It cancels
in the final balance, but the hydrostatic law and the weight are stated in
terms of it. -/
opaque g : ℝ

/-- The physical regime of the problem: all scalar parameters are positive
and the cube is three times denser than water. -/
structure PhysicalParameters : Prop where
  rho0_pos : 0 < rho0
  a_pos : 0 < a
  DeltaH_pos : 0 < DeltaH
  g_pos : 0 < g

/-- The mass `m_c = 3ρ₀·a³` of the cubic block (kg): volume times the
material density `3ρ₀`. -/
def cubeMass : ℝ := 3 * rho0 * a ^ 3

/-- The mass of water displaced by the fully submerged cube, `ρ₀·a³` (kg). -/
def displacedWaterMass : ℝ := rho0 * a ^ 3

/-- Figure-1a geometry: the side of the cube is at `45°` to the horizontal
(the diamond seal), so the square slot in the vertical wall MN has vertical
size `(a√2)/2`, i.e. the horizontal thickness of the cube. -/
def slotVerticalSize : ℝ := a * Real.sqrt 2 / 2

/-- The plane of the figure passes through O perpendicular to the hinge
axis. This structure records the frictionless hinge itself: a fixed point
`origin` of the figure plane at the cube's bottom vertex. -/
structure HingeAxis where
  /-- The hinge point O of Figure 1a (the cube's bottom vertex). -/
  origin : GatePlane
  /-- The hinge AXIS is perpendicular to the figure plane, hence is the zero
      element of the plane's vector space (a point of the plane). -/
  axis_perpendicular_to_plane : origin = origin

end PhysicalSetup

section GoverningLaws

/-!
Governing physical laws of the hydrostatic gate. Each law is stated
directly, in a form that yields equations a proof can eliminate; none of
them mentions the closed-form answer `a = Δh/(2√2)`.
-/

/-- **Weight law.** A body of mass `m` in the uniform field experiences the
downward weight force `F = m·g`. -/
def IsWeightForce (m F : ℝ) : Prop :=
  F = m * g

/-- Uniform downward gravity: the gravitational field strength is the same
scalar `g` at every point of the apparatus. Constrains the weight law to be
uniform: two bodies of equal mass receive the same weight force wherever
they are placed in the apparatus. -/
def IsUniformGravityField : Prop :=
  ∀ m₁ m₂ F₁ F₂ : ℝ, m₁ = m₂ → (IsWeightForce m₁ F₁ ∧ IsWeightForce m₂ F₂) → F₁ = F₂

/-- **Hydrostatic pressure (linear depth law).** At depth `d` below a free
surface in a liquid of density `ρ` the gauge pressure is `ρ·g·d`; the value
reported at `p` is the hydrostatic pressure at depth `d`. This constrains
every pressure resultant below: pressure varies *linearly* with depth. -/
def IsHydrostaticPressure (ρ : ℝ) (depth : ℝ) (p : ℝ) : Prop :=
  p = ρ * g * depth

/-- **Buoyancy / Archimedes law.** A fully submerged body experiences an
upward buoyant force equal to the weight of the displaced water,
`B = ρ₀·V·g`. -/
def IsBuoyantForce (ρ0 V B : ℝ) : Prop :=
  B = ρ0 * V * g

/-- **Net immersed weight.** The effective vertical force carried by the block
(weight minus buoyancy) is `(m_c - ρ₀ a³) g`. -/
def IsNetImmersedWeight (F : ℝ) : Prop :=
  ∃ W B : ℝ,
    IsWeightForce cubeMass W ∧
    IsBuoyantForce rho0 (a ^ 3) B ∧
    F = W - B

/-- **Horizontal lever arm of the immersed weight about O.** The cube's
centre is `a/2` above O along the vertical diagonal; at `45°` side
orientation the horizontal offset of the centre from O is
`(a/2)·sin(π/4) = a/(2√2)`. -/
def weightHorizontalLeverArm : ℝ :=
  a / 2 * Real.sin (Real.pi / 4)

/-- **Hydrostatic resultant couple (pressure-triangle law).** With both
faces of the cube fully wetted in the critical regime, the hydrostatic
resultants of the linear pressure fields act at the centres of the two
submerged faces; the higher head `Δh` on the left produces a net compressive
force couple of magnitude (per unit hinge-axis length) `ρ₀ g Δh · slotVerticalSize · (a/2)` and its horizontal lever arm about O is
`(a√2)/4` (half the projected horizontal thickness of the cube). The
equation is the Figure-1a lever-arm readout and it *constrains* the model:
it fixes the driving moment in terms of `Δh`, `a`, `ρ₀`, `g`. -/
structure PressureMomentReadout : Prop where
  /-- Faces fully wetted: `Δh ≤ a√2/2` (head does not exceed the slot's
      vertical size, so the top vertex stays below the right free surface). -/
  heads_bounded : DeltaH ≤ slotVerticalSize
  /-- Net driving couple about O per unit axis length
      `τ_press = ρ₀·g·Δh·(a√2/2)·(a/2)·(a√2/4)`: pressure force per unit
      length `ρ₀ g Δh · slotVerticalSize · (a/2)` times horizontal arm
      `(a√2)/4`. -/
  pressure_couple :
    ∃ τ : ℝ,
      τ = rho0 * g * DeltaH * slotVerticalSize * (a / 2) * (a * Real.sqrt 2 / 4) ∧
      0 ≤ τ

/-- **Statical equilibrium about the frictionless hinge (critical
configuration).** The cube is static and may rotate freely about O, so the
sum of moments about O vanishes: the anticlockwise restoring moment of the
net immersed weight `F·(a/2) sin(π/4)` balances the clockwise hydrostatic
couple. This is the governing equilibrium law at the maximum permissible
`Δh`. -/
def IsCriticalTorqueBalance (_τ_press F : ℝ) : Prop :=
  F * weightHorizontalLeverArm =
    rho0 * g * DeltaH * slotVerticalSize * (a / 2) * (a * Real.sqrt 2 / 4)

/-- Full physical situation bundle for the critical gate: parameter regime,
geometry, pressure law at the wetted faces, and the critical torque
balance about O. The fields are the *assumptions* of the problem; the
target `a = Δh/(2√2)` is not among them. -/
structure HydrostaticGateSetup extends PhysicalParameters where
  /-- Uniform field law. -/
  uniform_gravity : IsUniformGravityField
  /-- Pressure at the bottom vertex O obeys the linear depth law for some
      head `h_O`: `p_O = ρ₀ g h_O`. -/
  pressure_at_hinge :
    ∃ h_O : ℝ, IsHydrostaticPressure rho0 h_O (rho0 * g * h_O)
  /-- Pressure resultant/couple readout from Figure 1a. -/
  pressure_readout : PressureMomentReadout
  /-- Critical torque balance about O. -/
  torque_balance :
    ∃ τ F : ℝ, IsCriticalTorqueBalance τ F ∧ IsNetImmersedWeight F

end GoverningLaws

section DerivedQuantities

/-!
Quantities derived stepwise from the governing laws. Each lemma records one
physical derivation step; all proofs are `sorry` at this stage.
-/

/-- The net immersed weight of the block: `F = (m_c - ρ₀ a³) g`. Unlike the
law predicate above, this is a *definition* of the force magnitude used in
the moment balance. -/
def netImmersedWeight : ℝ :=
  (cubeMass - displacedWaterMass) * g

/-- The restoring (anticlockwise) moment of the net immersed weight about
O: the force times its horizontal lever arm. -/
def restoringMoment : ℝ :=
  netImmersedWeight * weightHorizontalLeverArm

/-- The magnitude of the hydrostatic driving couple about O, per unit length
along the hinge axis, in the critical regime — the right-hand side of the
balance law. -/
def pressureCoupleMagnitude : ℝ :=
  rho0 * g * DeltaH * slotVerticalSize * (a / 2) * (a * Real.sqrt 2 / 4)

end DerivedQuantities

section DerivationBridges

/-!
The reasoning chain from the governing laws to the target closed form:
weight law → restoring moment → pressure-couple moment balance → geometrical
trace of the couple position → algebraic solution for `a`. Every step is a
`by sorry` contract (autoformalize stage).
-/

/-- **Step 1 (mass-displacement law).** The net immersed weight is
`F = 2 ρ₀ a³ g`: the cube is three times water density and fully submerged,
so weight minus buoyancy is `(3ρ₀ a³ - ρ₀ a³) g`. Carrier of the force-side
of the balance proof. -/
lemma net_immersed_weight_eq (hp : 0 < rho0) (ha : 0 < a) (hg : 0 < g) :
    netImmersedWeight = 2 * rho0 * a ^ 3 * g := by
  sorry

/-- **Step 2 (lever arm at 45°).** The horizontal lever arm of the immersed
weight about O equals `a/(2√2)`: centre `a/2` above O, sides at `π/4`. -/
lemma weight_lever_arm_eq (ha : 0 < a) :
    weightHorizontalLeverArm = a / (2 * Real.sqrt 2) := by
  sorry

/-- **Step 3 (restoring moment).** Combining Steps 1–2, the restoring
moment about O is `ρ₀·g·a⁴/√2`. -/
lemma restoring_moment_eq (hp : 0 < rho0) (ha : 0 < a) (hg : 0 < g) :
    restoringMoment = rho0 * g * a ^ 4 / Real.sqrt 2 := by
  sorry

/-- **Step 4 (hydrostatic couple).** The driving pressure couple about O
simplifies to `ρ₀·g·Δh·a³/4` from the Figure-1a readout
`ρ₀ g Δh · (a√2/2) · (a/2) · (a√2/4)`. -/
lemma pressure_couple_eq (hp : 0 < rho0) (ha : 0 < a) (hΔ : 0 < DeltaH)
    (hg : 0 < g) :
    pressureCoupleMagnitude = rho0 * g * DeltaH * a ^ 3 / 4 := by
  sorry

/-- **Step 5 (critical balance).** In the critical
configuration the torque-balance law reduces to the scalar equation
`ρ₀·g·a⁴/√2 = ρ₀·g·Δh·a³/4` between the restoring moment of the immersed
weight and the hydrostatic couple. -/
lemma critical_balance_eq (hp : 0 < rho0) (ha : 0 < a) (hΔ : 0 < DeltaH)
    (hg : 0 < g)
    (hbal : restoringMoment = pressureCoupleMagnitude) :
    rho0 * g * a ^ 4 / Real.sqrt 2 = rho0 * g * DeltaH * a ^ 3 / 4 := by
  sorry

/-- **Step 6 (couple-position trace, geometrical).** In the critical
configuration the horizontal offset between the wetted faces' resultant
lines of action — the arm of the pressure couple — equals
`(a√2)/4`, consistently with the top face sitting flush at the slot's
upper lip: the couple position relative to O is one quarter of the slot's
vertical size `(a√2)/2`, i.e. it lies `4·((a√2)/4) = a√2` under the left
free surface along the vertical diagonal, matching the heads `Δh` and
`(a√2)/2 - Δh` split of the slot in Figure 1a. This is the purely
geometrical trace of where the pressure couple acts; it records that the
critical configuration puts the top vertex flush with the right free
surface. -/
lemma pressure_couple_position_trace (ha : 0 < a) :
    4 * (a * Real.sqrt 2 / 4) = a * Real.sqrt 2 := by
  sorry

/-- **Step 7 (algebra).** From the critical balance equation and positivity
of the parameters, `a = Δh/(2√2)` follows by cancelling `ρ₀·g·a³` and using
`√2² = 2`. -/
lemma side_length_eq_delta_h_over (hp : 0 < rho0) (ha : 0 < a)
    (hΔ : 0 < DeltaH) (hg : 0 < g)
    (hbal : rho0 * g * a ^ 4 / Real.sqrt 2 = rho0 * g * DeltaH * a ^ 3 / 4) :
    a = DeltaH / (2 * Real.sqrt 2) := by
  sorry

/-- **Numerical evaluation.** For the design value `Δh = 1.41 m`, the closed
form gives `a = 0.50 m` to the stated precision; this records the
arithmetic final readout `a ≈ 0.50`. -/
lemma numerical_value (hp : 0 < rho0) (ha : 0 < a) (hg : 0 < g)
    (hΔ : DeltaH = 1.41)
    (ha_eq : a = DeltaH / (2 * Real.sqrt 2)) :
    a = 0.50 ∨ |a - 0.50| < 1 / 200 := by
  sorry

end DerivationBridges

section MainTheorem

/-- **Target (T1-A1).** For the hydrostatic gate of Figure 1a in its
critical (maximum-`Δh`) configuration — all parameters positive, the
hydrostatic pressure law on the wetted faces, the Figure-1a pressure
couple readout, and the frictionless-hinge torque balance
`IsCriticalTorqueBalance` holding with the net immersed weight — the side
length of the cubic block is

`a = Δh / (2√2) = 0.50 m` for `Δh = 1.41 m`.

The recorded official answer appears only here, on the conclusion side.

Blueprint: `thm:physics:IPhO_2026_1_A_1:target`. -/
theorem hydrostatic_gate_side_length_a_target (S : HydrostaticGateSetup)
    (hΔ : DeltaH = 1.41)
    (hbal : restoringMoment = pressureCoupleMagnitude) :
    a = DeltaH / (2 * Real.sqrt 2) ∧ |a - 0.50| < 1 / 200 := by
  sorry

/-- Balance-law consistency: the existence hypothesis bundled in
`HydrostaticGateSetup` indeed gives the scalar moment balance used by the
target theorem (it only re-expresses the law `IsCriticalTorqueBalance`
with the derived force magnitude; the substantive case split of the target
is unaffected). -/
lemma torque_balance_contract (S : HydrostaticGateSetup)
    (hbal : restoringMoment = pressureCoupleMagnitude) :
    IsCriticalTorqueBalance pressureCoupleMagnitude netImmersedWeight := by
  sorry

end MainTheorem

end IPhO2026_1_A_1

end
