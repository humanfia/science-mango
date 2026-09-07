import Mathlib

/-!
# IPhO 2026 · Theory problem T1-A1 — "Hydrostatic gate"

Autoformalization of IPhO 2026 T1-A1 (source: `reports/ipho_2026/problem_ipho_2026_t1_a1.source.json`,
figure `ipho_2026_source/image/T1_page-1.png`, Fig. 1a).

## Physical scenario

Two water reservoirs are separated by a vertical wall MN.  The left reservoir can be
filled from a source, so its free surface can stand higher than the right one; the
difference of the levels is `Δh`.  A slot of vertical size `a·√2/2` is cut in MN and is
sealed by a solid cubic block of side `a` and density `3·ρ₀` (with `ρ₀` the density of
water).  The block is fully submerged, is fixed to the wall at the point O, and can
rotate without friction about the axis perpendicular to the plane of the figure
through O.  It must be ensured that the maximum possible difference of the water
levels is `Δh = 1.41 m`.

**Subquestion T1-A1.** Calculate the side length `a` that makes `Δh = 1.41 m` the
maximum permissible water-level difference.

## Figure 1a readout (coordinates)

In the plane of the figure, with the centre C of the square cross-section of the block
as origin, `x` pointing right and `y` pointing up, and `d = a·√2/2` the half-diagonal:

* the square cross-section is tilted 45°, vertices at `(± d, 0)`, `(0, ± d)`;
* the wall MN is the vertical line `x = -d/2` (M above, N below);
* the hinge **O is the midpoint of the upper-left edge**, `O = (-d/2, d/2)`: the
  figure label `½a` measures the distance `a/2` along the edge from the left vertex
  `(-d, 0)` to O;
* the wall crosses the lower-left edge at its midpoint `(-d/2, -d/2)` as well, so the
  slot is the wall segment `-d/2 ≤ y ≤ d/2`, of vertical size `d = a·√2/2`
  (see `slot_geometry_consistent`);
* the triangular tip of the block with `x ≤ -d/2` pokes through the slot and is wetted
  by the *left* reservoir along the two half-edges of length `a/2`; every other face
  is wetted by the *right* reservoir; both free surfaces lie above the block
  (fully submerged).

## Physical model (assumptions)

1. *Hydrostatic law* (`hydrostaticGaugePressure`): gauge pressure at depth `s` below a
   free surface open to the atmosphere is `ρ₀·g·s`.  Because both surfaces are
   atmospheric and the block is fully submerged, at every height the left-minus-right
   pressure is the constant `ρ₀·g·Δh` (`excess_pressure_uniform`, `excessPressure`).
2. *Pressure decomposition*: the hydrostatic field is split into the equal-level part,
   whose resultant is the Archimedes buoyancy `ρ₀·g·a³` at the centroid of the
   displaced volume (the centre C, see `buoyancyForce`), and the uniform excess part
   `ρ₀·g·Δh` acting on the left-wetted half-faces only.
3. *Excess resultant*: a uniform pressure on the two 45° half-faces gives a horizontal
   force `Δp·A_proj` with `A_proj = (a·√2/2)·a` the vertical projection of the wetted
   surface times the block depth (`exposedProjectedArea`, `excessHydrostaticForce`);
   by symmetry of the projection about the centre height, its line of action is
   horizontal at the centre height, i.e. `a·√2/4` below O (`pressureLeverArm`).
4. *Effective weight*: gravity `3ρ₀·g·a³` and buoyancy `ρ₀·g·a³` both act at C, so the
   apparent weight `2ρ₀·g·a³` acts downward at C, with horizontal lever arm `a·√2/4`
   about O (`effectiveWeight`, `weightLeverArm`).
5. *Frictionless hinge*: the hinge at O transmits forces but no torque, so equilibrium
   of the block is decided by the torque balance about O.  Sign convention:
   counterclockwise (the gate-opening direction, driven by the higher left level) is
   positive; the apparent weight drives the clockwise, gate-closing direction,
   pressing the block against the lower lip of the slot.
6. *Sealing contract* (`SealHolds`): the gate stays sealed iff the overturning torque
   does not exceed the restoring torque; at equality the contact force on the lower
   lip vanishes (incipient opening).  `IsMaxPermissibleLevelDiff` says `Δh` is the
   supremum of the sealed level differences.

## Current target (conclusion side only)

`exists_unique_side`: there is a unique side length `a > 0` for which `1.41 m` is the
maximum permissible level difference.  The derived candidate `candidateSide` (raw
end-to-end quantity `Δh/(2√2)`), its correctness and uniqueness certificates, the
numerical bounds `0.498 < a < 0.499`, and the source-derived rounding rule (round *up*
to whole centimetres — a larger block only seals better, cf. `sealed_upto_iff` —
giving `0.50 m`, see `candidateSide_ceiling_cm`) are all proved from the model; none
of them is assumed.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
lengths in m, densities in kg/m³, `g` in m/s², pressures in Pa, forces in N,
torques in N·m.  LeanExplore found no usable PhysLean hydrostatics / planar-statics
torque API (`RigidBody` mass distributions and the Navier–Stokes continuum
`FluidDynamics` structures are near misses), so the model is built from real-valued
quantities with the physical roles kept explicit.
-/

namespace IPhO2026.T1A1

/-! ## Problem parameters and figure readouts (Fig. 1a) -/

/-- Prescribed maximum permissible difference of the water levels, `Δh = 1.41 m`
(problem data; the left reservoir is the higher one, so `Δh ≥ 0` throughout).
Units: metres. -/
noncomputable def deltaHGiven : ℝ := 1.41

/-- Density of the cubic block, `3·ρ₀`, where `ρ₀` is the density of water
(problem data).  Units: kg/m³. -/
noncomputable def blockDensity (ρ₀ : ℝ) : ℝ := 3 * ρ₀

/-- Vertical size of the slot cut in the wall MN, `a·√2/2` (problem data, Fig. 1a).
Units: metres. -/
noncomputable def slotVerticalSize (a : ℝ) : ℝ := a * Real.sqrt 2 / 2

/-- Distance from the centre C of the square cross-section to a vertex
(half-diagonal), `a·√2/2`.  Units: metres. -/
noncomputable def centerToVertex (a : ℝ) : ℝ := a * Real.sqrt 2 / 2

/-- Hinge position along the upper-left edge: the figure label `½a` places the
hinge O at the midpoint of the upper-left edge, a distance `a/2` from the left
vertex.  Units: metres. -/
noncomputable def hingeEdgeOffset (a : ℝ) : ℝ := a / 2

/-- Lever arm of the effective weight about O: with the 45° tilt, the centre C is
horizontally displaced from O by half the half-diagonal, `a·√2/4`
(Fig. 1a coordinate readout).  Units: metres. -/
noncomputable def weightLeverArm (a : ℝ) : ℝ := centerToVertex a / 2

/-- Lever arm of the excess-pressure resultant about O: the resultant acts
horizontally at the centre height of the block, i.e. vertically `a·√2/4` below O
(Fig. 1a coordinate readout).  Units: metres. -/
noncomputable def pressureLeverArm (a : ℝ) : ℝ := centerToVertex a / 2

/-! ## Governing laws and derived physical quantities -/

/-- Hydrostatic gauge-pressure law (governing law): in static water whose free
surface is open to the atmosphere, the gauge pressure at (positive) depth `s`
below the free surface is `ρ₀·g·s`.  Units: pascals. -/
noncomputable def hydrostaticGaugePressure (ρ₀ g s : ℝ) : ℝ := ρ₀ * g * s

/-- Uniform excess pressure produced by the level difference (consequence of the
hydrostatic law, see `excess_pressure_uniform`): with both free surfaces
atmospheric and the block fully submerged, the left-minus-right pressure
difference at any fixed height is the constant `ρ₀·g·Δh`.  Units: pascals. -/
noncomputable def excessPressure (ρ₀ g Δh : ℝ) : ℝ := ρ₀ * g * Δh

/-- Vertical projection of the block surface wetted from the left through the
slot (the two 45° half-faces of edge length `a/2`), times the block depth `a`
perpendicular to the figure: `2·(a/2)·(√2/2)·a = (a·√2/2)·a`, exactly the slot
cross-section `slotVerticalSize a × a`.  Units: m². -/
noncomputable def exposedProjectedArea (a : ℝ) : ℝ := slotVerticalSize a * a

/-- Resultant horizontal force exerted on the block by the excess pressure:
the uniform excess pressure times the projected area.  Units: newtons. -/
noncomputable def excessHydrostaticForce (ρ₀ g a Δh : ℝ) : ℝ :=
  excessPressure ρ₀ g Δh * exposedProjectedArea a

/-- Weight of the block, `3·ρ₀·g·a³`, acting at the centre C.  Units: newtons. -/
noncomputable def gravityForce (ρ₀ g a : ℝ) : ℝ := blockDensity ρ₀ * g * a ^ 3

/-- Archimedes' principle (governing law) for the fully submerged block: the
buoyancy equals the weight of the displaced water, `ρ₀·g·a³`, and acts at the
centroid of the displaced volume, which is the centre C.  Units: newtons. -/
noncomputable def buoyancyForce (ρ₀ g a : ℝ) : ℝ := ρ₀ * g * a ^ 3

/-- Effective (apparent) weight of the submerged block, gravity minus buoyancy,
`(3ρ₀ - ρ₀)·g·a³`; since both terms act at C the resultant acts at C, pointing
downward.  Units: newtons. -/
noncomputable def effectiveWeight (ρ₀ g a : ℝ) : ℝ :=
  gravityForce ρ₀ g a - buoyancyForce ρ₀ g a

/-- Overturning torque about O from the excess hydrostatic pressure
(sign convention: counterclockwise about the axis through O perpendicular to the
figure is positive; this is the gate-opening direction, driven by the higher
left water level).  Units: N·m. -/
noncomputable def overturningTorque (ρ₀ g a Δh : ℝ) : ℝ :=
  excessHydrostaticForce ρ₀ g a Δh * pressureLeverArm a

/-- Restoring torque about O from the effective weight acting at C (clockwise,
gate-closing: it presses the block against the lower lip of the slot).
Units: N·m. -/
noncomputable def restoringTorque (ρ₀ g a : ℝ) : ℝ :=
  effectiveWeight ρ₀ g a * weightLeverArm a

/-! ## Sealing contract and maximum permissible level difference -/

/-- Sealing contract: the gate stays sealed at level difference `Δh` iff the
clockwise restoring torque is at least the counterclockwise overturning torque.
The frictionless hinge at O supplies forces but no torque; while `SealHolds`
holds, equilibrium is maintained by the contact force on the lower lip of the
slot, and at equality that contact force vanishes (incipient opening). -/
def SealHolds (ρ₀ g a Δh : ℝ) : Prop :=
  overturningTorque ρ₀ g a Δh ≤ restoringTorque ρ₀ g a

/-- `Δh` is the *maximum permissible* level difference for a block of side `a`
iff it is positive, the seal holds at `Δh`, and no larger difference is sealed:
`Δh` is the supremum of the sealed level differences. -/
def IsMaxPermissibleLevelDiff (ρ₀ g a Δh : ℝ) : Prop :=
  0 < Δh ∧ SealHolds ρ₀ g a Δh ∧ ∀ Δh' : ℝ, SealHolds ρ₀ g a Δh' → Δh' ≤ Δh

/-! ## Bridge lemmas (proofs deferred to the prover stage) -/

variable (ρ₀ g : ℝ)

/-- Uniformity of the excess pressure: if the left and right free-surface heights
differ by `Δh`, then at every geometric height `y` the left-minus-right gauge
pressure is the constant `excessPressure ρ₀ g Δh`.  Carrier of the hydrostatic
law into the model. -/
theorem excess_pressure_uniform (hL hR y Δh : ℝ) (hΔ : hL - hR = Δh) :
    hydrostaticGaugePressure ρ₀ g (hL - y) - hydrostaticGaugePressure ρ₀ g (hR - y)
      = excessPressure ρ₀ g Δh := by
  unfold hydrostaticGaugePressure excessPressure
  linear_combination ρ₀ * g * hΔ

/-- Figure coherence: the slot vertical size equals twice the vertical distance
from the centre height to O, i.e. the slot spans exactly from O (top) to the
lower crossing point (bottom). -/
theorem slot_geometry_consistent (a : ℝ) :
    slotVerticalSize a = 2 * weightLeverArm a := by
  unfold slotVerticalSize weightLeverArm centerToVertex
  ring

/-- Figure coherence: the `½a` hinge offset along the 45° edge projects to the
lever arm `a·√2/4`, both horizontally and vertically. -/
theorem hinge_offset_consistent (a : ℝ) :
    hingeEdgeOffset a * (Real.sqrt 2 / 2) = weightLeverArm a := by
  unfold hingeEdgeOffset weightLeverArm centerToVertex
  ring

/-- Assembled form of the overturning torque: `ρ₀·g·Δh·a³/4`. -/
theorem overturningTorque_eq (a Δh : ℝ) :
    overturningTorque ρ₀ g a Δh = ρ₀ * g * Δh * a ^ 3 / 4 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold overturningTorque excessHydrostaticForce excessPressure
    exposedProjectedArea slotVerticalSize pressureLeverArm centerToVertex
  linear_combination (ρ₀ * g * Δh * a ^ 3 / 8) * hs

/-- Assembled form of the restoring torque: `√2·ρ₀·g·a⁴/2`. -/
theorem restoringTorque_eq (a : ℝ) :
    restoringTorque ρ₀ g a = Real.sqrt 2 * ρ₀ * g * a ^ 4 / 2 := by
  unfold restoringTorque effectiveWeight gravityForce buoyancyForce blockDensity
    weightLeverArm centerToVertex
  ring

/-- Core bridge: the sealing inequality is linear in `Δh`; the gate seals exactly
up to `Δh = 2·√2·a`.  Positivity of `ρ₀`, `g`, `a` legitimizes the cancellation. -/
theorem sealHolds_iff (hρ₀ : 0 < ρ₀) (hg : 0 < g) (a Δh : ℝ) (ha : 0 < a) :
    SealHolds ρ₀ g a Δh ↔ Δh ≤ 2 * Real.sqrt 2 * a := by
  have pos : (0 : ℝ) < ρ₀ * g * a ^ 3 / 4 := by positivity
  have e1 : ρ₀ * g * Δh * a ^ 3 / 4 = (ρ₀ * g * a ^ 3 / 4) * Δh := by ring
  have e2 : Real.sqrt 2 * ρ₀ * g * a ^ 4 / 2
      = (ρ₀ * g * a ^ 3 / 4) * (2 * Real.sqrt 2 * a) := by ring
  unfold SealHolds
  rw [overturningTorque_eq ρ₀ g a Δh, restoringTorque_eq ρ₀ g a, e1, e2]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h pos
  · intro h
    exact mul_le_mul_of_nonneg_left h pos.le

/-- Safety direction: the gate seals for every level difference in `[0, Δh]` iff
`Δh ≤ 2·√2·a`, i.e. a *larger* block only seals better.  This is the monotonicity
behind "ensures the maximum permissible difference is not exceeded". -/
theorem sealed_upto_iff (hρ₀ : 0 < ρ₀) (hg : 0 < g) (a Δh : ℝ) (ha : 0 < a) (hΔ : 0 ≤ Δh) :
    (∀ Δh' : ℝ, 0 ≤ Δh' → Δh' ≤ Δh → SealHolds ρ₀ g a Δh') ↔ Δh ≤ 2 * Real.sqrt 2 * a := by
  constructor
  · intro h
    exact (sealHolds_iff ρ₀ g hρ₀ hg a Δh ha).mp (h Δh hΔ le_rfl)
  · intro h Δh' _ hle
    exact (sealHolds_iff ρ₀ g hρ₀ hg a Δh' ha).mpr (le_trans hle h)

/-- The maximum permissible level difference is characterized by the torque
balance `Δh = 2·√2·a` (incipient opening at the threshold). -/
theorem isMaxPermissibleLevelDiff_iff (hρ₀ : 0 < ρ₀) (hg : 0 < g) (a Δh : ℝ)
    (ha : 0 < a) (hΔ : 0 < Δh) :
    IsMaxPermissibleLevelDiff ρ₀ g a Δh ↔ Δh = 2 * Real.sqrt 2 * a := by
  constructor
  · intro h
    obtain ⟨hpos, hseal, hsup⟩ := h
    have h1 : Δh ≤ 2 * Real.sqrt 2 * a := (sealHolds_iff ρ₀ g hρ₀ hg a Δh ha).mp hseal
    have h2 : 2 * Real.sqrt 2 * a ≤ Δh :=
      hsup _ ((sealHolds_iff ρ₀ g hρ₀ hg a (2 * Real.sqrt 2 * a) ha).mpr le_rfl)
    exact le_antisymm h1 h2
  · intro heq
    refine ⟨hΔ, (sealHolds_iff ρ₀ g hρ₀ hg a Δh ha).mpr heq.le, ?_⟩
    intro Δh' hseal'
    rw [heq]
    exact (sealHolds_iff ρ₀ g hρ₀ hg a Δh' ha).mp hseal'

/-! ## Main target: existence, uniqueness, and the derived candidate value -/

/-- **T1-A1 main target.**  There is a unique side length for which the
prescribed `Δh = 1.41 m` is exactly the maximum permissible water-level
difference. -/
theorem exists_unique_side (hρ₀ : 0 < ρ₀) (hg : 0 < g) :
    ∃! a : ℝ, 0 < a ∧ IsMaxPermissibleLevelDiff ρ₀ g a deltaHGiven := by
  have h2 : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
  have hΔ : (0 : ℝ) < deltaHGiven := by unfold deltaHGiven; norm_num
  have h2' : (2 : ℝ) * Real.sqrt 2 ≠ 0 := ne_of_gt h2
  refine ⟨deltaHGiven / (2 * Real.sqrt 2), ⟨div_pos hΔ h2, ?_⟩, ?_⟩
  · rw [isMaxPermissibleLevelDiff_iff ρ₀ g hρ₀ hg _ deltaHGiven (div_pos hΔ h2) hΔ]
    -- goal: deltaHGiven = 2 * √2 * (deltaHGiven / (2 * √2))
    have key : (2 : ℝ) * Real.sqrt 2 * (deltaHGiven / (2 * Real.sqrt 2)) = deltaHGiven :=
      calc (2 : ℝ) * Real.sqrt 2 * (deltaHGiven / (2 * Real.sqrt 2))
          = deltaHGiven / (2 * Real.sqrt 2) * (2 * Real.sqrt 2) := mul_comm _ _
        _ = deltaHGiven := div_mul_cancel₀ deltaHGiven h2'
    exact key.symm
  · intro y ⟨hypos, hmax⟩
    rw [isMaxPermissibleLevelDiff_iff ρ₀ g hρ₀ hg y deltaHGiven hypos hΔ] at hmax
    rw [eq_div_iff h2']
    linear_combination -hmax

/-- Raw end-to-end quantity requested by T1-A1 (derived candidate): the side
length whose maximum permissible level difference equals the prescribed `Δh`;
by `isMaxPermissibleLevelDiff_iff` this is `Δh / (2·√2)` metres.  The definition
only records the candidate; that it meets the specification is proved in
`candidateSide_correct` and that nothing else does in `candidateSide_unique`. -/
noncomputable def candidateSide : ℝ := deltaHGiven / (2 * Real.sqrt 2)

/-- The derived candidate meets the specification: it is positive and makes
`1.41 m` the maximum permissible level difference. -/
theorem candidateSide_correct (hρ₀ : 0 < ρ₀) (hg : 0 < g) :
    0 < candidateSide ∧ IsMaxPermissibleLevelDiff ρ₀ g candidateSide deltaHGiven := by
  have h2 : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
  have hΔ : (0 : ℝ) < deltaHGiven := by unfold deltaHGiven; norm_num
  have h2' : (2 : ℝ) * Real.sqrt 2 ≠ 0 := ne_of_gt h2
  refine ⟨div_pos hΔ h2, ?_⟩
  rw [isMaxPermissibleLevelDiff_iff ρ₀ g hρ₀ hg candidateSide deltaHGiven (div_pos hΔ h2) hΔ]
  show deltaHGiven = (2 : ℝ) * Real.sqrt 2 * (deltaHGiven / (2 * Real.sqrt 2))
  exact (calc (2 : ℝ) * Real.sqrt 2 * (deltaHGiven / (2 * Real.sqrt 2))
      = deltaHGiven / (2 * Real.sqrt 2) * (2 * Real.sqrt 2) := mul_comm _ _
    _ = deltaHGiven := div_mul_cancel₀ deltaHGiven h2').symm

/-- Identification: any side length meeting the specification equals the
candidate (uniqueness before recording the derived value). -/
theorem candidateSide_unique (hρ₀ : 0 < ρ₀) (hg : 0 < g) (a : ℝ) (ha : 0 < a)
    (h : IsMaxPermissibleLevelDiff ρ₀ g a deltaHGiven) :
    a = candidateSide := by
  have h2 : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
  have hΔ : (0 : ℝ) < deltaHGiven := by unfold deltaHGiven; norm_num
  rw [isMaxPermissibleLevelDiff_iff ρ₀ g hρ₀ hg a deltaHGiven ha hΔ] at h
  show a = deltaHGiven / (2 * Real.sqrt 2)
  rw [eq_div_iff (ne_of_gt h2)]
  linear_combination -h

/-- Numerical evaluation of the raw quantity: `a = 1.41·√2/4 ≈ 0.4985 m`. -/
theorem candidateSide_bounds :
    (0.498 : ℝ) < candidateSide ∧ candidateSide < 0.499 := by
  have h1 : (1.4142 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2 : Real.sqrt 2 < (1.4143 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have h2pos : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
  show (0.498 : ℝ) < 1.41 / (2 * Real.sqrt 2) ∧ 1.41 / (2 * Real.sqrt 2) < 0.499
  constructor
  · rw [lt_div_iff₀ h2pos]
    linarith [h2]
  · rw [div_lt_iff₀ h2pos]
    linarith [h1]

/-- Source-derived rounding rule: the datum `Δh = 1.41 m` is stated to the
nearest centimetre; reporting the side length rounded *up* to whole centimetres
guarantees the permissible difference is not exceeded (a larger block only seals
better, cf. `sealed_upto_iff`).  The reported value is `0.50 m`. -/
theorem candidateSide_ceiling_cm : ⌈candidateSide * 100⌉₊ = 50 := by
  obtain ⟨hlo, hhi⟩ := candidateSide_bounds
  have h49 : ((49 : ℕ) : ℝ) < candidateSide * 100 := by
    have h : (49 : ℝ) < candidateSide * 100 := by linarith
    exact_mod_cast h
  have h50 : candidateSide * 100 ≤ ((50 : ℕ) : ℝ) := by
    have h : candidateSide * 100 ≤ (50 : ℝ) := by linarith
    exact_mod_cast h
  have h1 : (49 : ℕ) < ⌈candidateSide * 100⌉₊ := Nat.lt_ceil.mpr h49
  have h2 : ⌈candidateSide * 100⌉₊ ≤ 50 := Nat.ceil_le.mpr h50
  omega

end IPhO2026.T1A1
