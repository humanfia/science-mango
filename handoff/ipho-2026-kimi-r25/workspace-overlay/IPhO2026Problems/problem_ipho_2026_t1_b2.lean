import Mathlib

open Real Filter InnerProductGeometry
open scoped InnerProductSpace RealInnerProductSpace Topology

/-!
# IPhO 2026, Theory problem T1-B2 — the unbound electron–positron pair (`μ = 15/2`)

## Problem-side summary (source: T1 page 2, figure 1b)

A positron `e⁺` and an electron `e⁻`, each of mass `m`, with charges of equal
magnitude `e` and opposite sign, are at one instant separated by `100·a₀`. Their
velocities are antiparallel and perpendicular to the separation line (figure 1b:
`e⁺` above moving right, `e⁻` below moving left, separation vertical). Each
particle has angular momentum of magnitude `μ·ℏ` about the system's center of
mass, with `μ` a dimensionless factor. The system is isolated, classical,
non-relativistic, and interacts only electrostatically. The problem defines
`a₀ = 4πε₀ℏ²/(m e²)` (Bohr radius) and `k = 1/(4πε₀)` (Coulomb's constant), and
supplies two hints:

* **Hint 1.** the eccentricity of the conic trajectory is
  `ε = √(1 + 4L²E/(k²e⁴m))`, with `E` the total energy and `L` the magnitude of
  the total angular momentum;
* **Hint 2.** a conic in polar coordinates is `r = a/(1 − ε cos θ)`.

**Subquestion T1-B2.** For `μ = 15/2` the pair is unbound. With `u⃗∞` the velocity
of `e⁺` relative to `e⁻` as the separation tends to infinity, find the angle
between `u⃗∞` and the initial line of motion of `e⁺`, in degrees.

## Candidate derived from problem-side evidence only (answer-blind)

* Equal-magnitude angular momenta about the center of mass plus antiparallel
  velocities force `v⃗₋(0) = −v⃗₊(0)`; hence `u⃗(0) = 2v⃗₊(0)` is parallel to the
  initial line of motion of `e⁺`, and `m·(100a₀/2)·‖v⃗₊(0)‖ = μℏ`.
* With `k e² = ℏ²/(m a₀)`: the total energy evaluates to
  `E = ℏ²(μ² − 25)/(2500 m a₀²)` and the total angular momentum to `L = 2μℏ`.
* Hint 1 then gives `ε = √(1 + 16μ²(μ² − 25)/2500)`; at `μ = 15/2`,
  `ε = √(49/4) = 7/2` (and `E = ℏ²/(80 m a₀²) > 0`, consistent with unbound).
* The initial instant is an apsis (`r⃗(0) ⊥ u⃗(0)`); on the unbound orbit it is the
  periapsis, so Hint 2's axis is `e₀ = −r̂(0)` and `a = 100a₀·(1 + ε) = 450 a₀`.
* The outgoing asymptote satisfies `1 − ε⟨e₀, r̂∞⟩ = 0`, i.e. the undirected angle
  from `e₀` to `u⃗∞ ∥ r̂∞` is `arccos (2/7)`; since `v⃗₊(0) ⊥ e₀` and the outgoing
  branch keeps a positive component along `u⃗(0)`, the requested angle is
  `π/2 − arccos (2/7) = arcsin (2/7) ≈ 16.60°`.

## Declarations

* `Constants`, `Constants.coulombK`, `Constants.bohrRadius` — physical constants
  and the two defining relations of the problem statement.
* `PairMotion` and derived coordinates (`relPos`, `relVel`, `cmPos`, `cmVel`).
* `CoulombKeplerLaws` — governing-law package: Newton's second law with the
  Coulomb attraction, the conserved energy and angular momentum of the relative
  motion, the conic orbit and eccentricity exactly as given by Hints 1–2, and
  the unbound-escape facts of the subquestion (separation → ∞, `u⃗∞` exists).
* `InitialData` — the instant data of the problem and figure 1b.
* Bridge lemmas evaluating `E`, `L`, `ε`, the periapsis geometry, and the
  asymptote direction; main theorem `angle_uInfinity_initial_positron_motion`
  (blueprint label `thm:physics:ipho_2026_t1_b2:target`) with the degree form
  and certified decimal bounds.
-/

namespace IPhO2026.T1B2

/-- The orbital plane of the pair: central-force motion is planar, and all motion
takes place in the plane of figure 1b. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The out-of-plane scalar component of the planar wedge product,
`planeWedge x y = x₀ y₁ − x₁ y₀`. Masses times wedges of positions and velocities
are the signed angular momenta (about the origin/center of mass) used below. -/
def planeWedge (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

/-! ## Physical constants -/

/-- The physical constants of the problem: the common mass `m` of `e±`, the
elementary charge `e` (the magnitude of each charge), the reduced Planck
constant `ℏ`, and the vacuum permittivity `ε₀`. Coulomb's constant `k` and the
Bohr radius `a₀` are the derived constants `Constants.coulombK` and
`Constants.bohrRadius` defined by the relations given in the problem statement. -/
structure Constants where
  /-- the common mass `m` of the positron and the electron -/
  mass : ℝ
  /-- the elementary charge `e`; the particles carry `+e` and `-e` -/
  charge : ℝ
  /-- the reduced Planck constant `ℏ` -/
  hbar : ℝ
  /-- the vacuum permittivity `ε₀` -/
  permittivity : ℝ
  mass_pos : 0 < mass
  charge_pos : 0 < charge
  hbar_pos : 0 < hbar
  permittivity_pos : 0 < permittivity

namespace Constants

/-- Coulomb's constant `k = 1/(4πε₀)`, as defined in the problem statement. -/
noncomputable def coulombK (c : Constants) : ℝ := 1 / (4 * π * c.permittivity)

/-- The Bohr radius `a₀ = 4πε₀ℏ²/(m e²)`, as defined in the problem statement. -/
noncomputable def bohrRadius (c : Constants) : ℝ :=
  4 * π * c.permittivity * c.hbar ^ 2 / (c.mass * c.charge ^ 2)

lemma coulombK_pos (c : Constants) : 0 < c.coulombK := by
  have hε := c.permittivity_pos
  rw [coulombK]
  positivity

lemma bohrRadius_pos (c : Constants) : 0 < c.bohrRadius := by
  have hm := c.mass_pos
  have he := c.charge_pos
  have hh := c.hbar_pos
  have hε := c.permittivity_pos
  rw [bohrRadius]
  positivity

/-- The Bohr radius in terms of `k`: `a₀ = ℏ²/(k m e²)` (from `k = 1/(4πε₀)`). -/
lemma bohrRadius_eq (c : Constants) :
    c.bohrRadius = c.hbar ^ 2 / (c.coulombK * c.mass * c.charge ^ 2) := by
  have hm : c.mass ≠ 0 := ne_of_gt c.mass_pos
  have he : c.charge ≠ 0 := ne_of_gt c.charge_pos
  have hε : c.permittivity ≠ 0 := ne_of_gt c.permittivity_pos
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  rw [bohrRadius, coulombK]
  field_simp

/-- The working form of the Coulomb coupling, `k e² = ℏ²/(m a₀)`. -/
lemma coulombK_mul_charge_sq (c : Constants) :
    c.coulombK * c.charge ^ 2 = c.hbar ^ 2 / (c.mass * c.bohrRadius) := by
  have hm : c.mass ≠ 0 := ne_of_gt c.mass_pos
  have he : c.charge ≠ 0 := ne_of_gt c.charge_pos
  have hh : c.hbar ≠ 0 := ne_of_gt c.hbar_pos
  have hε : c.permittivity ≠ 0 := ne_of_gt c.permittivity_pos
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  rw [bohrRadius, coulombK]
  field_simp

end Constants

/-! ## The motion of the pair and the two-body coordinates -/

/-- A planar motion of the positron–electron pair: twice continuously
differentiable position functions of time `t`, where `t = 0` is the instant
described in the problem statement (figure 1b). -/
structure PairMotion where
  /-- position of the positron `e⁺` -/
  positron : ℝ → Plane
  /-- position of the electron `e⁻` -/
  electron : ℝ → Plane
  positron_smooth : ContDiff ℝ 2 positron
  electron_smooth : ContDiff ℝ 2 electron

namespace PairMotion

/-- The separation vector `r⃗(t) = r⃗₊(t) − r⃗₋(t)` (pointing from `e⁻` to `e⁺`). -/
def relPos (P : PairMotion) (t : ℝ) : Plane := P.positron t - P.electron t

/-- The relative velocity `u⃗(t) = v⃗₊(t) − v⃗₋(t)`: the velocity of `e⁺` relative
to `e⁻`. The `u⃗∞` of the problem is the limit of this function as `t → ∞`. -/
noncomputable def relVel (P : PairMotion) (t : ℝ) : Plane :=
  deriv P.positron t - deriv P.electron t

/-- The center-of-mass position `R⃗(t) = (r⃗₊(t) + r⃗₋(t))/2` (equal masses). -/
noncomputable def cmPos (P : PairMotion) (t : ℝ) : Plane := (1 / 2 : ℝ) • (P.positron t + P.electron t)

/-- The center-of-mass velocity `V⃗(t) = (v⃗₊(t) + v⃗₋(t))/2` (equal masses). -/
noncomputable def cmVel (P : PairMotion) (t : ℝ) : Plane :=
  (1 / 2 : ℝ) • (deriv P.positron t + deriv P.electron t)

end PairMotion

/-! ## Governing laws -/

/-- **Governing-law package** for the isolated, classical, non-relativistic
electron–positron system whose only interaction is the electrostatic (Coulomb)
attraction, together with the orbital facts supplied by the problem statement.

The package contains:

* Newton's second law for each particle with the Coulomb attraction
  `F = k e²/r²` (`newton_positron`, `newton_electron`) — the fundamental
  dynamics ("classical and non-relativistic … only interaction … electrostatic");
* the two first integrals of the relative motion `r⃗ = r⃗₊ − r⃗₋` (reduced mass
  `m/2`): the conserved energy `E` (`energy_eq`, equal to the total energy of the
  pair since the center of mass is at rest) and the conserved signed angular
  momentum `L` (`angMom_eq`, the total angular momentum about the center of mass);
* the orbit geometry given by the problem's hints: the trajectory is the conic
  `r = a/(1 − ε cos θ)` of Hint 2, written in the vector form
  `‖r⃗‖ = a + ε⟨e₀, r⃗⟩` with `a > 0` and a unit reference direction `e₀`
  (`conic_eq`, `semiLatus_pos`, `axis_unit`), and the eccentricity is given by
  Hint 1, `ε = √(1 + 4L²E/(k²e⁴m))` (`eccentricity_eq`);
* the unbound-escape facts of this subquestion: the separation tends to infinity
  (`escape`, "the system is unbound … as the separation distance between them
  tends to infinity") and the relative velocity has a limit `u⃗∞`
  (`uInfinity_tendsto`, the problem's "let `u⃗∞` be the velocity of `e⁺` relative
  to `e⁻` as the separation tends to infinity"). -/
structure CoulombKeplerLaws (c : Constants) (P : PairMotion) where
  /-- the conserved total energy `E` of the pair -/
  energy : ℝ
  /-- the conserved signed total angular momentum `L` about the center of mass
  (out-of-plane scalar; `|L|` is the magnitude entering Hint 1) -/
  angMom : ℝ
  /-- the semi-latus rectum `a` of the conic (Hint 2) -/
  semiLatus : ℝ
  /-- the eccentricity `ε` of the conic (Hint 1) -/
  eccentricity : ℝ
  /-- the unit reference direction of the conic's polar axis (`θ = 0` in Hint 2) -/
  axis : Plane
  /-- the asymptotic relative velocity `u⃗∞ = lim_{t → ∞} u⃗(t)` -/
  uInfinity : Plane
  /-- Newton's second law for the positron: `m a⃗₊ = −k e² r⃗/‖r⃗‖³` (attraction
  toward the electron). -/
  newton_positron : ∀ t, c.mass • deriv (deriv P.positron) t =
    (-(c.coulombK * c.charge ^ 2) / ‖P.relPos t‖ ^ 3) • P.relPos t
  /-- Newton's second law for the electron: `m a⃗₋ = +k e² r⃗/‖r⃗‖³` (attraction
  toward the positron). -/
  newton_electron : ∀ t, c.mass • deriv (deriv P.electron) t =
    ((c.coulombK * c.charge ^ 2) / ‖P.relPos t‖ ^ 3) • P.relPos t
  /-- the particles never collide on this orbit (so the force laws are regular) -/
  relPos_ne : ∀ t, P.relPos t ≠ 0
  /-- Conservation of energy: `(m/4)‖u⃗‖² − k e²/‖r⃗‖ = E` for all times. The
  relative-motion energy with reduced mass `m/2`; equals the total energy of the
  pair because the center of mass is at rest (`PairMotion.cmVel_zero`). -/
  energy_eq : ∀ t, (c.mass / 4) * ‖P.relVel t‖ ^ 2
    - c.coulombK * c.charge ^ 2 / ‖P.relPos t‖ = energy
  /-- Conservation of angular momentum: `(m/2)·(r⃗ × u⃗)_z = L` for all times; this
  is the total angular momentum of the pair about the center of mass. -/
  angMom_eq : ∀ t, (c.mass / 2) * planeWedge (P.relPos t) (P.relVel t) = angMom
  /-- the semi-latus rectum is positive -/
  semiLatus_pos : 0 < semiLatus
  /-- the conic's reference direction is a unit vector -/
  axis_unit : ‖axis‖ = 1
  /-- Hint 2 of the problem: the relative orbit is the conic
  `r = a/(1 − ε cos θ)`, equivalently `‖r⃗‖ = a + ε⟨e₀, r⃗⟩`. -/
  conic_eq : ∀ t, ‖P.relPos t‖ = semiLatus + eccentricity * ⟪axis, P.relPos t⟫_ℝ
  /-- Hint 1 of the problem: `ε = √(1 + 4L²E/(k²e⁴m))`. -/
  eccentricity_eq : eccentricity =
    Real.sqrt (1 + 4 * angMom ^ 2 * energy / (c.coulombK ^ 2 * c.charge ^ 4 * c.mass))
  /-- the pair is unbound (given for `μ = 15/2`): the separation tends to
  infinity in forward time -/
  escape : Tendsto (fun t => ‖P.relPos t‖) atTop atTop
  /-- the relative velocity has the limit `u⃗∞` as the separation tends to
  infinity (forward in time) -/
  uInfinity_tendsto : Tendsto P.relVel atTop (𝓝 uInfinity)

/-! ## The initial instant (problem data and figure 1b) -/

/-- The data of the initial instant `t = 0` (problem statement and figure 1b):
the separation is `100 a₀`, the velocities are antiparallel and perpendicular to
the separation line, nonzero, and each particle has angular momentum of
magnitude `μ·ℏ` with respect to the system's center of mass (the midpoint, the
masses being equal). -/
structure InitialData (c : Constants) (P : PairMotion) (mu : ℝ) : Prop where
  /-- initial separation `‖r⃗(0)‖ = 100 a₀` (figure 1b) -/
  separation : ‖P.relPos 0‖ = 100 * c.bohrRadius
  /-- the velocities are antiparallel: `v⃗₋(0) = −s·v⃗₊(0)` for some `s > 0` -/
  v_antiparallel : ∃ s : ℝ, 0 < s ∧ deriv P.electron 0 = (-s) • deriv P.positron 0
  /-- the velocities are perpendicular to the separation line (figure 1b);
  stated for the positron, the electron's perpendicularity follows from
  `v_antiparallel` -/
  v_perpendicular : ⟪deriv P.positron 0, P.relPos 0⟫_ℝ = 0
  /-- the positron is actually moving (figure 1b) -/
  v_positron_ne : deriv P.positron 0 ≠ 0
  /-- angular momentum of the positron about the center of mass:
  `|m ((r⃗₊ − R⃗) × v⃗₊)_z| = μℏ` with `r⃗₊ − R⃗ = r⃗/2` -/
  angMom_positron :
    |c.mass * planeWedge ((1 / 2 : ℝ) • P.relPos 0) (deriv P.positron 0)| = mu * c.hbar
  /-- angular momentum of the electron about the center of mass:
  `|m ((r⃗₋ − R⃗) × v⃗₋)_z| = μℏ` with `r⃗₋ − R⃗ = −r⃗/2` -/
  angMom_electron :
    |c.mass * planeWedge ((1 / 2 : ℝ) • (-P.relPos 0)) (deriv P.electron 0)| = mu * c.hbar

variable {c : Constants} {P : PairMotion}

/-! ## Bridge lemmas: initial kinematics -/

/-- From "velocities antiparallel" and "each particle has angular momentum `μℏ`
about the center of mass": the velocities are in fact opposite,
`v⃗₋(0) = −v⃗₊(0)`. (With `v⃗₋(0) = −s·v⃗₊(0)` one computes `|L₋| = s·|L₊|`, and
`|L₊| = |L₋| = μℏ ≠ 0` — nonzero because `v⃗₊(0) ≠ 0`, `r⃗(0) ≠ 0` and
`v⃗₊(0) ⊥ r⃗(0)` — forces `s = 1`.) -/
theorem electron_velocity_neg {mu : ℝ} (ic : InitialData c P mu) :
    deriv P.electron 0 = -deriv P.positron 0 := by
  sorry

/-- The center of mass is initially at rest (equal masses, opposite velocities);
as the system is isolated it remains at rest, so the given frame is the
center-of-mass frame. -/
theorem cmVel_zero {mu : ℝ} (ic : InitialData c P mu) :
    P.cmVel 0 = 0 := by
  sorry

/-- The initial relative velocity is twice the positron velocity,
`u⃗(0) = 2·v⃗₊(0)`; in particular it is parallel to the initial line of motion
of `e⁺`. -/
theorem relVel_zero {mu : ℝ} (ic : InitialData c P mu) :
    P.relVel 0 = 2 • deriv P.positron 0 := by
  sorry

/-- The initial relative velocity is perpendicular to the initial separation
(figure 1b): the initial instant is an apsis (extremum of `‖r⃗‖`) of the
relative orbit. -/
theorem relPos_relVel_orthogonal {mu : ℝ} (ic : InitialData c P mu) :
    ⟪P.relPos 0, P.relVel 0⟫_ℝ = 0 := by
  sorry

/-- The initial speed of the positron from the angular-momentum datum:
`m·(100a₀/2)·‖v⃗₊(0)‖ = μℏ`, using `v⃗₊(0) ⊥ r⃗(0)` and
`|r⃗₊(0) − R⃗| = ‖r⃗(0)‖/2 = 50 a₀`. -/
theorem initial_speed {mu : ℝ} (ic : InitialData c P mu) :
    c.mass * (100 * c.bohrRadius / 2) * ‖deriv P.positron 0‖ = mu * c.hbar := by
  sorry

/-! ## Bridge lemmas: the conserved quantities evaluated on the initial data -/

/-- The conserved total energy, evaluated at `t = 0`:
`E = m‖v⃗₊(0)‖² − k e²/(100a₀) = ℏ²(μ² − 25)/(2500 m a₀²)`,
using `u⃗(0) = 2v⃗₊(0)`, the angular-momentum datum, and `k e² = ℏ²/(m a₀)`. -/
theorem energy_value (laws : CoulombKeplerLaws c P) {mu : ℝ} (ic : InitialData c P mu) :
    laws.energy = c.hbar ^ 2 * (mu ^ 2 - 25) / (2500 * c.mass * c.bohrRadius ^ 2) := by
  sorry

/-- The conserved total angular momentum is twice the single-particle angular
momentum, `L = 2 m ((r⃗(0)/2) × v⃗₊(0))_z`. -/
theorem angMom_value (laws : CoulombKeplerLaws c P) {mu : ℝ} (ic : InitialData c P mu) :
    laws.angMom =
      2 * (c.mass * planeWedge ((1 / 2 : ℝ) • P.relPos 0) (deriv P.positron 0)) := by
  sorry

/-- The squared total angular momentum, `L² = 4μ²ℏ²` (the combination entering
Hint 1). -/
theorem angMom_sq (laws : CoulombKeplerLaws c P) {mu : ℝ} (ic : InitialData c P mu) :
    laws.angMom ^ 2 = 4 * (mu * c.hbar) ^ 2 := by
  sorry

/-! ## Bridge lemmas: the orbit for `μ = 15/2` -/

/-- For `μ = 15/2` the total energy is positive — `E = ℏ²/(80 m a₀²) > 0` —
consistent with the given fact that the pair is unbound. -/
theorem energy_pos (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    0 < laws.energy := by
  sorry

/-- The eccentricity from Hint 1 at `μ = 15/2`: with `L² = 4μ²ℏ²`,
`E = ℏ²(μ² − 25)/(2500 m a₀²)` and `k²e⁴m = ℏ⁴/(m a₀²)` one gets
`ε = √(1 + 16μ²(μ² − 25)/2500) = √(49/4) = 7/2`. -/
theorem eccentricity_value (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    laws.eccentricity = 7 / 2 := by
  sorry

/-- The initial instant is the *periapsis* of the hyperbola: the conic's
reference axis (`θ = 0` in Hint 2) points opposite to the initial separation,
`e₀ = −r̂(0)`. Indeed, differentiating Hint 2's `‖r⃗‖ = a + ε⟨e₀, r⃗⟩` at the
apsis `t = 0` gives `⟨e₀, u⃗(0)⟩ = 0`, so in the orbital plane `e₀ = ±r̂(0)`;
the `+` sign would force `a = 100a₀·(1 − ε) < 0` (since `ε = 7/2 > 1`),
contradicting `a > 0`. -/
theorem axis_eq_neg_relPos0 (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    laws.axis = (-(‖P.relPos 0‖)⁻¹) • P.relPos 0 := by
  sorry

/-- The semi-latus rectum of the conic: evaluating Hint 2 at the periapsis,
`a = 100a₀·(1 + ε) = 450 a₀`. -/
theorem semiLatus_value (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    laws.semiLatus = 450 * c.bohrRadius := by
  sorry

/-! ## Bridge lemmas: the outgoing asymptote -/

/-- The asymptotic relative velocity is nonzero: by energy conservation
`(m/4)‖u⃗∞‖² = E > 0`, the potential energy dying out at infinite separation. -/
theorem uInfinity_ne (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    laws.uInfinity ≠ 0 := by
  sorry

/-- Asymptote direction: as `‖r⃗‖ → ∞`, Hint 2's `1 = a/‖r⃗‖ + ε⟨e₀, r̂⟩` forces
`⟨e₀, r̂⟩ → 1/ε`, and `u⃗∞` is parallel to that limiting direction (the transverse
component `L/((m/2)‖r⃗‖)` of the velocity dies out while the radial component
tends to `√(4E/m) > 0`), hence `⟨e₀, u⃗∞⟩ = ‖u⃗∞‖/ε`. -/
theorem inner_axis_uInfinity (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    ⟪laws.axis, laws.uInfinity⟫_ℝ = (1 / laws.eccentricity) * ‖laws.uInfinity‖ := by
  sorry

/-- Outgoing-branch orientation: `u⃗∞` keeps a positive component along the
initial relative velocity `u⃗(0) = 2v⃗₊(0)`. The transverse motion never reverses,
because the conserved angular momentum is nonzero, so the polar angle sweeps
monotonically from the periapsis (`106.6°` before the asymptote) to the outgoing
asymptote; this selects the outgoing branch of the asymptote line. -/
theorem inner_uInfinity_relVel0_pos (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    0 < ⟪laws.uInfinity, P.relVel 0⟫_ℝ := by
  sorry

/-- The undirected angle between `u⃗∞` and the conic's reference axis is
`arccos (1/ε) = arccos (2/7)`. -/
theorem angle_uInfinity_axis (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    angle laws.uInfinity laws.axis = Real.arccos (2 / 7) := by
  sorry

/-- The initial positron velocity is perpendicular to the conic's reference axis
(it is perpendicular to the separation, which is antiparallel to the axis). -/
theorem axis_inner_vPositron0 (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    ⟪laws.axis, deriv P.positron 0⟫_ℝ = 0 := by
  sorry

/-! ## Main result -/

/-- **Main result (T1-B2)** — blueprint `thm:physics:ipho_2026_t1_b2:target`.
For `μ = 15/2` the angle between the asymptotic relative velocity `u⃗∞` (the
velocity of `e⁺` relative to `e⁻` as the separation tends to infinity) and the
initial line of motion of `e⁺` is `arcsin (2/7)` radians.

With `⟨e₀, û∞⟩ = 2/7` and `v⃗₊(0) ⊥ e₀` in the orbital plane, the component of
`û∞` along `v̂₊(0)` has magnitude `√(1 − (2/7)²) = 3√5/7`; the outgoing-branch
orientation (`inner_uInfinity_relVel0_pos`) makes this component positive, so
the undirected angle is `arccos (3√5/7) = arcsin (2/7)`. -/
theorem angle_uInfinity_initial_positron_motion (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    angle laws.uInfinity (deriv P.positron 0) = Real.arcsin (2 / 7) := by
  sorry

/-- The answer in degrees, as requested by the problem: the angle is
`(180/π)·arcsin(2/7)` degrees. -/
theorem angle_uInfinity_initial_positron_motion_degrees
    (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    angle laws.uInfinity (deriv P.positron 0) * (180 / π) =
      Real.arcsin (2 / 7) * (180 / π) := by
  sorry

/-- Decimal readout of the degree answer: approximately `16.60°`. The source
states no explicit rounding rule, so the exact closed form
`(180/π)·arcsin(2/7)` above is the derived candidate; these bounds certify its
leading decimals. -/
theorem angle_degrees_numeric_bounds :
    Real.arcsin (2 / 7) * (180 / π) ∈ Set.Ioo 16.60 16.61 := by
  sorry

end IPhO2026.T1B2
