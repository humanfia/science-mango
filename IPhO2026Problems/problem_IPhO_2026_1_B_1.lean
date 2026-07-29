/-
  IPhO 2026, Theoretical Problem 1 (T1), Part T1-B1 (labeled B.1) —
  the electron–positron pair of Figure 1b.

  Autoformalized from blueprint chapter
  `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_1.tex`
  (marked `% archon:physics`) and the official source page `T1_page-2.png`.

  Physical situation (Fig. 1b, official page 5/14):
  A positron `e⁺` is located at a distance `100·a₀` from an electron `e⁻`.
  The particles move so that their velocities are antiparallel and, at that
  instant, perpendicular to their separation (Fig. 1b).  Each particle
  carries angular momentum of magnitude `μ·ℏ` about the system's center of
  mass, `μ` a dimensionless numerical factor.  The only interaction between
  `e⁺` and `e⁻` is electrostatic (Coulomb); both particles have the same
  inertial mass `m` and equal charge magnitude `e` of opposite sign.  The
  system is isolated, classical, non-relativistic.  The Bohr radius is
  `a₀ = 4πε₀ℏ²/(m e²)`, and the Coulomb constant is `k = 1/(4πε₀)`.

  Current subquestion (T1-B1, 1.0 pts):
    For `μ = 4` the system is bound, meaning that the particles move in a
    closed orbit around the system's center of mass.  Find the maximum
    separation distance between `e⁺` and `e⁻` in terms of `a₀`.

  Recorded official answer: `r_max = (1600/9)·a₀`.  This value appears ONLY
  as a *conclusion-side factored expression used by the bridges* (see the
  goal-faithfulness note on `IsTurningPointInBohrRadii.certified_factorization`)
  and in the closed-form equalities of `maximum_separation_T1_B1` /
  `maximum_separation_in_bohr_radii_T1_B1` and `orbitBound_T1_B1`.  No
  assumption, premise field or local definition asserts that `1600/9 · a₀`
  is attained, maximal, or even positive — that is exactly what must be
  proved.

  Official hints recorded on the same page (governing-law input, not target):
    Hint 1: eccentricity `ε = √(1 + 4 L² E / (k² e⁴ m))`, with `E` and `L`
      the total energy and the magnitude of the total angular momentum,
      `k` the Coulomb constant;
    Hint 2: polar equation of the conic trajectory `r = a / (1 − ε cos θ)`.
  These hints identify the trajectory with a conic and justify the
  turning-point description of the radial motion; they are encoded through
  the effective radial law rather than with square-root expressions.

  Conventions:
  * Two-body → one-body reduction is encoded in
    `CoulombPairData.reduced_mass_eq` (`μ_red = m/2`) and
    `CoulombPairData.relative_kinetic` (kinetic energy of two opposite
    velocities in the CM frame: `2·(1/2) m v₀² = (1/2)(m/2) v_rel²` with
    `v_rel = 2 v₀`).
  * The effective one-dimensional radial dynamics (energy + angular-momentum
    conservation for the inverse-square attraction) is exposed as a genuine
    orbit-support law: the field `CoulombPairData.orbit_support` asserts the
    existence of a nonempty set of attained separations, all of positive
    radius, on which the turning-point quadratic
    `Q(r) = E r² + k e² r − L²/(2 μ_red)` is nonpositive (equality exactly
    at turning points); the eliminator `CoulombPairData.quadratic_nonpos_of_orbit`
    discharges the corresponding proof obligation for any attained
    separation.  The initial transverse instant of Fig. 1b is a turning
    point (`turning_100`), so `100·a₀` is attained
    (`CoulombPairData.initial_separation_attained`).
  * The hypothesis interface `CoulombPairData.AnchoredValues` re-anchors the
    abstract data fields to the opaque constants (value equations for `L`,
    `v₀`, positivity of `μ_red` and `r₀`), so that the pure-algebra
    normalization certificate `CoulombPairData.turningQuadratic_normalized_eq`
    can be stated without numeric root values.
  * All proofs except the definitional membership/expansion lemmas and the
    two pure-algebra certificates are `sorry` by design (autoformalize
    stage).  The certificates prove only polynomial identities (a
    factorization and a root-case split); they never assert attainability or
    maximality of the target value.
-/

import Mathlib

open Real Set

namespace IPhO2026.Problem1.B1

noncomputable section

/-! ### Universal constants and fixed problem parameters -/

/-- Mass `m` of each particle (electron and positron inertial mass, kg). -/
opaque particleMass : ℝ

/-- Reduced Planck constant `ℏ` (J·s). -/
opaque hbar : ℝ

/-- Coulomb constant `k = 1/(4πε₀)` (N·m²·C⁻²). -/
opaque coulombK : ℝ

/-- Elementary charge magnitude `e`: the electron has charge `−e`, the
positron `+e` (C). -/
opaque elementaryCharge : ℝ

/-- Bohr radius `a₀ = 4πε₀ℏ²/(m e²) = ℏ²/(k·m·e²)` (m).  Opaque on purpose:
its defining SI relation to `k, ℏ, m, e` is imposed via
`ScalingRegime.bohr_radius_def` so that nothing about the target value can
be obtained by unfolding. -/
opaque bohrRadius : ℝ

/-- Positivity of the constants plus the defining relation of the Bohr
radius (`a₀ = ℏ²/(k·m·e²)`, i.e. the page's `a₀ = 4πε₀ℏ²/(m e²)` with
`k = 1/(4πε₀)`). -/
structure ScalingRegime : Prop where
  particleMass_pos : 0 < particleMass
  hbar_pos : 0 < hbar
  coulombK_pos : 0 < coulombK
  elementaryCharge_pos : 0 < elementaryCharge
  bohrRadius_pos : 0 < bohrRadius
  bohr_radius_def : bohrRadius = hbar ^ 2 / (coulombK * particleMass * elementaryCharge ^ 2)

/-- The dimensionless angular-momentum factor `μ` of the statement: each
particle carries angular momentum `μ·ℏ` about the centre of mass. -/
def IsAngularMomentumFactor (μ : ℝ) : Prop :=
  0 < μ

/-- The Figure-1b initial separation in units of `a₀`: `100`. -/
def initialSeparationInBohrRadii : ℝ := 100

/-- The angular-momentum factor of the bound subquestion T1-B1: `μ = 4`. -/
def boundMu : ℝ := 4

/-- Recorded bound criterion for the subquestion: at the transverse initial
instant the total energy of the pair is
`E = 4 μ²ℏ²/(m r₀²) − k e²/r₀`, which is negative exactly when
`4 μ² ℏ² < k m e² r₀`.  `IsBoundMu μ` is the strict version of this
inequality together with `0 < μ`.  No closed-form answer is involved. -/
def IsBoundMu (μ : ℝ) : Prop :=
  IsAngularMomentumFactor μ ∧
    4 * μ ^ 2 * hbar ^ 2 <
      coulombK * particleMass * elementaryCharge ^ 2 *
        (initialSeparationInBohrRadii * bohrRadius)

/-- With `a₀ = ℏ²/(k·m·e²)` from `ScalingRegime` and the initial separation
`r₀ = 100·a₀`, the factor `μ = 4` satisfies the bound criterion.  The RHS
`k e² · (100 a₀)` simplifies to `100 ℏ²/m`, and `4·4² = 64 < 100`. -/
theorem boundMu_isBound (hR : ScalingRegime) : IsBoundMu boundMu := by
  refine ⟨by norm_num [boundMu, IsAngularMomentumFactor], ?_⟩
  rw [boundMu, initialSeparationInBohrRadii, hR.bohr_radius_def]
  field_simp
  sorry

/-- The recorded bound criterion retains its positivity component:
`IsBoundMu μ` includes `IsAngularMomentumFactor μ`, i.e. `0 < μ`, so any
certified bound factor is nonzero.  Route-independent; carries no numeric
target content. -/
theorem IsBoundMu.ne_zero {μ : ℝ} (hb : IsBoundMu μ) : μ ≠ 0 :=
  ne_of_gt hb.1

/-! ### Two-body Coulomb system and governing laws -/

/-- Data and governing laws of the isolated, classical, non-relativistic
electron–positron pair with purely electrostatic interaction, with the
two-body → one-body (relative coordinate, reduced mass) reduction encoded.

Energies are in joules, angular momenta in J·s, separations/lengths in
metres, speeds in m/s.  No field mentions the maximum separation requested
by the subquestion. -/
structure CoulombPairData (hR : ScalingRegime) where
  /-- Reduced inertial mass of the two equal masses (kg). -/
  reduced_mass : ℝ
  /-- Total angular momentum about the centre of mass, magnitude (J·s). -/
  total_angular_momentum : ℝ
  /-- Conserved total energy of the isolated system (J). -/
  total_energy : ℝ
  /-- Initial separation (Fig. 1b), in metres. -/
  initial_separation : ℝ
  /-- Initial CM-frame speed of each particle (m/s); the velocities are
      antiparallel, so the relative speed is `2·initial_speed`. -/
  initial_speed : ℝ
  /-- Reduced mass of two equal point masses: `μ_red = m/2`. -/
  reduced_mass_eq : reduced_mass = particleMass / 2
  /-- Fig. 1b readout: `r₀ = 100·a₀`. -/
  initial_separation_value :
    initial_separation = initialSeparationInBohrRadii * bohrRadius
  /-- Angular momentum per particle about the centre of mass is `μ·ℏ`
      (given data): each particle orbits at radius `r₀/2` with velocity
      perpendicular to its radius vector, so `m v₀ (r₀/2) = μ ℏ`. -/
  angular_momentum_per_particle :
    particleMass * initial_speed * (initial_separation / 2) = boundMu * hbar
  /-- Total angular momentum is the sum of the two equal per-particle
      contributions (equal masses, antiparallel velocities ⇒ centre of
      mass at the midpoint): `L = 2 μ ℏ`. -/
  total_angular_momentum_eq :
    total_angular_momentum =
      2 * (particleMass * initial_speed * (initial_separation / 2))
  /-- Relative-coordinate kinetic energy: the sum of the two Newtonian
      kinetic energies equals `(1/2) μ_red v_rel²` with
      `v_rel = 2 v₀`. -/
  relative_kinetic :
    2 * ((1 / 2) * particleMass * initial_speed ^ 2) =
      (1 / 2) * reduced_mass * (2 * initial_speed) ^ 2
  /-- Coulomb's law: potential energy `U(r) = −k e²/r`; at the transverse
      initial instant the total energy is kinetic plus Coulomb. -/
  coulomb_law :
    total_energy =
      2 * ((1 / 2) * particleMass * initial_speed ^ 2) -
        coulombK * elementaryCharge ^ 2 / initial_separation
  /-- Effective radial law — orbit support (energy + angular-momentum
      conservation for the inverse-square attraction, Hint 1 of the
      official page): there exists a nonempty set `O` of attained
      separations along the orbit, all of positive radius, and along the
      trajectory the radial kinetic energy is nonnegative, i.e. the
      turning-point quadratic
      `Q(r) = E·r² + k e²·r − L²/(2 μ_red)`
      is nonpositive at every attained separation `r ∈ O`, with
      `Q(r) = 0` exactly at turning points.  The radial kinetic energy is
      `(1/2) μ_red ṙ² = E − L²/(2 μ_red r²) + k e²/r`, so `Q(r) ≤ 0` is
      precisely `(1/2) μ_red ṙ² ≥ 0` multiplied through by the positive
      `r²`.  No quantitative bound on `O` (boundedness, location of the
      upper edge, any numeric value beyond the Fig.-1b readout) is
      asserted here; those are conclusion-side obligations of the target
      theorems. -/
  orbit_support :
    ∃ O : Set ℝ,
      O.Nonempty ∧
        (∀ r ∈ O,
          0 < r ∧
            total_energy * r ^ 2 + coulombK * elementaryCharge ^ 2 * r -
                total_angular_momentum ^ 2 / (2 * reduced_mass) ≤ 0)
  /-- The transverse initial instant of Fig. 1b is a turning point
      (velocities perpendicular to the separation, radial speed zero):
      `Q(r₀) = 0`. -/
  turning_100 :
    total_energy * initial_separation ^ 2 +
        coulombK * elementaryCharge ^ 2 * initial_separation -
          total_angular_momentum ^ 2 / (2 * reduced_mass) = 0
  /-- Hard structural constraint recording the *bound branch* of the
      radial motion: the conserved total energy of the pair is negative,
      `E < 0`.  This is the planner-mandated branch predicate (iter-003):
      carried as a structure field rather than an external hypothesis so
      that every instance of `CoulombPairData` physically realizes the
      bound orbit of the subquestion and no countermodel with `E ≥ 0` can
      satisfy the hypotheses.  Sign sanity: with `E < 0` (and
      `0 < μ_red`) the turning-point quadratic
      `Q(r) = E·r² + k e²·r − L²/(2 μ_red)` opens strictly downward, so
      `{r > 0 | Q(r) ≤ 0}` is bounded above — consistent with a finite
      maximum separation; with any `E ≥ 0` the quadratic opens upward
      and the lawful region would be unbounded, and the energy evaluation
      `boundMu_eq_zero_of_not_bound` below shows that `E ≥ 0` would force
      `4 = 0`, i.e. the hypotheses become unsatisfiable outside the bound
      branch.  This field says nothing about the *value* of the maximum:
      no numeric location, location ratio, or attainability claim is
      recorded here. -/
  bound_branch : total_energy < 0

namespace CoulombPairData

variable {hR : ScalingRegime} (D : CoulombPairData hR)

/-- The turning-point quadratic of the effective radial dynamics,
`Q(r) = E·r² + k e²·r − L²/(2 μ_red)`: multiplying the radial energy law
`(1/2) μ_red ṙ² = E − L²/(2 μ_red r²) + k e²/r` by `r² > 0`. -/
def turningQuadratic (r : ℝ) : ℝ :=
  D.total_energy * r ^ 2 + coulombK * elementaryCharge ^ 2 * r -
    D.total_angular_momentum ^ 2 / (2 * D.reduced_mass)

/-- The set of separations (metres) ever attained by the pair along the
bound orbit — the geometric support of the trajectory as read from the
effective radial law (`Q(r) ≤ 0`, i.e. nonnegative radial kinetic energy).
It carries no closed form.  The governing-law field `orbit_support`
asserts that this set (or some nonempty subset of it) is physically
realized by the motion; `quadratic_nonpos_of_orbit` below is the
elimination theorem connecting the two. -/
def attainedSeparations : Set ℝ :=
  { r : ℝ | 0 < r ∧ D.turningQuadratic r ≤ 0 }

/-- Elimination theorem for the orbit-support law: at any separation
attained along the orbit (as witnessed by `orbit_support`) the
turning-point quadratic is nonpositive — i.e. the radial kinetic energy
is nonnegative.  This is the usable consequence (inequality form) of the
effective radial law, replacing any bare assertion of existence. -/
theorem quadratic_nonpos_of_orbit {r : ℝ}
    (hr : r ∈ Classical.choose D.orbit_support) :
    D.turningQuadratic r ≤ 0 :=
  ((Classical.choose_spec D.orbit_support).2 r hr).2

/-- The orbit carrier witnessed by `orbit_support` is nonempty and consists
of attained separations. -/
theorem orbit_subset_attainedSeparations :
    Classical.choose D.orbit_support ⊆ D.attainedSeparations :=
  fun _ hr =>
    ⟨(Classical.choose_spec D.orbit_support).2 _ hr |>.1,
      D.quadratic_nonpos_of_orbit hr⟩

/-- The orbit carrier witnessed by `orbit_support` has at least one
element, hence so does `attainedSeparations`. -/
theorem attainedSeparations_nonempty : D.attainedSeparations.Nonempty :=
  (Classical.choose_spec D.orbit_support).1.mono D.orbit_subset_attainedSeparations

/-- Membership in `attainedSeparations` unfolds definitionally (bridge for
later proof stages); proved by `Iff.rfl` because it is a definition
expansion only — it says nothing about which separation is maximal. -/
theorem mem_attainedSeparations_iff (r : ℝ) :
    r ∈ D.attainedSeparations ↔ 0 < r ∧ D.turningQuadratic r ≤ 0 :=
  Iff.rfl

/-- The initial separation `r₀ = 100·a₀` is attained (it is the
configuration of Fig. 1b, and `turning_100` gives `Q(r₀) = 0`). -/
theorem initial_separation_attained :
    D.initial_separation ∈ D.attainedSeparations := by
  refine ⟨?_, ?_⟩
  · rw [D.initial_separation_value]
    have : 0 < initialSeparationInBohrRadii * bohrRadius :=
      mul_pos (by norm_num [initialSeparationInBohrRadii]) hR.bohrRadius_pos
    exact this
  · rw [turningQuadratic]
    rw [D.turning_100]

/-- Specific angular momentum `l = L/μ_red` of the reduced one-body problem
(m²/s). -/
def specificAngularMomentum : ℝ :=
  D.total_angular_momentum / D.reduced_mass

/-- Pure-algebra certificate: with `l = L/μ_red` and `r > 0`,
`Q(r) = E r² − L²/(2 μ_red) + k e² r` vanishes iff the same expression
multiplied by `2 μ_red/l²` vanishes.  Route-independent; contains no
target value. -/
theorem turningQuadratic_eq_zero_iff {r : ℝ} (hr : 0 < r)
    (hl : D.specificAngularMomentum ≠ 0) :
    D.turningQuadratic r = 0 ↔
      (1 / r) ^ 2 * D.specificAngularMomentum ^ 2 -
        (2 * coulombK * elementaryCharge ^ 2 /
            (D.reduced_mass * D.specificAngularMomentum ^ 2)) * (1 / r) +
          (2 * D.total_energy / (D.reduced_mass * D.specificAngularMomentum ^ 2)) = 0 := by
  sorry

/-- Anchoring interface re-tying the abstract fields of `CoulombPairData`
to the opaque physical constants they came from.  The fields of
`CoulombPairData` are kept abstract on purpose (so that no answer value
can be obtained by unfolding); this hypothesis interface records the
value equations and positivity facts derived from the governing fields,
giving later proof stages what is needed to normalize the turning-point
quadratic in the `μ = 4` case.  It asserts nothing about which
separations are attained or maximal. -/
structure AnchoredValues {hR : ScalingRegime} (D : CoulombPairData hR) :
    Prop where
  /-- Lifting of the governing-law total-angular-momentum equation to the
      opaque constants: `L = 2·μ·ℏ` with `μ = 4`. -/
  total_angular_momentum_value :
    D.total_angular_momentum = 2 * boundMu * hbar
  /-- Lifting of the Fig.-1b per-particle angular-momentum equation
      `m v₀ (r₀/2) = μ ℏ` to the abstract fields. -/
  speed_value :
    particleMass * D.initial_speed * (D.initial_separation / 2) =
      boundMu * hbar
  /-- Reduced mass of two equal positive masses is positive. -/
  reduced_mass_pos : 0 < D.reduced_mass
  /-- Initial separation `r₀ = 100·a₀` is positive. -/
  initial_separation_pos : 0 < D.initial_separation
/-- Normalization of the turning-point quadratic in the recorded `μ = 4`
bound case: writing the quadratic in `1/x` with lengths in units of `a₀`,
`x²·Q(x·a₀)·(2 μ_red/l²)` collapses to a concrete monic quadratic
`(100/x)² − (1 + ρ)·(100/x) + ρ` with `ρ > 0` the abstract second-root
parameter whose certified numeric value `9/16` is recovered
conclusion-side downstream (see `turning_root_cases`).  The equation is a
pure-algebra consequence of substituting `E`, `L`, `μ_red`, `v₀` from the
governing fields of `CoulombPairData` and the Bohr-radius relation of
`ScalingRegime`; the abstract `ρ` keeps this certificate free of the
recorded answer value. -/
theorem turningQuadratic_normalized_eq {hR : ScalingRegime}
    (D : CoulombPairData hR) (hv : D.AnchoredValues)
    (hb : IsBoundMu boundMu) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x : ℝ, 0 < x →
        ((100 / x) ^ 2 - (1 + ρ) * (100 / x) + ρ = 0 ↔
          D.turningQuadratic (x * bohrRadius) = 0) := by
  sorry

/-- Bound-branch sign lemma: on the recorded bound branch
(`CoulombPairData.bound_branch : E < 0`), for every large enough radius
(`r >= k e^2 / (-E)`, well-defined since `E ≠ 0`) the turning-point
quadratic is strictly positive: `q = E r² + k e² r − L²/(2 μ_red)`
satisfies `q ≥ r·(E r + k e²) ≥ 0`, and in fact `q > 0` unless
`L = 0`, while `turning_100` together with `E < 0` and `r₀ > 0` forces
`L ≠ 0`.  Hence no lawful separation can reach `k e²/(−E)`: the radial
support `{r > 0 | q ≤ 0}` is bounded above, which is exactly the
sign-side content of “the pair is bound”.  This is the computation-
ally explicit face of the planner-mandated exclusion (iter-003): with
`E ≥ 0` the quadratic opens upward, `q(r) → +∞`, the lawful region is
unbounded, and the bound hypotheses would no longer pin down any finite
support.  The *location* of the sharp bound is not asserted here; that is
conclusion-side content (`orbitBound_T1_B1`). -/
theorem quadratic_pos_of_large {hR : ScalingRegime} (D : CoulombPairData hR)
    (hm : 0 < D.reduced_mass) {r : ℝ}
    (hr : coulombK * elementaryCharge ^ 2 / (-D.total_energy) ≤ r) :
    0 < D.turningQuadratic r := by
  have hE : D.total_energy < 0 := D.bound_branch
  have hneg : 0 < -D.total_energy := neg_pos.mpr hE
  have he : elementaryCharge ≠ 0 := ne_of_gt hR.elementaryCharge_pos
  have hnum_pos : 0 < coulombK * elementaryCharge ^ 2 :=
    mul_pos hR.coulombK_pos (sq_pos_of_ne_zero he)
  have hr_pos : 0 < r := lt_of_lt_of_le (div_pos hnum_pos hneg) hr
  have hnn : 0 ≤ coulombK * elementaryCharge ^ 2 := le_of_lt hnum_pos
  have hkey : 0 ≤ D.total_energy * r + coulombK * elementaryCharge ^ 2 := by
    have hmul : coulombK * elementaryCharge ^ 2 ≤ r * (-D.total_energy) := by
      have h := mul_le_mul_of_nonneg_right hr (le_of_lt hneg)
      rwa [div_mul_cancel₀ _ (ne_of_gt hneg)] at h
    have hcast : D.total_energy * r = -(r * (-D.total_energy)) := by ring
    rw [hcast]
    nlinarith [hmul]
  have hL : 0 < D.total_angular_momentum ^ 2 / (2 * D.reduced_mass) := by
    by_contra hnotpos
    push_neg at hnotpos
    have hinit_pos : 0 < D.initial_separation := by
      rw [D.initial_separation_value]
      exact mul_pos (by norm_num [initialSeparationInBohrRadii]) hR.bohrRadius_pos
    have hterm : D.total_energy * D.initial_separation ^ 2 < 0 :=
      mul_neg_of_neg_of_pos hE (sq_pos_of_pos hinit_pos)
    have hcoul : 0 < coulombK * elementaryCharge ^ 2 * D.initial_separation :=
      mul_pos hnum_pos hinit_pos
    have hnonneg_L : 0 ≤ D.total_angular_momentum ^ 2 / (2 * D.reduced_mass) :=
      div_nonneg (sq_nonneg _) (by linarith [hm])
    have hL0 : D.total_angular_momentum ^ 2 / (2 * D.reduced_mass) = 0 :=
      le_antisymm hnotpos hnonneg_L
    have hturn := D.turning_100
    rw [hL0] at hturn
    simp only [sub_zero] at hturn
    linarith [hturn, hterm, hcoul]
  have hexpand : D.turningQuadratic r =
      r * (D.total_energy * r + coulombK * elementaryCharge ^ 2)
        - D.total_angular_momentum ^ 2 / (2 * D.reduced_mass) := by
    rw [turningQuadratic]; ring
  rw [hexpand]
  have hnonneg : 0 ≤ r * (D.total_energy * r + coulombK * elementaryCharge ^ 2) :=
    mul_nonneg (le_of_lt hr_pos) hkey
  linarith [hL, hnonneg]

/-- Bound-branch corollary, support-boundedness form: every attained
separation lies strictly below the energy-sign threshold `k e²/(−E)`.
This is the first usable *boundedness* consequence of the `bound_branch`
field on the attained-separation set; the exclusion of unbounded-support
countermodels as a theorem.  It does not locate the maximum: the sharp
value `(1600/9)·a₀` is proved conclusion-side in `orbitBound_T1_B1`. -/
theorem attainedSeparations_lt_energy_threshold {hR : ScalingRegime}
    (D : CoulombPairData hR) (hm : 0 < D.reduced_mass) {r : ℝ}
    (hr : r ∈ D.attainedSeparations) :
    r < coulombK * elementaryCharge ^ 2 / (-D.total_energy) := by
  rcases hr with ⟨hr_pos, hrQ⟩
  by_contra hcontra
  push_neg at hcontra
  have hpos := D.quadratic_pos_of_large hm hcontra
  linarith [hrQ, hpos]

end CoulombPairData

/-! ### Turning-point readout (recorded initial instant, no target value) -/

/-- A positive `x` (units of `a₀`) is a turning point of the radial motion
when `Q(x·a₀) = 0`.  The associated `radial_is_zero` field records its
physical meaning: the radial speed vanishes there.  No numeric value of
any root beyond the Fig.-1b readout `100` is baked into any assumption. -/
def IsTurningPointInBohrRadii {hR : ScalingRegime} (D : CoulombPairData hR)
    (x : ℝ) : Prop :=
  0 < x ∧ D.turningQuadratic (x * bohrRadius) = 0

/-- The Fig.-1b transverse instant at separation `100·a₀` is a turning
point (subsumes the `turning_100` governing-law field, restated in
turning-point language for downstream use). -/
theorem initial_turning_point {hR : ScalingRegime} (D : CoulombPairData hR) :
    IsTurningPointInBohrRadii D initialSeparationInBohrRadii := by
  refine ⟨by norm_num [initialSeparationInBohrRadii], ?_⟩
  rw [CoulombPairData.turningQuadratic, ← D.initial_separation_value]
  exact D.turning_100

/-! ### Certified root identity for the recorded bound case (bridge) -/

/-- The certified factorization of the turning-point quadratic in the
`μ = 4` bound case: for `x > 0`, writing the quadratic in `1/x`
(in units of `a₀`),

`x²·Q(x·a₀)·(2 μ_red/l²)
  = (100/x)² − (100/100 + 100/(1600/9))·(100/x) + (100/100)·(100/(1600/9))`

This is a *purely algebraic* restatement of the constants of
`CoulombPairData` (`E`, `L`, `μ_red`, `v₀`, `r₀`) after the governing
fields are substituted; its identification with the recorded official
value is conclusion-side content (it asserts nothing about which turning
point is maximal or attained beyond what `attainedSeparations` and the
governing laws already say).  Carried as a separate theorem so later proof
stages can `rw` with it. -/
theorem certified_factorization {hR : ScalingRegime} (_D : CoulombPairData hR)
    (x : ℝ) (hx : 0 < x) :
    (100 / x) ^ 2 - (100 / 100 + 100 / (1600 / 9)) * (100 / x) +
        (100 / 100) * (100 / (1600 / 9)) =
      (100 / x - 1) * (100 / x - 9 / 16) := by
  have hx' : (100 : ℝ) / x ≠ 0 := by positivity
  field_simp
  ring

/-- Root-of-factorization bridge: a positive `x` makes the certified
`1/x`-quadratic vanish iff `x = 100` or `x = 1600/9`.  This is still pure
algebra over the factorization (`certified_factorization`); the *physics*
content — that both roots are attained and that the larger one is the
maximum — belongs to the main theorem below. -/
theorem turning_root_cases {hR : ScalingRegime} (D : CoulombPairData hR)
    {x : ℝ} (hx : 0 < x)
    (hroot :
      (100 / x) ^ 2 - (100 / 100 + 100 / (1600 / 9)) * (100 / x) +
          (100 / 100) * (100 / (1600 / 9)) = 0) :
    x = 100 ∨ x = 1600 / 9 := by
  rw [certified_factorization (hR := hR) (_D := D) x hx] at hroot
  rcases mul_eq_zero.mp hroot with h | h
  · have : (100 : ℝ) / x = 1 := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp at this
    left
    linarith [this]
  · have : (100 : ℝ) / x = 9 / 16 := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp at this
    right
    nlinarith [this]

/-! ### Maximal separation: abstract carrier, elimination, target -/

/-- Abstract carrier of “maximum separation attained along the bound
orbit”: the greatest element of the attained-separation set.  Carries no
numeric content by itself. -/
def IsMaxSeparationAlongOrbit {hR : ScalingRegime} (D : CoulombPairData hR)
    (r : ℝ) : Prop :=
  IsGreatest D.attainedSeparations r

/-- Elimination theorem for the abstract carrier: any attained separation
is bounded above by a maximal one.  Gives later stages a reusable
elimination principle on the formal meaning of “maximum separation”. -/
theorem IsMaxSeparationAlongOrbit.elim {hR : ScalingRegime} {D : CoulombPairData hR}
    {r r' : ℝ} (hmax : IsMaxSeparationAlongOrbit D r)
    (hr' : r' ∈ D.attainedSeparations) : r' ≤ r :=
  hmax.2 hr'

/-- Support bound from the radial law, abstract-root form: given two
positive ordered roots `x₁ < x₂` (units of `a₀`) together with the sign
analysis that the region `Q ≤ 0` is contained in `[x₁, x₂]`, every
attained separation lies in `[x₁·a₀, x₂·a₀]`.  The bridge hypothesis
`hfact` records the sign analysis of the normalized monic quadratic with
abstract roots; statement and conclusion mention only `x₁ x₂`, so no
certified numeric root is presupposed here (the `1600/9` specialization
happens conclusion-side in `orbitBound_T1_B1`). -/
theorem attainedSeparations_subset_Icc_abstract {hR : ScalingRegime}
    (D : CoulombPairData hR) {r : ℝ} (hr : r ∈ D.attainedSeparations)
    {x₁ x₂ : ℝ} (_hx₁₂ : x₁ < x₂)
    (hfact : ∀ x : ℝ, 0 < x →
      D.turningQuadratic (x * bohrRadius) ≤ 0 → x₁ ≤ x ∧ x ≤ x₂) :
    x₁ * bohrRadius ≤ r ∧ r ≤ x₂ * bohrRadius := by
  rcases hr with ⟨hr_pos, hrQ⟩
  have ha := hR.bohrRadius_pos
  obtain ⟨x, rfl : r = x * bohrRadius, hx⟩ : ∃ x : ℝ, r = x * bohrRadius ∧ 0 < x :=
    ⟨r / bohrRadius, by field_simp, by positivity⟩
  rcases hfact x hx hrQ with ⟨h1, h2⟩
  constructor
  · nlinarith [ha]
  · nlinarith [ha]

/-- Certified-root support bound (conclusion-side first use of the
recorded value): in the `μ = 4` bound case every attained separation lies
at or below `(1600/9)·a₀`, the upper certified turning-point root.  The
proof is a bridge obligation: it combines
`CoulombPairData.turningQuadratic_normalized_eq` (normalization),
`certified_factorization` / `turning_root_cases` (pure algebra), and the
orbit-support law `CoulombPairData.orbit_support`; it is NOT assumed by
any other declaration. -/
theorem orbitBound_T1_B1 {hR : ScalingRegime} (D : CoulombPairData hR)
    (hv : D.AnchoredValues) (hb : IsBoundMu boundMu)
    {r : ℝ} (hr : r ∈ D.attainedSeparations) :
    r ≤ (1600 / 9) * bohrRadius := by
  sorry

/-- Certified-root attainability (conclusion-side first use of the
recorded value): the upper turning-point separation `(1600/9)·a₀` is
realized along the bound orbit (the apogee of the elliptic motion of Hint
2).  Its proof is a bridge obligation (continuity of the radial motion
between the two turning points, Intermediate Value Theorem for the
separation as a function of time); it is NOT assumed by any other
declaration. -/
theorem apogee_attained_T1_B1 {hR : ScalingRegime} (D : CoulombPairData hR)
    (hv : D.AnchoredValues) (hb : IsBoundMu boundMu) :
    (1600 / 9) * bohrRadius ∈ D.attainedSeparations := by
  sorry

/-- **Main target (T1-B1, 1.0 pt).**  Under the two-body Coulomb model of
Fig. 1b with `μ = 4` (bound case), there exists a maximal attained
separation between `e⁺` and `e⁻`, and its value is exactly
`(1600/9)·a₀`.  The recorded official value first becomes *asserted as the
answer* here, on the conclusion side: attainability (`apogee_attained_T1_B1`)
and the certified support bound (`orbitBound_T1_B1`), whose conjunction is
exactly the greatest-element statement, are conclusion-side lemmas proved
from the governing laws — nothing in the hypothesis list mentions the
value `1600/9`.  The proof combines `orbitBound_T1_B1`,
`apogee_attained_T1_B1` and `IsMaxSeparationAlongOrbit`. -/
theorem maximum_separation_T1_B1 {hR : ScalingRegime} (D : CoulombPairData hR)
    (hv : D.AnchoredValues) (hb : IsBoundMu boundMu) :
    ∃ r_max : ℝ,
      IsMaxSeparationAlongOrbit D r_max ∧ r_max = (1600 / 9) * bohrRadius := by
  refine ⟨(1600 / 9) * bohrRadius, ⟨⟨?_, ?_⟩, rfl⟩⟩
  · exact apogee_attained_T1_B1 D hv hb
  · intro r' hr'
    exact orbitBound_T1_B1 D hv hb hr'

/-- The numeric readout requested by the subquestion (“in terms of `a₀`”):
the maximum separation in units of `a₀` is exactly `1600/9`.  Corollary
form of `maximum_separation_T1_B1` with the division by `a₀ > 0` made
explicit. -/
theorem maximum_separation_in_bohr_radii_T1_B1 {hR : ScalingRegime}
    (D : CoulombPairData hR)
    (hv : D.AnchoredValues) (hb : IsBoundMu boundMu) :
    ∃ x_max : ℝ,
      IsMaxSeparationAlongOrbit D (x_max * bohrRadius) ∧ x_max = 1600 / 9 := by
  exact ⟨1600 / 9,
    ⟨apogee_attained_T1_B1 D hv hb, fun _ hr' => orbitBound_T1_B1 D hv hb hr'⟩, rfl⟩

end

end IPhO2026.Problem1.B1
