/-
  IPhO 2026, Theoretical Problem 1 (T1), Part T1-B2 (labeled B.2) —
  the unbound electron–positron pair of Figure 1b: asymptotic relative
  velocity and signed deflection angle.

  Autoformalized from blueprint chapter
  `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_2.tex`
  (marked `% archon:physics`) and the official source page `T1_page-2.png`.

  Physical situation (Fig. 1b, official page 5/14 — same setting as B.1):
  A positron `e+` is located at a distance `100 * a0` from an electron `e-`.
  The particles move so that their velocities are antiparallel and, at that
  instant, perpendicular to their separation (Fig. 1b).  Each particle
  carries angular momentum of magnitude `mu * hbar` about the system's
  center of mass, `mu` a dimensionless numerical factor.  The only
  interaction between `e+` and `e-` is electrostatic (Coulomb); both
  particles have the same inertial mass `m` and equal charge magnitude `e`
  of opposite sign.  The system is isolated, classical, non-relativistic.
  The Bohr radius is `a0 = 4*pi*eps0*hbar^2/(m e^2)`, and the Coulomb
  constant is `k = 1/(4*pi*eps0)`.

  Current subquestion (T1-B2, 2.5 pts):
    For `mu = 15/2` the pair is unbound (hyperbolic scattering).  Let
    `u_inf` be the relative velocity of `e+` with respect to `e-` as the
    separation tends to infinity.  Find the angle between `u_inf` and the
    initial line of motion of `e+`, in degrees.

  Recorded official answer: signed deflection `-16.60` degrees, i.e. the
  asymptotic direction of `u_inf` lies 16.60 degrees BELOW the initial
  positron line of motion.  This value appears ONLY on the conclusion side
  of `signed_deflection_angle_T1_B2` and of its magnitude corollary
  `unsigned_deflection_angle_in_degrees_T1_B2`.  No assumption, premise
  field, or local definition mentions `16.60`, `83/900`, or any numeric
  deflection — the sign toward the line connecting the pair and the
  magnitude are exactly what must be proved.

  Official hints recorded on the problem page (governing-law input, not
  target): Hint 1: eccentricity `eps = sqrt(1 + 4 L^2 E / (k^2 e^4 m))`
  with `E` and `L` the total energy and the magnitude of the total angular
  momentum, `k` the Coulomb constant; Hint 2: polar equation of the conic
  trajectory `r = a / (1 - eps cos theta)`.  They are encoded as
  *derivable bridge lemmas* (`eccentricity_sq_eq`, `orbit_eq_conic`);
  the deflection formula is a sorry-bodied bridge
  (`signed_deflection_eq_formula`).

  Conventions:
  * Two-body -> one-body reduction is encoded in
    `CoulombScatteringData.reduced_mass_eq` (`m_red = m/2`) and
    `CoulombScatteringData.relative_kinetic_law` (kinetic energy of the
    two opposite CM-frame velocities equals `(1/2) m_red u^2` with
    `u = 2 v0`).
  * The trajectory is an abstract planar curve `sep : R -> R^2`, the
    relative coordinate `r_positron - r_electron` as a function of time,
    constrained by governing-law fields (Newton's equation for the
    reduced particle under attractive Coulomb, angular-momentum
    conservation, the multiplied-out radial-energy identity, the turning
    point at `t = 0`, polar decomposition).  No closed orbit shape is
    assumed: the conic form appears only in the bridge lemma
    `orbit_eq_conic`.
  * `u_inf` carries a *definition* (`AsymptoticRelativeVelocity`, a
    `Filter.Tendsto` statement of the trajectory's relative velocity at
    `Filter.atTop`), so its existence is a theorem to be proved
    (`exists_asymptoticRelativeVelocity`), not an assumption.
  * Proofs are `by sorry` by design (autoformalize stage).  The only
    closed proofs are pure definitional/algebraic certificates
    (`unboundMu_isAngularMomentumFactor`, `total_angular_momentum_value`,
    `initial_separation_pos`, `turningQuadratic_periapsis`,
    `eccentricity_gt_one`, `asymptote_factor_certificate`,
    `signedDeflection_eq_neg_angle`); none of them asserts any
    deflection-angle value.
  * The orientation convention for the signed answer: choosing the
    Fig.-1b frame with positive signed bracket
    `perp sep0 v0 > 0` (positron above the line connecting the pair,
    moving left, so the polar angle increases), the attraction bends
    the trajectory toward the line connecting the pair and
    `perp (initialDirection) u_inf < 0` — the clockwise case of
    `signedDeflection`, i.e. the official “16.60 degrees BELOW the
    initial line of motion”.
-/

import Mathlib

open Real Set Filter

namespace IPhO2026.Problem1.B2

noncomputable section

/-! ### Planar vectors: dot product and perpendicular bracket -/

/-- The scattering plane (CM frame): `R^2` with its standard inner product. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Dot product of two planar vectors. -/
def dot (v w : Plane) : ℝ := v 0 * w 0 + v 1 * w 1

/-- Planar perpendicular bracket `perp v w = v_x w_y - v_y w_x`: the signed
z-component of the 2D cross product.  Positive when `w` is reached from `v`
by a counterclockwise rotation of less than 180 degrees.  Used to express
angular momentum and the side (branch/orientation) of the deflection. -/
def perp (v w : Plane) : ℝ := v 0 * w 1 - v 1 * w 0

/-! ### Universal constants and fixed problem parameters -/

/-- Mass `m` of each particle (electron and positron inertial mass, kg). -/
opaque particleMass : ℝ

/-- Reduced Planck constant `ℏ` (J·s). -/
opaque hbar : ℝ

/-- Coulomb constant `k = 1/(4 pi eps0)` (N·m²·C⁻²). -/
opaque coulombK : ℝ

/-- Elementary charge magnitude `e`: the electron has charge `-e`, the
positron `+e` (C). -/
opaque elementaryCharge : ℝ

/-- Bohr radius `a0 = 4 pi eps0 ℏ²/(m e²) = ℏ²/(k·m·e²)` (m).  Opaque on
purpose: its defining SI relation to `k, ℏ, m, e` is imposed via
`ScalingRegime.bohr_radius_def` so that nothing about the target value
can be obtained by unfolding. -/
opaque bohrRadius : ℝ

/-- Positivity of the constants plus the defining relation of the Bohr
radius (`a0 = ℏ²/(k·m·e²)`, i.e. the page's `a0 = 4 pi eps0 ℏ²/(m e²)`
with `k = 1/(4 pi eps0)`). -/
structure ScalingRegime : Prop where
  particleMass_pos : 0 < particleMass
  hbar_pos : 0 < hbar
  coulombK_pos : 0 < coulombK
  elementaryCharge_pos : 0 < elementaryCharge
  bohrRadius_pos : 0 < bohrRadius
  bohr_radius_def : bohrRadius = hbar ^ 2 / (coulombK * particleMass * elementaryCharge ^ 2)

/-- The dimensionless angular-momentum factor `mu` of the statement: each
particle carries angular momentum `mu * ℏ` about the centre of mass. -/
def IsAngularMomentumFactor (μ : ℝ) : Prop :=
  0 < μ

/-- The value `mu = 15/2` of subquestion B.2 (unbound case). -/
def unboundMu : ℝ := 15 / 2

/-- `15/2` is a valid angular-momentum factor. -/
theorem unboundMu_isAngularMomentumFactor : IsAngularMomentumFactor unboundMu := by
  norm_num [unboundMu, IsAngularMomentumFactor]

/-! ### Two-body Coulomb scattering data and governing laws -/

/-- Data and governing laws of the isolated, classical, non-relativistic
electron–positron pair with purely electrostatic interaction, with the
two-body -> one-body (relative coordinate, reduced mass) reduction encoded.

`sep t` is the relative coordinate `r_e+(t) - r_e-(t)` in the centre-of-mass
plane (metres).  Energies are in joules, angular momenta in J·s, speeds in
m/s.  No field mentions the asymptotic velocity or any deflection angle:
those are conclusion-side concepts defined after this structure. -/
structure CoulombScatteringData (hR : ScalingRegime) where
  /-- Relative position `r_e+(t) - r_e-(t)` in the CM frame (m). -/
  sep : ℝ → Plane
  /-- Initial relative position at the recorded instant `t = 0` (m). -/
  sep0 : Plane
  /-- Initial CM-frame velocity of the positron (m/s); the electron's is
  `-v0` (equal masses, antiparallel velocities, CM at rest). -/
  v0 : Plane
  /-- A continuous polar angle of the relative coordinate (rad). -/
  polar_angle : ℝ → ℝ
  /-- Reduced inertial mass of the two equal masses (kg). -/
  reduced_mass : ℝ
  /-- Total angular momentum about the centre of mass, magnitude (J·s). -/
  total_angular_momentum : ℝ
  /-- Conserved total energy of the isolated system (J). -/
  total_energy : ℝ
  /-- Initial separation (Fig. 1b readout), in metres. -/
  initial_separation : ℝ
  /-- Initial CM-frame speed of each particle (m/s); the velocities are
  antiparallel, so the relative speed is `2 * initial_speed`. -/
  initial_speed : ℝ
  /-- The pair is never at zero separation (attractive Coulomb scattering
  with nonzero angular momentum). -/
  sep_ne_zero : ∀ t : ℝ, sep t ≠ 0
  /-- Regularity of the trajectory (Newtonian dynamics, twice continuously
  differentiable). -/
  smooth_sep : ContDiff ℝ 2 sep
  /-- The recorded instant `t = 0` has the Fig.-1b relative configuration
  and the antiparallel velocities: `sep 0 = sep0` and the relative
  velocity is `2 * v0`. -/
  initial_instant : sep 0 = sep0 ∧ deriv sep 0 = (2 : ℝ) • v0
  /-- Reduced mass of two equal point masses: `m_red = m/2`. -/
  reduced_mass_eq : reduced_mass = particleMass / 2
  /-- Fig. 1b readout: `r0 = 100 * a0`. -/
  initial_separation_value : initial_separation = 100 * bohrRadius
  /-- The relative position at `t = 0` has magnitude `r0`. -/
  initial_separation_is_norm : ‖sep0‖ = initial_separation
  /-- Nonzero initial motion; `v0` has magnitude `initial_speed`. -/
  initial_speed_value : v0 ≠ 0 ∧ ‖v0‖ = initial_speed
  /-- Angular momentum per particle about the centre of mass is `mu * ℏ`
  (given data): each particle orbits at radius `r0/2` with velocity
  perpendicular to its radius vector, so `m v0 (r0/2) = mu ℏ`. -/
  angular_momentum_per_particle :
    particleMass * initial_speed * (initial_separation / 2) = unboundMu * hbar
  /-- Total angular momentum is the sum of the two equal per-particle
  contributions (equal masses, antiparallel velocities, centre of mass at
  the midpoint): `L = 2 mu ℏ`. -/
  total_angular_momentum_eq :
    total_angular_momentum =
      2 * (particleMass * initial_speed * (initial_separation / 2))
  /-- Fig. 1b geometry and orientation: at `t = 0` the velocities are
  perpendicular to the separation, with the recorded left-handed
  orientation of the figure (positron above the line connecting the
  pair, moving left): the signed planar bracket of the separation with
  the positron velocity is `(+1) * r0 * v0` (`perp sep0 v0 = 0` would
  mean collinear, `perp sep0 v0 = -r0 v0` the mirrored figure). -/
  initial_transverse :
    perp sep0 v0 = initial_separation * initial_speed
  /-- Polar decomposition of the planar relative coordinate:
  `sep t = |sep t| * (cos θ(t), sin θ(t))`. -/
  polar_decomposition :
    ∀ t : ℝ, sep t 0 = ‖sep t‖ * Real.cos (polar_angle t) ∧
      sep t 1 = ‖sep t‖ * Real.sin (polar_angle t)
  /-- Angular-momentum conservation for the reduced one-body problem
  (the `r² θ' = L/m_red` law in bracket form): at every time the signed
  planar angular momentum per unit reduced mass is the constant
  `L / m_red`.  Sign consistency: at `t = 0`, combining
  `initial_instant`, `initial_transverse` and `reduced_mass_eq` gives
  `perp sep0 (2 · v0) = 2 r0 v0 = L / (m/2)`, i.e. exactly the stated
  RHS — the trajectory already starts on the increasing-angle branch. -/
  angular_momentum_law :
    ∀ t : ℝ, perp (sep t) (deriv sep t) = total_angular_momentum / reduced_mass
  /-- Relative-coordinate kinetic energy: the sum of the two Newtonian
  kinetic energies equals `(1/2) m_red u^2` with `u = 2 v0`. -/
  relative_kinetic_law :
    2 * ((1 / 2) * particleMass * initial_speed ^ 2) =
      (1 / 2) * reduced_mass * (2 * initial_speed) ^ 2
  /-- Coulomb's law: potential energy `U(r) = -k e²/r`; at the transverse
  initial instant the conserved total energy is kinetic plus Coulomb. -/
  coulomb_law :
    total_energy =
      2 * ((1 / 2) * particleMass * initial_speed ^ 2) -
        coulombK * elementaryCharge ^ 2 / initial_separation
  /-- Newton's equation for the reduced particle under the attractive
  Coulomb force (two-body reduction: acceleration of the reduced particle
  is `(m/2)⁻¹` times the Coulomb force along the separation, so its
  magnitude is `k e² / (m_red r²) = k e² / ((m/2) r²)`). -/
  newton_relative_law :
    ∀ t : ℝ, ‖(1 / 2 : ℝ) • (deriv (deriv sep)) t‖ =
      coulombK * elementaryCharge ^ 2 / ‖sep t‖ ^ 2
  /-- Energy + angular-momentum conservation for the inverse-square
  attraction, multiplied through by `r^2 > 0` (with `radial speed = r'`):
  `E r^2 = (1/2) m_red (r' r)^2 + L^2/(2 m_red) - k e^2 r`.  The left-hand
  rearrangement `E r^2 + k e^2 r - L^2/(2 m_red)` is the turning-point
  quadratic `turningQuadratic`; it vanishes exactly where the radial speed
  vanishes. -/
  radial_energy_law :
    ∀ t : ℝ,
      total_energy * ‖sep t‖ ^ 2 +
          coulombK * elementaryCharge ^ 2 * ‖sep t‖ -
        total_angular_momentum ^ 2 / (2 * reduced_mass) =
      (1 / 2) * reduced_mass * (deriv (fun s => ‖sep s‖) t * ‖sep t‖) ^ 2
  /-- The transverse initial instant of Fig. 1b is a turning point
  (velocities perpendicular to the separation, radial speed zero). -/
  turning_point_initial : deriv (fun s => ‖sep s‖) 0 = 0

namespace CoulombScatteringData

variable {hR : ScalingRegime} (S : CoulombScatteringData hR)

/-- Initial separation is positive (Fig. 1b readout `100 * a0`, `a0 > 0`). -/
theorem initial_separation_pos : 0 < S.initial_separation := by
  rw [S.initial_separation_value]
  exact mul_pos (by norm_num) hR.bohrRadius_pos

/-- The total angular momentum has the value `2 * mu * ℏ = 15 ℏ` for
`mu = 15/2`. -/
theorem total_angular_momentum_value :
    S.total_angular_momentum = 2 * (unboundMu * hbar) := by
  rw [S.total_angular_momentum_eq, S.angular_momentum_per_particle]

/-- The turning-point quadratic of the effective radial dynamics,
`Q(r) = E r^2 + k e^2 r - L^2/(2 m_red)`: the radial-energy identity
multiplied by `r^2 > 0`; `Q(r) = (1/2) m_red r'^2 r^2` along the
trajectory, so `Q(r) = 0` exactly at turning points. -/
def turningQuadratic (r : ℝ) : ℝ :=
  S.total_energy * r ^ 2 + coulombK * elementaryCharge ^ 2 * r -
    S.total_angular_momentum ^ 2 / (2 * S.reduced_mass)

/-- The initial separation is a turning point (the periapsis of the
unbound orbit): `Q(r0) = 0`, from `radial_energy_law` at `t = 0` and
`turning_point_initial`.  Pure rearrangement of governing-law fields. -/
theorem turningQuadratic_periapsis : S.turningQuadratic S.initial_separation = 0 := by
  have h1 := S.radial_energy_law 0
  rw [S.initial_instant.1, S.turning_point_initial, S.initial_separation_is_norm,
    zero_mul, zero_pow (two_ne_zero : (2 : ℕ) ≠ 0), mul_zero] at h1
  rw [CoulombScatteringData.turningQuadratic]
  exact h1

/-- Semilatus rectum `p = L^2 / (m_red k e^2)` of the reduced one-body
problem (m): the geometric scale of the conic in Hint 2. -/
def semilatusRectum : ℝ :=
  S.total_angular_momentum ^ 2 /
    (S.reduced_mass * coulombK * elementaryCharge ^ 2)

/-- Dimensionless squared eccentricity of Hint 1 for equal masses
(`m_red = m/2` reconciles `2 m_red` in the denominator with the page's
`m`): `eps^2 = 1 + 2 E L^2 / (m_red (k e^2)^2) = 1 + 4 E L^2 / (k^2 e^4 m)`. -/
def eccentricitySq : ℝ :=
  1 + 2 * S.total_energy * S.total_angular_momentum ^ 2 /
    (S.reduced_mass * (coulombK * elementaryCharge ^ 2) ^ 2)

end CoulombScatteringData

/-! ### Unboundness at `mu = 15/2` -/

/-- The total energy is the Figure-1b value `mu²/2500 - 1/200` in units of
`ℏ²/(m a0²)`; for `mu = 15/2` this is `7/400 > 0`: the pair is unbound
(hyperbolic scattering).  Derivable from `coulomb_law`,
`angular_momentum_per_particle`, `initial_separation_value`,
`bohr_radius_def` and `relative_kinetic_law`; the proof is pure algebra
once those laws are granted, and contains no angle information. -/
theorem total_energy_pos {hR : ScalingRegime} (S : CoulombScatteringData hR)
    (hμ : IsAngularMomentumFactor unboundMu) : 0 < S.total_energy := by
  have hm : (0:ℝ) < particleMass := hR.particleMass_pos
  have ha0 : (0:ℝ) < bohrRadius := hR.bohrRadius_pos
  have hh : (0:ℝ) < hbar := hR.hbar_pos
  have hk : (0:ℝ) < coulombK := hR.coulombK_pos
  have he : (0:ℝ) < elementaryCharge := hR.elementaryCharge_pos
  have hke : (0:ℝ) < coulombK * elementaryCharge ^ 2 := mul_pos hk (pow_pos he 2)
  -- Initial speed from the angular-momentum datum `m v0 (r0/2) = mu hbar`
  -- with `r0 = 100 a0`:  `v0 = 2 mu hbar / (m * (100 a0))`.
  have hv0 : S.initial_speed = 2 * unboundMu * hbar / (particleMass * (100 * bohrRadius)) := by
    have hperp := S.angular_momentum_per_particle
    rw [S.initial_separation_value] at hperp
    have hd : particleMass * (100 * bohrRadius) ≠ 0 :=
      mul_ne_zero (ne_of_gt hm) (mul_ne_zero (by norm_num) (ne_of_gt ha0))
    have h2 : particleMass * (100 * bohrRadius) * S.initial_speed =
        2 * (unboundMu * hbar) := by
      have e : particleMass * (100 * bohrRadius) * S.initial_speed =
          2 * (particleMass * S.initial_speed * (100 * bohrRadius / 2)) := by ring
      rw [e, hperp]
    have h2'' : particleMass * (100 * bohrRadius) * S.initial_speed
        = 2 * unboundMu * hbar := by
      have e : (2:ℝ) * unboundMu * hbar = 2 * (unboundMu * hbar) := by ring
      rw [e, h2]
    rw [eq_div_iff hd, mul_comm S.initial_speed (particleMass * (100 * bohrRadius))]
    exact h2''
  rw [S.coulomb_law, S.initial_separation_value, hv0, hR.bohr_radius_def]
  -- Everything over the common unit `hbar^2/(m a0^2)` is the rational
  -- computation `4 mu^2/100^2 - 1/100 = 1/80 > 0` at `mu = 15/2`.
  have hmu : unboundMu = 15 / 2 := rfl
  rw [hmu]
  have hkene : coulombK * elementaryCharge ^ 2 ≠ 0 := ne_of_gt hke
  field_simp [ne_of_gt hm, ne_of_gt ha0, ne_of_gt hh, hkene]
  have h125 : (0:ℝ) < 15 ^ 2 - 100 := by norm_num
  nlinarith [mul_pos hm hke, hke, h125, sq_pos_of_pos hh]

/-- At `mu = 15/2` the squared eccentricity strictly exceeds `1`
(hyperbola, not ellipse): the added term
`2 E L^2 / (m_red (k e²)²)` is strictly positive. -/
theorem eccentricity_gt_one {hR : ScalingRegime} (S : CoulombScatteringData hR)
    (hμ : IsAngularMomentumFactor unboundMu) : 1 < S.eccentricitySq := by
  have hE : 0 < S.total_energy := total_energy_pos S hμ
  have hm : 0 < S.reduced_mass := by
    rw [S.reduced_mass_eq]
    exact div_pos hR.particleMass_pos (by norm_num)
  have hL : S.total_angular_momentum ≠ 0 := by
    rw [S.total_angular_momentum_value]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero (by norm_num [unboundMu]) (ne_of_gt hR.hbar_pos))
  have hke : coulombK * elementaryCharge ^ 2 ≠ 0 :=
    mul_ne_zero (ne_of_gt hR.coulombK_pos)
      (pow_ne_zero 2 (ne_of_gt hR.elementaryCharge_pos))
  have hpos :
      0 < 2 * S.total_energy * S.total_angular_momentum ^ 2 /
        (S.reduced_mass * (coulombK * elementaryCharge ^ 2) ^ 2) :=
    div_pos (mul_pos (mul_pos (by norm_num) hE) (sq_pos_of_ne_zero hL))
      (mul_pos hm (sq_pos_of_ne_zero hke))
  have hdef : S.eccentricitySq =
      1 + 2 * S.total_energy * S.total_angular_momentum ^ 2 /
        (S.reduced_mass * (coulombK * elementaryCharge ^ 2) ^ 2) := rfl
  rw [hdef]
  linarith

/-- Value of Hint 1 for this scenario: the squared eccentricity equals
`67/4` (so `eps = sqrt 67 / 2 > 1`).  Derivable from the same laws as
`total_energy_pos`; conclusion-free of angle data. -/
theorem eccentricity_sq_eq {hR : ScalingRegime} (S : CoulombScatteringData hR)
    (hμ : IsAngularMomentumFactor unboundMu) : S.eccentricitySq = 67 / 4 := by
  -- REDRAFT REQUEST (see task_results): with the governing-law fields as
  -- written, Hint 1 evaluates to `49/4`, not `67/4`.  Both downstream main
  -- targets are stated with the `f(67/4) = 2/sqrt 63` closed form, so they
  -- are mutually inconsistent with this theorem; the correct one-line
  -- redraft (49/4, `2/sqrt 45`, `arctan(1/sqrt(eps^2-1))`) reproduces the
  -- official `-16.60 deg`.  The `49/4`-side proof is field arithmetic and
  -- is recorded in the task result; left as `sorry` only because of the
  -- protected conclusion `67/4`.
  sorry

end

/-! ### Initial line of motion of the positron -/

/-- The initial line of motion of `e+`: the unit vector along the initial
positron velocity `v0` (Fig. 1b).  The reference direction of the asked
angle. -/
noncomputable def initialDirection {hR : ScalingRegime} (S : CoulombScatteringData hR) : Plane :=
  ‖S.v0‖⁻¹ • S.v0

/-! ### The conic bridge (Hint 2) -/

noncomputable section

/-- Hint 2 made derivable: the trajectory `|sep|` as a function of its
own polar angle `polar_angle` is a conic.  For the unbound case
`eps > 1` the physical branch near the periapsis has denominator
`eps * cos θ - 1 > 0`.  `θ0` is the (a priori unknown) direction of the
symmetry axis of the hyperbola; nothing here fixes its value. -/
theorem orbit_eq_conic {hR : ScalingRegime} (S : CoulombScatteringData hR)
    (hμ : IsAngularMomentumFactor unboundMu) :
    ∃ eps θ0 : ℝ, eps = Real.sqrt S.eccentricitySq ∧ 1 < eps ∧
      ∀ t : ℝ, 0 < eps * Real.cos (S.polar_angle t - θ0) - 1 ∧
        ‖S.sep t‖ =
          S.semilatusRectum / (eps * Real.cos (S.polar_angle t - θ0) - 1) := by
  -- Blocked: this is the full Kepler-equation/Binet-ODE content
  -- (differentiate L·θ' = u²/p·(1+e cos) via the radial-energy law and
  -- integrate with `polar_angle` monotone by `angular_momentum_law`).
  -- Provable in principle, but a multi-hundred-line project on the raw
  -- `ContDiff`/`deriv` fields; no Mathlib Kepler API exists.  Left as
  -- `sorry` per the physics-proof workflow (missing infrastructure noted).
  sorry

/-! ### Asymptotic relative velocity `u_inf` -/

/-- A candidate asymptotic relative-velocity vector (m/s): plain data,
to which the predicate `IsAsymptoticRelativeVelocity` then assigns the
physical role of `u_inf`. -/
structure RelativeVelocityVector where
  /-- The planar vector (m/s). -/
  vec : Plane

/-- The asymptotic relative velocity `u_inf` of `e+` with respect to `e-`
as the separation tends to infinity: `u.vec` is a nonzero planar vector
that is the limit of the relative velocity `deriv sep` at `Filter.atTop`
(energy conservation keeps the speed bounded, so future time infinity and
infinite separation coincide for the unbound orbit).  The orientation
field `direction_toward_pair` records the rolling branch: the deflection
rotates the initial line of motion toward the line connecting the pair
(clockwise in the Fig.-1b orientation), so the signed planar bracket of
the initial direction with `u.vec` is nonpositive.  Constraining: the
`tendsto` field is a genuine limit equation, so the predicate can hold of
at most one vector; existence is a theorem to be proved
(`exists_asymptoticRelativeVelocity`), not an assumption. -/
structure IsAsymptoticRelativeVelocity {hR : ScalingRegime}
    (S : CoulombScatteringData hR) (u : RelativeVelocityVector) : Prop where
  /-- `u.vec` is the limit of the relative velocity as `t -> +∞`. -/
  tendsto : Filter.Tendsto (deriv S.sep) Filter.atTop (nhds u.vec)
  /-- The asymptotic motion is nontrivial (scattering, not capture). -/
  u_inf_ne_zero : u.vec ≠ 0
  /-- Rolling branch: the deflection bends the trajectory toward the line
  connecting the pair, so `(initial direction) ×z u.vec ≤ 0`. -/
  direction_toward_pair : perp (initialDirection (S := S)) u.vec ≤ 0

/-- Existence of the asymptotic relative velocity for the unbound orbit
(`mu = 15/2`, `E > 0`): the hyperbolic scattering trajectory has a
well-defined limiting relative velocity on the outward (post-periapsis)
branch.  This is the definitionally-grounded meaning of `u_inf` in the
subquestion; the proof derives the limit from the conic form of
`orbit_eq_conic` together with energy conservation. -/
theorem exists_asymptoticRelativeVelocity {hR : ScalingRegime}
    (S : CoulombScatteringData hR) (hμ : IsAngularMomentumFactor unboundMu) :
    ∃ u : RelativeVelocityVector, IsAsymptoticRelativeVelocity S u := by
  -- Blocked: constructing `u∞` requires the integrated velocity formula of
  -- the hyperbolic orbit (via `orbit_eq_conic` + energy conservation), plus
  -- the `Filter.Tendsto` limit argument for `deriv S.sep`.  Dependent on
  -- the same missing Kepler-layer infrastructure as `orbit_eq_conic`.
  sorry

/-- The angle (rad) between two nonzero planar vectors, via the standard
`Real.arccos` characterization (values in `[0, pi]`). -/
noncomputable def angleBetween (a b : Plane) : ℝ :=
  Real.arccos (dot a b / (‖a‖ * ‖b‖))

/-- Unit speed of the asymptotic relative motion: `u_inf` has magnitude
the asymptotic relative speed `sqrt(2 E / m_red)`, and its direction makes
angle `delta = pi - 2 * arctan(1 / sqrt(eps² - 1))` with the initial line
of motion on the branch side recorded in
`IsAsymptoticRelativeVelocity.direction_toward_pair` (for a hyperbola of
eccentricity `eps > 1` traversed outward from periapsis, the acute
asymptote angle to the symmetry axis is `arctan(sqrt(eps² - 1))`, so the
angle between the incoming direction and `u_inf` is
`pi - 2 * arctan(sqrt(eps²-1))⁻¹`).  Bridges Hint 1
(`eccentricity_sq_eq`), Hint 2 (`orbit_eq_conic`), and the definition of
`u_inf` (`exists_asymptoticRelativeVelocity`) to the numeric answer;
contains the sign/orientation input but NO numeric deflection value. -/
theorem signed_deflection_eq_formula {hR : ScalingRegime}
    (S : CoulombScatteringData hR) (u : RelativeVelocityVector)
    (hu : IsAsymptoticRelativeVelocity S u)
    (hμ : IsAngularMomentumFactor unboundMu) :
    ‖u.vec‖ = Real.sqrt (2 * S.total_energy / S.reduced_mass) ∧
      angleBetween (initialDirection (S := S)) u.vec =
        Real.pi - 2 * Real.arctan (1 / Real.sqrt (S.eccentricitySq - 1)) := by
  -- The norm component is the standard asymptotic-speed identity
  -- `|u∞| = sqrt(2E/m_red)` (energy conservation at vanishing Coulomb
  -- potential), admissible from `IsAsymptoticRelativeVelocity.tendsto`
  -- plus the governing-law fields — but carrying the full `deriv`-limit
  -- argument here is a project in itself.  The angle component as stated
  -- is physically WRONG for the periapsis-referenced scenario: the true
  -- unsigned deflection is the ACUTE `arctan(1/√(eps²-1))`
  -- (= arctan(2/√45) ≈ 16.6015° here), while
  -- `π - 2·arctan(1/√(eps²-1))` is the apocenter-referenced Rutherford
  -- turning angle (~146.8°).  Both components stay `sorry`; see the
  -- redraft analysis in the task result.
  sorry

/-- The oriented (signed) deflection angle of the scattering, in radians:
`theta_sign * angleBetween (initialDirection) u_inf`, where `theta_sign`
is `+1` when the deflection is counterclockwise from the initial line of
motion of `e+` and `-1` when it is clockwise.  The Fig.-1b orientation
(captured by `IsAsymptoticRelativeVelocity.direction_toward_pair`) selects
the clockwise case. -/
noncomputable def signedDeflection {hR : ScalingRegime}
    (S : CoulombScatteringData hR) (u : RelativeVelocityVector) : ℝ :=
  (if 0 ≤ perp (initialDirection (S := S)) u.vec then (1 : ℝ) else -1) *
    angleBetween (initialDirection (S := S)) u.vec

/-- Radians-to-degrees conversion. -/
noncomputable def radiansToDegrees (θ : ℝ) : ℝ := θ * (180 / Real.pi)

/-- Under the branch condition of Fig. 1b (`perp u0 u_inf ≤ 0`), the
signed deflection is the negated unsigned angle.  Definitional bridge
(`if_neg`); the degenerate zero-deflection case is discharged by the
physics side (`direction_toward_pair` together with the nonzero
deflection from `signed_deflection_eq_formula` excludes it, so the
remaining branch is strict). -/
theorem signedDeflection_eq_neg_angle {hR : ScalingRegime}
    (S : CoulombScatteringData hR) (u : RelativeVelocityVector)
    (_hu : IsAsymptoticRelativeVelocity S u)
    (hnondeg : perp (initialDirection (S := S)) u.vec < 0) :
    signedDeflection (S := S) u =
      -angleBetween (initialDirection (S := S)) u.vec := by
  unfold signedDeflection
  rw [if_neg (not_le.mpr hnondeg)]
  ring

/-! ### Main target (T1-B2, 2.5 pts) -/

/-- A real `x` rounds to the official printed value `-16.60` degrees,
i.e. to two decimal places in the sense of the official marking scheme:
`-16.605 ≤ x < -16.595`. -/
def roundsToOfficialDegrees (x : ℝ) : Prop :=
  -(16605 : ℝ) / 1000 ≤ x ∧ x < -(16595 : ℝ) / 1000

/-- **Main target (T1-B2, 2.5 pts).**  Under the two-body Coulomb model
of Fig. 1b with `mu = 15/2` (unbound case), there exists an asymptotic
relative velocity `u_inf` of `e+` with respect to `e-`, and its signed
deflection `delta` from the initial line of motion of `e+` equals
the exact value `-(pi - 2 * arctan(2 / sqrt 63))` radians, whose degree
reading rounds to the official `-16.60` degrees.  The negative sign
(“16.60 degrees BELOW the initial line of motion”) is carried by the
branch condition `perp u0 u_inf ≤ 0` inside
`IsAsymptoticRelativeVelocity.direction_toward_pair` together with the
closed form.  The recorded official value first appears here,
conclusion-side; every hypothesis is a governing law, a figure readout,
or a derivable bridge. -/
theorem signed_deflection_angle_T1_B2 {hR : ScalingRegime}
    (S : CoulombScatteringData hR) (hμ : IsAngularMomentumFactor unboundMu) :
    ∃ u : RelativeVelocityVector, ∃ delta : ℝ,
      IsAsymptoticRelativeVelocity S u ∧
        delta = signedDeflection (S := S) u ∧
        delta = -(Real.pi - 2 * Real.arctan (2 / Real.sqrt 63)) ∧
        roundsToOfficialDegrees (radiansToDegrees delta) := by
  -- Component 4 (rounding band) is shown unconditionally below via the
  -- auxiliary bounds `radiansToDegrees (-(π - 2·arctan(2/√63))) ≤ -90`
  -- (pi_gt_d2 + arctan monotonicity) and hence is incompatible with the
  -- stated band [-16.605, -16.595): the claimed closed form evaluates to
  -- ≈ -151.71°, NOT -16.60°.  The physical answer of this scenario is
  -- -arctan(2/√45) ≈ -16.6015° (see `signed_deflection_eq_formula` and
  -- the redraft note in the task result).  Components 1-3 (existence of
  -- `u_inf` and the exact-value claim) depend on the Kepler bridges
  -- `orbit_eq_conic` / `exists_asymptoticRelativeVelocity` and on the
  -- same false closed form, so the whole assembly stays `sorry`.
  have hpibnd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hout : radiansToDegrees (-(Real.pi - 2 * Real.arctan (2 / Real.sqrt 63))) ≤ -90 := by
    have hpipos : (0 : ℝ) < Real.pi := by linarith
    have h63 : 2 / Real.sqrt 63 ≤ 1 := by
      have hs : (2 : ℝ) ≤ Real.sqrt 63 := by
        rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) ] <;> norm_num
      calc 2 / Real.sqrt 63 ≤ 2 / 2 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
        _ = 1 := by norm_num
    have harctan : Real.arctan (2 / Real.sqrt 63) ≤ Real.arctan 1 :=
      arctan_le_arctan_iff.mpr h63
    rw [Real.arctan_one] at harctan
    have hδ : -(Real.pi - 2 * Real.arctan (2 / Real.sqrt 63)) ≤ -(Real.pi / 2) := by
      nlinarith [harctan, hpibnd]
    unfold radiansToDegrees
    calc -(Real.pi - 2 * Real.arctan (2 / Real.sqrt 63)) * (180 / Real.pi)
        ≤ -(Real.pi / 2) * (180 / Real.pi) := by
          apply mul_le_mul_of_nonneg_right hδ (by positivity)
      _ = -90 := by
          field_simp [ne_of_gt hpipos]
          ring
  -- `-90 < -16.605`, so `roundsToOfficialDegrees` of the claimed delta is FALSE:
  have hband_false : ¬ roundsToOfficialDegrees
      (radiansToDegrees (-(Real.pi - 2 * Real.arctan (2 / Real.sqrt 63)))) := by
    rintro ⟨hlo, -⟩
    have : (-(16605 : ℝ) / 1000) ≤ -90 := le_trans hlo hout
    norm_num at this
  sorry

/-- Algebraic certificate for the equal-mass eccentricity value: the
hyperbola `eps² = 67/4` makes the scattering asymptote factor
`1/sqrt(eps²-1) = 2/sqrt(63)`, so the exact signed deflection in
`signed_deflection_angle_T1_B2` has the stated closed form.  Pure
algebra up to the square-root identity `sqrt(63/4) = sqrt 63 / 2`. -/
theorem asymptote_factor_certificate :
    1 / Real.sqrt ((67 / 4 : ℝ) - 1) = 2 / Real.sqrt 63 := by
  have h634 : (63 / 4 : ℝ) = (Real.sqrt 63 / 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have halg : (67 / 4 : ℝ) - 1 = 63 / 4 := by norm_num
  rw [halg, h634, Real.sqrt_sq (by positivity)]
  field_simp

/-- A real `x` rounds to the official magnitude `16.60` degrees, i.e. to
two decimal places in the sense of the official marking scheme:
`16.595 ≤ x < 16.615`. -/
def roundsToOfficialDegreesAbs (x : ℝ) : Prop :=
  (16595 : ℝ) / 1000 ≤ x ∧ x < (16615 : ℝ) / 1000

/-- Magnitude corollary: the unsigned deflection angle between `u_inf` and
the initial line of motion of `e+` equals the exact value
`pi - 2 * arctan(2 / sqrt 63)` radians, whose degree reading rounds to
the official `16.60` degrees below the initial line of motion. -/
theorem unsigned_deflection_angle_in_degrees_T1_B2 {hR : ScalingRegime}
    (S : CoulombScatteringData hR) (hμ : IsAngularMomentumFactor unboundMu) :
    ∃ u : RelativeVelocityVector,
      IsAsymptoticRelativeVelocity S u ∧
        angleBetween (initialDirection (S := S)) u.vec =
          Real.pi - 2 * Real.arctan (2 / Real.sqrt 63) ∧
        roundsToOfficialDegreesAbs
          (radiansToDegrees (angleBetween (initialDirection (S := S)) u.vec)) := by
  -- The unconditional side computation below shows the STATED exact value
  -- `π - 2·arctan(2/√63)` reads ≥ 90°, hence is excluded by the theorem's
  -- own band [16.595, 16.615): the theorem as written is impossible.  The
  -- correct unsigned deflection of this scenario is `arctan(2/√45)` ≈
  -- 16.6015° (redraft blockers in the task result); the assembly is left
  -- `sorry` with the witnessed obstruction made explicit here.
  have hpibnd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  -- auxiliary bound: the claimed angle, in degrees, is at least 90:
  have hge : 90 ≤ radiansToDegrees (Real.pi - 2 * Real.arctan (2 / Real.sqrt 63)) := by
    have hpipos : (0 : ℝ) < Real.pi := by linarith
    have h63 : 2 / Real.sqrt 63 ≤ 1 := by
      have hs : (2 : ℝ) ≤ Real.sqrt 63 := by
        rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) ] <;> norm_num
      calc 2 / Real.sqrt 63 ≤ 2 / 2 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
        _ = 1 := by norm_num
    have harctan : Real.arctan (2 / Real.sqrt 63) ≤ Real.arctan 1 :=
      arctan_le_arctan_iff.mpr h63
    rw [Real.arctan_one] at harctan
    have hδ : (Real.pi / 2) ≤ Real.pi - 2 * Real.arctan (2 / Real.sqrt 63) := by
      nlinarith [harctan, hpibnd]
    unfold radiansToDegrees
    calc (90 : ℝ)
        = (Real.pi / 2) * (180 / Real.pi) := by
          field_simp [ne_of_gt hpipos]
          ring
      _ ≤ (Real.pi - 2 * Real.arctan (2 / Real.sqrt 63)) * (180 / Real.pi) := by
          apply mul_le_mul_of_nonneg_right hδ (by positivity)
  -- hence `roundsToOfficialDegreesAbs` of the claimed angle is FALSE
  -- (90 ≥ 16.615 violates x < 16.615):
  have hband_false : ¬ roundsToOfficialDegreesAbs
      (radiansToDegrees (Real.pi - 2 * Real.arctan (2 / Real.sqrt 63))) := by
    rintro ⟨-, hhi⟩
    have : (90 : ℝ) < (16615 : ℝ) / 1000 := lt_of_le_of_lt hge hhi
    norm_num at this
  sorry

end

end IPhO2026.Problem1.B2
