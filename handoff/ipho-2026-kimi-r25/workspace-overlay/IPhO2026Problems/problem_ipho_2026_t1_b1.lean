/-
# IPhO 2026 Theory T1-B1 — Electron–positron pair: maximum separation (bound case `μ = 4`)

Problem-only sources: extracted question text
(`reports/ipho_2026/problem_ipho_2026_t1_b1.source.json`) and the problem page
`ipho_2026_source/image/T1_page-2.png` (Fig. 1b, Hints 1–2).

## Physical scenario (T1-B stem)

* A positron `e⁺` and an electron `e⁻`, each of mass `m`, carry charges `+e` and
  `-e` (equal magnitude, opposite sign).
* At one instant the separation is `r₀ = 100 a₀`; the velocities are
  antiparallel and perpendicular to the separation line (Fig. 1b).
* Each particle has angular momentum of magnitude `μ ℏ` about the centre of
  mass (CM), with `μ` a dimensionless numerical factor.
* The system is isolated, classical, non-relativistic, and the only mutual
  interaction is electrostatic (Coulomb).
* `a₀ = 4π ε₀ ℏ² / (m e²)` is the Bohr radius and `k = 1 / (4π ε₀)` is the
  Coulomb constant.

## Subquestion T1-B1

For `μ = 4` the pair is bound, i.e. the particles move on a closed orbit around
the CM.  Find the maximum electron–positron separation distance, in units of
`a₀`.

## Governing laws encoded below

* Problem Hint 1: the eccentricity of the conic trajectory is
  `ε = √(1 + 4 L² E / (k² e⁴ m))`, where `E` and `L` are the total energy and
  the magnitude of the total angular momentum.
* Problem Hint 2: the conic trajectory in polar coordinates about the CM is
  `r(θ) = p / (1 - ε cos θ)` (the problem calls the semi-latus rectum "`a`";
  we name it `p = semiLatus`).
* Kepler/Coulomb semi-latus-rectum relation for the relative motion of the
  equal-mass pair (reduced mass `m_red = m/2`, coupling `k e²`):
  `p = L² / (m_red · k e²)`.  This is a general consequence of Newtonian
  dynamics with the Coulomb force (the only interaction admitted by the stem);
  it is a governing law, not the requested answer.

## Answer-blind derived candidate

From problem-side data only: `r_max / a₀ = 1600 / 9` (≈ 177.78).  No official
answer was consulted; see the task-result file for the derivation chain.

Blueprint label: `thm:physics:ipho_2026_t1_b1:target`.
-/

import Mathlib

namespace IPhO2026T1B1

/-- Parameters of the classical electron–positron two-body system of
IPhO 2026 T1-B.  Every field is a scalar physical parameter (SI roles are
recorded in the docstrings); positivity of the mass, charge magnitude,
permittivity and `ℏ` is part of the data. -/
structure ElectronPositronPair where
  /-- Common mass `m` of the electron and the positron [kg]. -/
  m : ℝ
  /-- Elementary charge magnitude `e`; the charges are `+e` and `-e` [C]. -/
  e : ℝ
  /-- Vacuum permittivity `ε₀` [F/m]. -/
  eps0 : ℝ
  /-- Reduced Planck constant `ℏ` [J·s]. -/
  hbar : ℝ
  /-- Dimensionless factor `μ`: each particle carries angular momentum of
  magnitude `μ ℏ` about the centre of mass. -/
  mu : ℝ
  m_pos : 0 < m
  e_pos : 0 < e
  eps0_pos : 0 < eps0
  hbar_pos : 0 < hbar

namespace ElectronPositronPair

variable (P : ElectronPositronPair)

/-- Coulomb constant `k = 1 / (4 π ε₀)` (given in the problem). -/
noncomputable def coulombK : ℝ := 1 / (4 * Real.pi * P.eps0)

/-- Bohr radius `a₀ = 4 π ε₀ ℏ² / (m e²)` (given in the problem). -/
noncomputable def bohrRadius : ℝ := 4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2)

/-- Initial electron–positron separation `r₀ = 100 a₀` (figure readout,
Fig. 1b). -/
noncomputable def initialSeparation : ℝ := 100 * P.bohrRadius

/-- Reduced mass of the equal-mass pair, `m_red = m / 2`: the relative
coordinate `r = r_{e⁺} - r_{e⁻}` obeys a one-body Coulomb problem with this
mass. -/
noncomputable def reducedMass : ℝ := P.m / 2

/-- Total angular-momentum magnitude about the CM, `L = 2 μ ℏ`: each particle
contributes `μ ℏ`, and the two contributions point along the same axis with the
same sense, because the position vectors from the CM and the velocities are
both antiparallel (Fig. 1b). -/
def totalAngularMomentum : ℝ := 2 * P.mu * P.hbar

/-- Total (conserved) energy of the isolated pair, evaluated at the initial
instant.  The initial velocities are perpendicular to the separation, so the
motion is purely tangential there; with moment of inertia about the CM
`I = 2 m (r₀/2)² = m r₀² / 2` the kinetic energy is `L² / (2 I) = L² / (m r₀²)`,
and the Coulomb potential energy is `-k e² / r₀`:
`E = L² / (m r₀²) - k e² / r₀`. -/
noncomputable def totalEnergy : ℝ :=
  P.totalAngularMomentum ^ 2 / (P.m * P.initialSeparation ^ 2)
    - P.coulombK * P.e ^ 2 / P.initialSeparation

end ElectronPositronPair

/-- Governing laws of the classical Coulomb (Kepler) orbit traced by the
relative motion of the pair.  This packages the two hints printed on the
problem page together with the standard semi-latus-rectum relation as
equational hypotheses; none of the fields is the requested T1-B1 output, and
all three fields are pinned exactly by the three equations, so the orbit data
admit no free interpretation. -/
structure CoulombOrbitLaws (P : ElectronPositronPair) where
  /-- Eccentricity `ε` of the conic trajectory. -/
  ecc : ℝ
  /-- Semi-latus rectum `p` of the conic (denoted "`a`" in Hint 2 of the
  problem). -/
  semiLatus : ℝ
  /-- Electron–positron separation `r` as a function of the polar angle `θ`
  about the centre of mass (the conic trajectory of the relative motion). -/
  separation : ℝ → ℝ
  /-- Problem Hint 1: `ε = √(1 + 4 L² E / (k² e⁴ m))`. -/
  hint1 : ecc = Real.sqrt (1 + 4 * P.totalAngularMomentum ^ 2 * P.totalEnergy /
    (P.coulombK ^ 2 * P.e ^ 4 * P.m))
  /-- Problem Hint 2: `r(θ) = p / (1 - ε cos θ)`. -/
  hint2 : ∀ θ : ℝ, separation θ = semiLatus / (1 - ecc * Real.cos θ)
  /-- Semi-latus-rectum relation of the Kepler/Coulomb problem for the relative
  motion (reduced mass `m/2`, coupling `k e²`): `p = L² / ((m/2) · k e²)`. -/
  semiLatus_eq : semiLatus =
    P.totalAngularMomentum ^ 2 / (P.reducedMass * P.coulombK * P.e ^ 2)

/-- The maximum electron–positron separation along the orbit: the supremum of
the separation `r(θ)` over all polar angles.  For a bound orbit (`ε < 1`) this
is the apoapsis value `p / (1 - ε)`. -/
noncomputable def maxSeparation (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) : ℝ :=
  sSup (Set.range laws.separation)

/-- The minimum electron–positron separation along the orbit: the infimum of
`r(θ)`; for a bound orbit this is the periapsis value `p / (1 + ε)`. -/
noncomputable def minSeparation (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) : ℝ :=
  sInf (Set.range laws.separation)

/-- The Coulomb constant is positive. -/
lemma coulombK_pos (P : ElectronPositronPair) : 0 < P.coulombK := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hε : (0 : ℝ) < P.eps0 := P.eps0_pos
  show 0 < 1 / (4 * Real.pi * P.eps0)
  positivity

/-- The Bohr radius is positive. -/
lemma bohrRadius_pos (P : ElectronPositronPair) : 0 < P.bohrRadius := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hm : (0 : ℝ) < P.m := P.m_pos
  have he : (0 : ℝ) < P.e := P.e_pos
  have hε : (0 : ℝ) < P.eps0 := P.eps0_pos
  have hh : (0 : ℝ) < P.hbar := P.hbar_pos
  show 0 < 4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2)
  positivity

/-- The initial separation `100 a₀` is positive. -/
lemma initialSeparation_pos (P : ElectronPositronPair) :
    0 < P.initialSeparation := by
  have hA : (0 : ℝ) < P.bohrRadius := bohrRadius_pos P
  show 0 < 100 * P.bohrRadius
  positivity

/-- The eccentricity delivered by Hint 1 is nonnegative, since it is a square
root. -/
lemma ecc_nonneg (P : ElectronPositronPair) (laws : CoulombOrbitLaws P) :
    0 ≤ laws.ecc := by
  rw [laws.hint1]; exact Real.sqrt_nonneg _

/-- For `μ = 4` the total energy is negative: the pair is bound, as stated in
the problem ("If μ = 4, the system is bound").  This is recorded as a
*derivable consequence* of the initial data
(`E = -(9/2500) · ℏ² / (m a₀²)`), not as a premise. -/
lemma totalEnergy_neg_of_mu_eq_four (P : ElectronPositronPair) (hμ : P.mu = 4) :
    P.totalEnergy < 0 := by
  have hm : P.m ≠ 0 := ne_of_gt P.m_pos
  have he : P.e ≠ 0 := ne_of_gt P.e_pos
  have hε : P.eps0 ≠ 0 := ne_of_gt P.eps0_pos
  have hh : P.hbar ≠ 0 := ne_of_gt P.hbar_pos
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hA : (0 : ℝ) < P.bohrRadius := bohrRadius_pos P
  -- Exact evaluation at `μ = 4`: with `L = 8 ℏ`, `r₀ = 100 a₀` and
  -- `k e² = ℏ² / (m a₀)` (the definition of `a₀`),
  -- `E = 64 ℏ²/(m (100 a₀)²) - k e²/(100 a₀) = -(36/10000) · ℏ²/(m a₀²)`.
  have hE : P.totalEnergy =
      -(36 / 10000) * (P.hbar ^ 2 / (P.m * P.bohrRadius ^ 2)) := by
    show (2 * P.mu * P.hbar) ^ 2 /
          (P.m * (100 * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2))) ^ 2) -
        (1 / (4 * Real.pi * P.eps0)) * P.e ^ 2 /
          (100 * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2))) =
        -(36 / 10000) * (P.hbar ^ 2 /
          (P.m * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2)) ^ 2))
    rw [hμ]
    field_simp
    ring
  rw [hE]
  exact mul_neg_of_neg_of_pos (by norm_num)
    (div_pos (pow_pos P.hbar_pos 2) (mul_pos P.m_pos (pow_pos hA 2)))

/-- Apoapsis formula: for a bound conic (`ε < 1`), the maximum separation is
`p / (1 - ε)`, attained at `cos θ = 1`.  This is the bridge from the
supremum definition of `maxSeparation` to the closed form, using Hint 2 and
`Real.cos θ ∈ [-1, 1]`. -/
lemma maxSeparation_eq_apoapsis (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hecc : laws.ecc < 1) :
    maxSeparation P laws = laws.semiLatus / (1 - laws.ecc) := by
  have hε0 : 0 ≤ laws.ecc := ecc_nonneg P laws
  have h1ε : (0 : ℝ) < 1 - laws.ecc := by linarith
  -- The semi-latus rectum is nonnegative from the Kepler/Coulomb relation
  -- (`p = L²/((m/2) k e²)` with positive denominator).
  have hp : 0 ≤ laws.semiLatus := by
    rw [laws.semiLatus_eq]
    show 0 ≤ P.totalAngularMomentum ^ 2 / (P.m / 2 * P.coulombK * P.e ^ 2)
    have hk : (0 : ℝ) < P.coulombK := coulombK_pos P
    have hm : (0 : ℝ) < P.m := P.m_pos
    have he : (0 : ℝ) < P.e := P.e_pos
    positivity
  -- Pointwise upper bound: `r(θ) = p/(1 - ε cos θ) ≤ p/(1 - ε)`, since
  -- `cos θ ≤ 1`, `ε ≥ 0`, `p ≥ 0` and the denominators are positive.
  have hbound : ∀ θ : ℝ, laws.separation θ ≤ laws.semiLatus / (1 - laws.ecc) := by
    intro θ
    rw [laws.hint2 θ]
    have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hεc : laws.ecc * Real.cos θ ≤ laws.ecc := by
      have h := mul_le_mul_of_nonneg_left hc hε0
      rwa [mul_one] at h
    have hD : 1 - laws.ecc ≤ 1 - laws.ecc * Real.cos θ := by linarith
    have hDpos : 0 < 1 - laws.ecc * Real.cos θ := by linarith
    rw [div_le_div_iff₀ hDpos h1ε]
    exact mul_le_mul_of_nonneg_left hD hp
  have hBdd : BddAbove (Set.range laws.separation) := by
    refine ⟨laws.semiLatus / (1 - laws.ecc), ?_⟩
    rintro y ⟨θ, rfl⟩
    exact hbound θ
  show sSup (Set.range laws.separation) = laws.semiLatus / (1 - laws.ecc)
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨θ, rfl⟩
    exact hbound θ
  · -- The value `p/(1-ε)` is attained at `θ = 0` (`cos 0 = 1`).
    apply le_csSup hBdd
    exact ⟨0, by rw [laws.hint2, Real.cos_zero, mul_one]⟩

/-- Periapsis formula: for a bound conic (`ε < 1`), the minimum separation is
`p / (1 + ε)`, attained at `cos θ = -1`. -/
lemma minSeparation_eq_periapsis (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hecc : laws.ecc < 1) :
    minSeparation P laws = laws.semiLatus / (1 + laws.ecc) := by
  have hε0 : 0 ≤ laws.ecc := ecc_nonneg P laws
  have h1ε : (0 : ℝ) < 1 - laws.ecc := by linarith
  have h1ε' : (0 : ℝ) < 1 + laws.ecc := by linarith
  -- The semi-latus rectum is nonnegative from the Kepler/Coulomb relation.
  have hp : 0 ≤ laws.semiLatus := by
    rw [laws.semiLatus_eq]
    show 0 ≤ P.totalAngularMomentum ^ 2 / (P.m / 2 * P.coulombK * P.e ^ 2)
    have hk : (0 : ℝ) < P.coulombK := coulombK_pos P
    have hm : (0 : ℝ) < P.m := P.m_pos
    have he : (0 : ℝ) < P.e := P.e_pos
    positivity
  -- Pointwise lower bound: `r(θ) = p/(1 - ε cos θ) ≥ p/(1 + ε)`, since
  -- `-1 ≤ cos θ`, `ε ≥ 0`, `p ≥ 0` and the denominators are positive.
  have hbound : ∀ θ : ℝ, laws.semiLatus / (1 + laws.ecc) ≤ laws.separation θ := by
    intro θ
    rw [laws.hint2 θ]
    have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hc2 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    have hεc1 : laws.ecc * Real.cos θ ≤ laws.ecc := by
      have h := mul_le_mul_of_nonneg_left hc1 hε0
      rwa [mul_one] at h
    have hεc2 : -laws.ecc ≤ laws.ecc * Real.cos θ := by
      have h := mul_le_mul_of_nonneg_left hc2 hε0
      rwa [mul_neg, mul_one] at h
    have hD : 1 - laws.ecc * Real.cos θ ≤ 1 + laws.ecc := by linarith
    have hDpos : 0 < 1 - laws.ecc * Real.cos θ := by linarith
    rw [div_le_div_iff₀ h1ε' hDpos]
    exact mul_le_mul_of_nonneg_left hD hp
  have hBdd : BddBelow (Set.range laws.separation) := by
    refine ⟨laws.semiLatus / (1 + laws.ecc), ?_⟩
    rintro y ⟨θ, rfl⟩
    exact hbound θ
  show sInf (Set.range laws.separation) = laws.semiLatus / (1 + laws.ecc)
  apply le_antisymm
  · -- The value `p/(1+ε)` is attained at `θ = π` (`cos π = -1`).
    apply csInf_le hBdd
    exact ⟨Real.pi, by rw [laws.hint2, Real.cos_pi]; congr 1; ring⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨θ, rfl⟩
    exact hbound θ

/-- With `μ = 4`, Hint 1 evaluates to `ε = 7 / 25`:
`4 L² E / (k² e⁴ m) = -9216 / 10000`, so `ε² = 49 / 625`. -/
lemma ecc_eq_of_mu_eq_four (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hμ : P.mu = 4) :
    laws.ecc = 7 / 25 := by
  have hm : P.m ≠ 0 := ne_of_gt P.m_pos
  have he : P.e ≠ 0 := ne_of_gt P.e_pos
  have hε : P.eps0 ≠ 0 := ne_of_gt P.eps0_pos
  have hh : P.hbar ≠ 0 := ne_of_gt P.hbar_pos
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  -- Exact energy evaluation at `μ = 4` (same computation as in
  -- `totalEnergy_neg_of_mu_eq_four`): `E = -(36/10000) · ℏ²/(m a₀²)`.
  have hE : P.totalEnergy =
      -(36 / 10000) * (P.hbar ^ 2 / (P.m * P.bohrRadius ^ 2)) := by
    show (2 * P.mu * P.hbar) ^ 2 /
          (P.m * (100 * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2))) ^ 2) -
        (1 / (4 * Real.pi * P.eps0)) * P.e ^ 2 /
          (100 * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2))) =
        -(36 / 10000) * (P.hbar ^ 2 /
          (P.m * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2)) ^ 2))
    rw [hμ]
    field_simp
    ring
  -- Hint 1 argument evaluates to `(7/25)²`: `4L²E/(k²e⁴m) = -9216/10000`,
  -- so `1 + 4L²E/(k²e⁴m) = 784/10000 = 49/625`.
  have hkey : 1 + 4 * P.totalAngularMomentum ^ 2 * P.totalEnergy /
      (P.coulombK ^ 2 * P.e ^ 4 * P.m) = (7 / 25 : ℝ) ^ 2 := by
    rw [hE]
    show 1 + 4 * (2 * P.mu * P.hbar) ^ 2 *
        (-(36 / 10000) * (P.hbar ^ 2 /
          (P.m * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2)) ^ 2))) /
        ((1 / (4 * Real.pi * P.eps0)) ^ 2 * P.e ^ 4 * P.m) = (7 / 25 : ℝ) ^ 2
    rw [hμ]
    field_simp
    ring
  rw [laws.hint1, hkey, Real.sqrt_sq (show (0 : ℝ) ≤ 7 / 25 by norm_num)]

/-- With `μ = 4` the orbit is eccentricity-`< 1`, i.e. bound. -/
lemma ecc_lt_one_of_mu_eq_four (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hμ : P.mu = 4) :
    laws.ecc < 1 := by
  rw [ecc_eq_of_mu_eq_four P laws hμ]
  norm_num

/-- With `μ = 4` the semi-latus rectum is positive. -/
lemma semiLatus_pos_of_mu_eq_four (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hμ : P.mu = 4) :
    0 < laws.semiLatus := by
  have hk : (0 : ℝ) < P.coulombK := coulombK_pos P
  have hm : (0 : ℝ) < P.m := P.m_pos
  have he : (0 : ℝ) < P.e := P.e_pos
  have hh : (0 : ℝ) < P.hbar := P.hbar_pos
  have hL : P.totalAngularMomentum = 8 * P.hbar := by
    show 2 * P.mu * P.hbar = 8 * P.hbar
    rw [hμ]; ring
  rw [laws.semiLatus_eq, hL]
  show 0 < (8 * P.hbar) ^ 2 / (P.m / 2 * P.coulombK * P.e ^ 2)
  positivity

/-- With `μ = 4`, the semi-latus-rectum relation evaluates to
`p = 128 a₀` (using `k e² = ℏ² / (m a₀)`, which is the definition of `a₀`). -/
lemma semiLatus_eq_of_mu_eq_four (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hμ : P.mu = 4) :
    laws.semiLatus = 128 * P.bohrRadius := by
  have hm : P.m ≠ 0 := ne_of_gt P.m_pos
  have he : P.e ≠ 0 := ne_of_gt P.e_pos
  have hε : P.eps0 ≠ 0 := ne_of_gt P.eps0_pos
  have hh : P.hbar ≠ 0 := ne_of_gt P.hbar_pos
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hL : P.totalAngularMomentum = 8 * P.hbar := by
    show 2 * P.mu * P.hbar = 8 * P.hbar
    rw [hμ]; ring
  rw [laws.semiLatus_eq, hL]
  -- `(8ℏ)² / ((m/2) k e²) = 64 ℏ² · 8 π ε₀ / (m e²) = 128 · 4 π ε₀ ℏ²/(m e²)`.
  show (8 * P.hbar) ^ 2 / (P.m / 2 * (1 / (4 * Real.pi * P.eps0)) * P.e ^ 2) =
      128 * (4 * Real.pi * P.eps0 * P.hbar ^ 2 / (P.m * P.e ^ 2))
  field_simp
  ring

/-- Consistency with Fig. 1b: the initial separation `100 a₀` is the periapsis
of the bound orbit (the initial velocities are perpendicular to the separation,
hence the radial velocity vanishes at the initial instant, so it is an apsis;
numerically it is the minimum, `p / (1 + ε) = 128 a₀ / (32/25) = 100 a₀`). -/
lemma minSeparation_eq_initial (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hμ : P.mu = 4) :
    minSeparation P laws = P.initialSeparation := by
  rw [minSeparation_eq_periapsis P laws (ecc_lt_one_of_mu_eq_four P laws hμ),
    ecc_eq_of_mu_eq_four P laws hμ, semiLatus_eq_of_mu_eq_four P laws hμ]
  show 128 * P.bohrRadius / (1 + 7 / 25) = 100 * P.bohrRadius
  rw [div_eq_iff (by norm_num : (1 + 7 / 25 : ℝ) ≠ 0)]
  ring

/-- **T1-B1 target** (blueprint `thm:physics:ipho_2026_t1_b1:target`).
For `μ = 4` (bound pair), the maximum electron–positron separation along the
orbit is `(1600 / 9) · a₀ ≈ 177.78 a₀`:
`r_max = p / (1 - ε) = 128 a₀ / (1 - 7/25) = 128 a₀ · 25 / 18 = 1600 a₀ / 9`. -/
theorem max_separation_eq (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hμ : P.mu = 4) :
    maxSeparation P laws = 1600 / 9 * P.bohrRadius := by
  rw [maxSeparation_eq_apoapsis P laws (ecc_lt_one_of_mu_eq_four P laws hμ),
    ecc_eq_of_mu_eq_four P laws hμ, semiLatus_eq_of_mu_eq_four P laws hμ]
  rw [div_eq_iff (by norm_num : (1 - 7 / 25 : ℝ) ≠ 0)]
  ring

/-- The requested output "in units of `a₀`": the dimensionless ratio
`r_max / a₀` equals `1600 / 9`.  The problem asks for an exact symbolic
multiple of `a₀`, so no rounding rule applies. -/
theorem max_separation_over_bohrRadius (P : ElectronPositronPair)
    (laws : CoulombOrbitLaws P) (hμ : P.mu = 4) :
    maxSeparation P laws / P.bohrRadius = 1600 / 9 := by
  rw [max_separation_eq P laws hμ, div_eq_iff (ne_of_gt (bohrRadius_pos P))]

end IPhO2026T1B1
