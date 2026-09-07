/-
# IPhO 2026 — Theory Problem 1, Part C1
## Photodissociation of ozone: minimum angular frequency for dissociation
## with the O₂ emitted at angle θ

### Physical scenario (T1-C, Fig. 1c)

A photon of angular frequency `ω` strikes an ozone molecule O₃ **at rest** and
is absorbed, dissociating the molecule into an oxygen molecule O₂ and an oxygen
atom O.  The outgoing O₂ momentum makes an angle `θ` with the incident photon
direction (in Fig. 1c the O₂ recoils above the photon axis, the O below).
The system is isolated; the fragments are treated classically and
non-relativistically (potential energies do not contribute to the mass
bookkeeping), and the photon obeys the stipulated relation `p = E/c`.

* `U_i`, `U_f` — ground-state energies of O₃ and O₂; `ΔU = U_f − U_i > 0` is
  the dissociation energy.
* `m` — mass of one oxygen atom, so the O₂ fragment has mass `2m`, the O atom
  mass `m`, and the initial O₃ molecule mass `3m`.
* Photon: energy `E_γ = ℏω`, momentum `p_γ = E_γ/c = ℏω/c`.

### Subquestion T1-C1

Determine the minimum angular frequency `ω_min` required for the dissociation
to occur with the O₂ emitted at angle `θ`, in terms of `ℏ`, `c`, `θ`,
`ΔU = U_f − U_i`, and `m`.  (Symbolic formula question — no numerical data,
hence no rounding rule or uncertainty propagation applies.)

### Formalization overview

* `OzonePhotodissociation` — parameter bundle with the physical sign
  constraints.
* `DissociationEvent` — a kinematically admissible final state: the two
  components of momentum conservation and the energy-conservation equation.
* `FeasibleAt`, `feasibleFreqs` — feasibility of the dissociation at a given
  angle and frequency.
* `omegaMinFormula` — the candidate closed form for `ω_min`, derived
  answer-blind from the conservation laws:
  `ω_min = 6 m c² ΔU / (ℏ (3 m c² + √(9 m²c⁴ − 6 m c² ΔU (3 − 2 cos²θ))))`.
* `isLeast_feasibleFreqs` — the main theorem: `omegaMinFormula θ` is the least
  feasible positive frequency.

All quantities are real scalars in a fixed consistent unit system; momenta are
represented by their Cartesian components in the scattering plane, with the
`x`-axis along the incident photon momentum and the O₂ on the `+θ` side as in
Fig. 1c (the mirror branch `-θ` is equivalent, see `feasibleAt_neg_angle`).
-/

import Mathlib

namespace IPhO2026.T1C1

/-- Parameter bundle for the ozone photodissociation problem (IPhO 2026 T1-C).

* `ℏ` — reduced Planck constant (energy·time),
* `c` — speed of light (length/time),
* `m` — mass of a single oxygen atom,
* `Ui`, `Uf` — ground-state energies of O₃ and O₂.

The sign hypotheses encode the physical setting: the constants are positive,
and dissociation costs energy (`Ui < Uf`).  All scalars are reals in a fixed
consistent unit system. -/
structure OzonePhotodissociation where
  /-- Reduced Planck constant `ℏ`. -/
  ℏ : ℝ
  /-- Speed of light `c`. -/
  c : ℝ
  /-- Mass `m` of one oxygen atom. -/
  m : ℝ
  /-- Ground-state energy `U_i` of the ozone molecule O₃. -/
  Ui : ℝ
  /-- Ground-state energy `U_f` of the oxygen molecule O₂. -/
  Uf : ℝ
  hℏ : 0 < ℏ
  hc : 0 < c
  hm : 0 < m
  /-- Dissociation costs energy: `ΔU = U_f − U_i > 0`. -/
  hU : Ui < Uf

namespace OzonePhotodissociation

/-- The dissociation energy `ΔU = U_f − U_i`. -/
def ΔU (D : OzonePhotodissociation) : ℝ := D.Uf - D.Ui

/-- Mass of the outgoing O₂ fragment (two oxygen atoms). -/
def mO2 (D : OzonePhotodissociation) : ℝ := 2 * D.m

/-- Mass of the outgoing oxygen atom O. -/
def mO (D : OzonePhotodissociation) : ℝ := D.m

/-- Mass of the initial O₃ molecule (three oxygen atoms).  It enters the
kinematics only through O₃ being initially at rest — zero initial kinetic
energy and zero initial momentum beyond the photon's — because the dynamics is
classical and potential energies do not contribute to mass. -/
def mO3 (D : OzonePhotodissociation) : ℝ := 3 * D.m

/-- Photon energy at angular frequency `ω`: `E_γ = ℏω`. -/
def photonEnergy (D : OzonePhotodissociation) (ω : ℝ) : ℝ := D.ℏ * ω

/-- Photon linear momentum, the relation `p = E/c` stipulated by the problem:
`p_γ = ℏω/c`. -/
noncomputable def photonMomentum (D : OzonePhotodissociation) (ω : ℝ) : ℝ :=
  D.photonEnergy ω / D.c

theorem ΔU_pos (D : OzonePhotodissociation) : 0 < D.ΔU := sub_pos.mpr D.hU

theorem mO2_pos (D : OzonePhotodissociation) : 0 < D.mO2 :=
  mul_pos zero_lt_two D.hm

/-- Helper expansion of the stipulated photon momentum relation. -/
theorem photonMomentum_eq (D : OzonePhotodissociation) (ω : ℝ) :
    D.photonMomentum ω = D.ℏ * ω / D.c := rfl

/-- A kinematically admissible dissociation event with the O₂ emitted at angle
`θ` relative to the incident photon and photon angular frequency `ω`.

We work in the scattering plane with the `x`-axis along the incident photon
momentum (Fig. 1c).  The O₂ momentum is `p • (cos θ, sin θ)` with `p > 0` — the
`+θ` branch of Fig. 1c — and `(qx, qy)` is the momentum of the oxygen atom.

The fields are the governing laws of the problem:

* `momX`, `momY` — conservation of linear momentum; the initial momentum is
  the photon's alone because O₃ is at rest and the system is isolated;
* `energy` — conservation of energy,
  `ℏω + U_i = U_f + p²/(2(2m)) + (qx² + qy²)/(2m)`, with classical
  non-relativistic kinetic energies of the fragments. -/
structure DissociationEvent (D : OzonePhotodissociation) (θ ω : ℝ) where
  /-- Magnitude `p > 0` of the O₂ momentum. -/
  p : ℝ
  /-- `x`-component of the O-atom momentum. -/
  qx : ℝ
  /-- `y`-component of the O-atom momentum. -/
  qy : ℝ
  hp : 0 < p
  /-- `x`-component of momentum conservation: `ℏω/c = qx + p cos θ`. -/
  momX : D.photonMomentum ω = qx + p * Real.cos θ
  /-- `y`-component of momentum conservation: `0 = qy + p sin θ`. -/
  momY : 0 = qy + p * Real.sin θ
  /-- Energy conservation with classical fragment kinetic energies:
  `ℏω + U_i = U_f + p²/(2(2m)) + (qx² + qy²)/(2m)`. -/
  energy : D.photonEnergy ω + D.Ui =
    D.Uf + p ^ 2 / (2 * D.mO2) + (qx ^ 2 + qy ^ 2) / (2 * D.mO)

/-- Dissociation with the O₂ emitted at angle `θ` is feasible at photon angular
frequency `ω`: a kinematically admissible final state exists. -/
def FeasibleAt (D : OzonePhotodissociation) (θ ω : ℝ) : Prop :=
  Nonempty (D.DissociationEvent θ ω)

/-- The set of positive angular frequencies at which the dissociation can occur
with the O₂ emitted at angle `θ`. -/
def feasibleFreqs (D : OzonePhotodissociation) (θ : ℝ) : Set ℝ :=
  {ω | 0 < ω ∧ D.FeasibleAt θ ω}

/-- Momentum conservation determines the O-atom momentum
`q = (ℏω/c − p cos θ, −p sin θ)`, so feasibility is equivalent to the existence
of a positive O₂ momentum magnitude satisfying the single scalar energy
balance.  (Bridge: eliminates the recoil momentum via the two momentum
components.) -/
theorem feasibleAt_iff_exists_p (D : OzonePhotodissociation) (θ ω : ℝ) :
    D.FeasibleAt θ ω ↔
      ∃ p : ℝ, 0 < p ∧
        D.photonEnergy ω = D.ΔU +
          p ^ 2 / (2 * D.mO2) +
            ((D.photonMomentum ω - p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2) /
              (2 * D.mO) := by
  constructor
  · intro h
    obtain ⟨ev⟩ := h
    refine ⟨ev.p, ev.hp, ?_⟩
    have hqx : ev.qx = D.photonMomentum ω - ev.p * Real.cos θ := by linarith [ev.momX]
    have hqy : ev.qy = -(ev.p * Real.sin θ) := by linarith [ev.momY]
    have hqy2 : ev.qy ^ 2 = (ev.p * Real.sin θ) ^ 2 := by rw [hqy]; ring
    have hΔ : D.ΔU = D.Uf - D.Ui := rfl
    have hen := ev.energy
    rw [hqx, hqy2] at hen
    linarith [hen, hΔ]
  · rintro ⟨p, hp, hE⟩
    refine ⟨⟨p, D.photonMomentum ω - p * Real.cos θ, -(p * Real.sin θ), hp, ?_, ?_, ?_⟩⟩
    · ring
    · ring
    · have hΔ : D.ΔU = D.Uf - D.Ui := rfl
      have h2 : (-(p * Real.sin θ)) ^ 2 = (p * Real.sin θ) ^ 2 := by ring
      rw [h2]
      linarith [hE, hΔ]

/-- Algebraic core of the threshold condition.  With `pg = E/c` the photon
momentum, `cs = cos θ`, `sn = sin θ` satisfying `cs² + sn² = 1`, `cs > 0` and
`E > 0`, a positive fragment-momentum magnitude `p` balancing energy and
momentum exists iff the quadratic `(3 − 2cs²)E² − 6mc²E + 6mc²ΔU` is
nonpositive.  Proof by completing the square in `p`: the energy/momentum
balance is equivalent to `3(p − p₀)² + K = 0` with vertex
`p₀ = 2pg·cs/3 > 0` and `K = (2/(3c²))·Q(E)`, so a positive root exists iff
`K ≤ 0` iff `Q(E) ≤ 0`. -/
theorem exists_pos_momentum_balance_iff_quadratic {E pg c m ΔU cs sn : ℝ}
    (hm : 0 < m) (hc : 0 < c) (_hΔ : 0 < ΔU)
    (hpg : pg = E / c) (hcsn : cs ^ 2 + sn ^ 2 = 1) (hcs : 0 < cs) (hE : 0 < E) :
    (∃ p : ℝ, 0 < p ∧
        E = ΔU + p ^ 2 / (2 * (2 * m)) + ((pg - p * cs) ^ 2 + (p * sn) ^ 2) / (2 * m))
      ↔ (3 - 2 * cs ^ 2) * E ^ 2 - 6 * m * c ^ 2 * E + 6 * m * c ^ 2 * ΔU ≤ 0 := by
  have hcn : c ≠ 0 := ne_of_gt hc
  have hmn : m ≠ 0 := ne_of_gt hm
  have hpgpos : 0 < pg := by rw [hpg]; exact div_pos hE hc
  have hpgsq : c ^ 2 * pg ^ 2 = E ^ 2 := by
    rw [hpg]; field_simp
  -- `Q(E) = (3c²/2)·K` where `K` is the value of the momentum quadratic at its
  -- vertex; this converts the discriminant condition into a sign condition on `K`.
  have hQK : (3 - 2 * cs ^ 2) * E ^ 2 - 6 * m * c ^ 2 * E + 6 * m * c ^ 2 * ΔU
      = (3 * c ^ 2 / 2) * (4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3) := by
    linear_combination (-(3 - 2 * cs ^ 2)) * hpgsq
  have h32 : (0 : ℝ) < 3 * c ^ 2 / 2 := by linarith [pow_pos hc 2]
  constructor
  · rintro ⟨p, hp, hbal⟩
    have hbal4 : 4 * m * E
        = 4 * m * ΔU + p ^ 2 + 2 * ((pg - p * cs) ^ 2 + (p * sn) ^ 2) := by
      rw [hbal]; field_simp; ring
    have hsq : 3 * (p - 2 * pg * cs / 3) ^ 2
        + (4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3) = 0 := by
      linear_combination (-1) * hbal4 + (-2 * p ^ 2) * hcsn
    have hnn : 0 ≤ 3 * (p - 2 * pg * cs / 3) ^ 2 := by positivity
    have hK : (4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3) ≤ 0 := by
      linarith [hsq, hnn]
    rw [hQK]
    exact mul_nonpos_of_nonneg_of_nonpos h32.le hK
  · intro hQ
    rw [hQK] at hQ
    have hK : (4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3) ≤ 0 := by
      rcases mul_nonpos_iff.mp hQ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · linarith [h32, h1]
    have hKval : (0 : ℝ) ≤ (-(4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3)) / 3 :=
      div_nonneg (by linarith [hK]) (by norm_num)
    set W : ℝ := 2 * pg * cs / 3
        + Real.sqrt ((-(4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3)) / 3) with hW
    have hWsub : W - 2 * pg * cs / 3
        = Real.sqrt ((-(4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3)) / 3) := by
      rw [hW]; ring
    have hWsq : (W - 2 * pg * cs / 3) ^ 2
        = (-(4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3)) / 3 := by
      rw [hWsub]; exact Real.sq_sqrt hKval
    have hsq : 3 * (W - 2 * pg * cs / 3) ^ 2
        + (4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3) = 0 := by
      rw [hWsq]; ring
    refine ⟨W, ?_, ?_⟩
    · have h2pgcs : (0 : ℝ) < 2 * pg * cs := mul_pos (mul_pos (by norm_num) hpgpos) hcs
      have hsqrt : (0 : ℝ) ≤
          Real.sqrt ((-(4 * m * ΔU + 2 * pg ^ 2 - 4 * m * E - 4 * pg ^ 2 * cs ^ 2 / 3)) / 3) :=
        Real.sqrt_nonneg _
      rw [hW]; linarith [h2pgcs, hsqrt]
    · have hbal4 : 4 * m * E
          = 4 * m * ΔU + W ^ 2 + 2 * ((pg - W * cs) ^ 2 + (W * sn) ^ 2) := by
        linear_combination (-1) * hsq + (-(2 * W ^ 2)) * hcsn
      field_simp
      linear_combination hbal4

/-- For the acute emission branch of Fig. 1c (`cos θ > 0`) and positive photon
frequency, feasibility is equivalent to the discriminant condition of the
momentum quadratic `3p² − 4(E/c)cosθ·p + (2E²/c² + 4mΔU − 4mE) = 0`, i.e. to
the photon energy `E = ℏω` lying between the two roots of
`(3 − 2cos²θ) E² − 6mc² E + 6mc²ΔU = 0`. -/
theorem feasibleAt_iff_quadratic (D : OzonePhotodissociation) {θ ω : ℝ}
    (hθ : 0 < Real.cos θ) (hω : 0 < ω) :
    D.FeasibleAt θ ω ↔
      (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy ω ^ 2 -
          6 * D.m * D.c ^ 2 * D.photonEnergy ω +
        6 * D.m * D.c ^ 2 * D.ΔU ≤ 0 := by
  rw [feasibleAt_iff_exists_p]
  have hE : 0 < D.photonEnergy ω := mul_pos D.hℏ hω
  have hpg : D.photonMomentum ω = D.photonEnergy ω / D.c := rfl
  have hcsn : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  exact exists_pos_momentum_balance_iff_quadratic D.hm D.hc D.ΔU_pos hpg hcsn hθ hE

/-- The mirror branch: feasibility at angle `-θ` coincides with feasibility at
`θ` (reflect the O-atom transverse momentum), so restricting to the `+θ` branch
of Fig. 1c is without loss of generality. -/
theorem feasibleAt_neg_angle (D : OzonePhotodissociation) (θ ω : ℝ) :
    D.FeasibleAt (-θ) ω ↔ D.FeasibleAt θ ω := by
  have step : ∀ φ : ℝ, D.FeasibleAt φ ω → D.FeasibleAt (-φ) ω := by
    intro φ h
    obtain ⟨ev⟩ := h
    refine ⟨⟨ev.p, ev.qx, -ev.qy, ev.hp, ?_, ?_, ?_⟩⟩
    · rw [Real.cos_neg]; exact ev.momX
    · rw [Real.sin_neg, mul_neg]; linarith [ev.momY]
    · rw [neg_sq]; exact ev.energy
  constructor
  · intro h
    have h' := step (-θ) h
    rwa [neg_neg] at h'
  · intro h
    exact step θ h

/-- Candidate minimum angular frequency, derived answer-blind from the
conservation laws (the smaller root of the kinematic quadratic
`(3 − 2cos²θ) E² − 6mc² E + 6mc²ΔU = 0`, rationalized):

`ω_min = 6 m c² ΔU / (ℏ (3 m c² + √(9 m²c⁴ − 6 m c² ΔU (3 − 2cos²θ))))`. -/
noncomputable def omegaMinFormula (D : OzonePhotodissociation) (θ : ℝ) : ℝ :=
  6 * D.m * D.c ^ 2 * D.ΔU /
    (D.ℏ * (3 * D.m * D.c ^ 2 +
      Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))))

theorem omegaMinFormula_pos (D : OzonePhotodissociation) (θ : ℝ) :
    0 < D.omegaMinFormula θ := by
  have hnum : 0 < 6 * D.m * D.c ^ 2 * D.ΔU :=
    mul_pos (mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)) D.ΔU_pos
  have hbase : 0 < 3 * D.m * D.c ^ 2 :=
    mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)
  have hden : 0 < D.ℏ * (3 * D.m * D.c ^ 2 +
      Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) :=
    mul_pos D.hℏ (add_pos_of_pos_of_nonneg hbase (Real.sqrt_nonneg _))
  exact div_pos hnum hden

/-- The photon energy at the candidate threshold `ω_min`:
`ℏ ω_min = 6mc²ΔU / (3mc² + √(9m²c⁴ − 6mc²ΔU(3 − 2cos²θ)))`
(the `ℏ` cancels).  Pure field manipulation, valid for all `θ`. -/
theorem photonEnergy_omegaMinFormula (D : OzonePhotodissociation) (θ : ℝ) :
    D.photonEnergy (D.omegaMinFormula θ)
      = 6 * D.m * D.c ^ 2 * D.ΔU /
          (3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) := by
  have hℏ : D.ℏ ≠ 0 := ne_of_gt D.hℏ
  unfold photonEnergy omegaMinFormula
  rw [← mul_div_assoc]
  exact mul_div_mul_left _ _ hℏ

/-- The candidate threshold energy is a root of the kinematic quadratic:
`(3 − 2cos²θ)·(ℏω_min)² − 6mc²·(ℏω_min) + 6mc²ΔU = 0`.  This is the key
algebraic fact making `ω_min` the threshold.  Requires the discriminant
hypothesis so that the square root is the real one. -/
theorem quadratic_omegaMinFormula (D : OzonePhotodissociation) {θ : ℝ}
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    (3 - 2 * Real.cos θ ^ 2) * (D.photonEnergy (D.omegaMinFormula θ)) ^ 2
      - 6 * D.m * D.c ^ 2 * (D.photonEnergy (D.omegaMinFormula θ))
      + 6 * D.m * D.c ^ 2 * D.ΔU = 0 := by
  have hS : (0 : ℝ) < 3 * D.m * D.c ^ 2 :=
    mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)
  have hRarg : 0 ≤ 9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := by
    have h1 : (0 : ℝ) ≤ 3 * D.m * D.c ^ 2 - 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := by
      linarith [hDisc]
    have h2 : 9 * D.m ^ 2 * D.c ^ 4 - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)
        = (3 * D.m * D.c ^ 2) * (3 * D.m * D.c ^ 2 - 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) := by
      ring
    rw [h2]; exact mul_nonneg hS.le h1
  set R := Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) with hRdef
  have hRsq : R ^ 2 = 9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := by
    rw [hRdef]; exact Real.sq_sqrt hRarg
  have hE : D.photonEnergy (D.omegaMinFormula θ)
      = 6 * D.m * D.c ^ 2 * D.ΔU / (3 * D.m * D.c ^ 2 + R) := by
    rw [hRdef]; exact photonEnergy_omegaMinFormula D θ
  have hSR : (0 : ℝ) < 3 * D.m * D.c ^ 2 + R := by
    rw [hRdef]; exact add_pos_of_pos_of_nonneg hS (Real.sqrt_nonneg _)
  have hSRn : (3 * D.m * D.c ^ 2 + R) ≠ 0 := ne_of_gt hSR
  rw [hE]
  field_simp
  linear_combination (6 * D.m * D.c ^ 2 * D.ΔU) * hRsq

/-- Recoil makes the threshold strictly exceed the naive value `ΔU/ℏ`:
`ℏω_min > ΔU` (the excess `ℏω_min − ΔU` is the quantity that T1-C2 evaluates
numerically). -/
theorem photonEnergy_omegaMinFormula_gt (D : OzonePhotodissociation) (θ : ℝ) :
    D.ΔU < D.photonEnergy (D.omegaMinFormula θ) := by
  rw [photonEnergy_omegaMinFormula]
  have hΔ : 0 < D.ΔU := D.ΔU_pos
  have hA : (0 : ℝ) < 3 - 2 * Real.cos θ ^ 2 := by
    have h := Real.cos_sq_le_one θ; nlinarith [h]
  have hS : (0 : ℝ) < 3 * D.m * D.c ^ 2 :=
    mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)
  -- `√arg < 3mc²` whether or not `arg` is positive (if `arg ≤ 0` then `√arg = 0`).
  have hRlt : Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) < 3 * D.m * D.c ^ 2 := by
    by_cases ha : (9 * D.m ^ 2 * D.c ^ 4
        - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) ≤ 0
    · rw [Real.sqrt_eq_zero_of_nonpos ha]; exact hS
    · have hargpos : 0 ≤ 9 * D.m ^ 2 * D.c ^ 4
          - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := le_of_lt (not_le.mp ha)
      have h3 : (0 : ℝ) < 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) :=
        mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)) hΔ) hA
      have hS2 : (3 * D.m * D.c ^ 2) ^ 2 = 9 * D.m ^ 2 * D.c ^ 4 := by ring
      have h2 : 9 * D.m ^ 2 * D.c ^ 4 - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)
          < (3 * D.m * D.c ^ 2) ^ 2 := by
        rw [hS2]; linarith [h3]
      calc Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))
          < Real.sqrt ((3 * D.m * D.c ^ 2) ^ 2) := Real.sqrt_lt_sqrt hargpos h2
        _ = 3 * D.m * D.c ^ 2 := Real.sqrt_sq hS.le
  have hSR : (0 : ℝ) < 3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) :=
    add_pos_of_pos_of_nonneg hS (Real.sqrt_nonneg _)
  rw [lt_div_iff₀ hSR]
  have hRΔ : Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) * D.ΔU
      < (3 * D.m * D.c ^ 2) * D.ΔU := mul_lt_mul_of_pos_right hRlt hΔ
  nlinarith [hRΔ, hS, hΔ]

/-- Equivalent form of the minimum frequency as the smaller root of the
kinematic quadratic,
`ω_min = (3mc² − √(9m²c⁴ − 6mc²ΔU(3 − 2cos²θ))) / (ℏ(3 − 2cos²θ))`,
valid whenever the roots are real. -/
theorem omegaMinFormula_eq_rootForm (D : OzonePhotodissociation) {θ : ℝ}
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    D.omegaMinFormula θ =
      (3 * D.m * D.c ^ 2 -
          Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) /
        (D.ℏ * (3 - 2 * Real.cos θ ^ 2)) := by
  have hS : (0 : ℝ) < 3 * D.m * D.c ^ 2 :=
    mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)
  have hA : (0 : ℝ) < 3 - 2 * Real.cos θ ^ 2 := by
    have h := Real.cos_sq_le_one θ; nlinarith [h]
  have hRarg : 0 ≤ 9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := by
    have h1 : (0 : ℝ) ≤ 3 * D.m * D.c ^ 2 - 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := by
      linarith [hDisc]
    have h2 : 9 * D.m ^ 2 * D.c ^ 4 - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)
        = (3 * D.m * D.c ^ 2) * (3 * D.m * D.c ^ 2 - 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) := by
      ring
    rw [h2]; exact mul_nonneg hS.le h1
  have hRsq : Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) ^ 2
      = 9 * D.m ^ 2 * D.c ^ 4 - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) :=
    Real.sq_sqrt hRarg
  have hSR : (0 : ℝ) < 3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) :=
    add_pos_of_pos_of_nonneg hS (Real.sqrt_nonneg _)
  have hden1 : D.ℏ * (3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
      - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) ≠ 0 :=
    ne_of_gt (mul_pos D.hℏ hSR)
  have hden2 : D.ℏ * (3 - 2 * Real.cos θ ^ 2) ≠ 0 := ne_of_gt (mul_pos D.hℏ hA)
  unfold omegaMinFormula
  rw [div_eq_div_iff hden1 hden2]
  linear_combination (D.ℏ) * hRsq

/-- The threshold photon energy in root form,
`ℏ ω_min = (3mc² − √(9m²c⁴ − 6mc²ΔU(3 − 2cos²θ))) / (3 − 2cos²θ)`
(the `ℏ` cancels from `omegaMinFormula_eq_rootForm`).  Useful for reading off
`a·E_min = 3mc² − R ≤ 3mc²`. -/
theorem photonEnergy_omegaMinFormula_root (D : OzonePhotodissociation) {θ : ℝ}
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    D.photonEnergy (D.omegaMinFormula θ)
      = (3 * D.m * D.c ^ 2 - Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) /
          (3 - 2 * Real.cos θ ^ 2) := by
  have h := omegaMinFormula_eq_rootForm D hDisc
  unfold photonEnergy
  rw [h]
  rw [← mul_div_assoc]
  exact mul_div_mul_left _ _ (ne_of_gt D.hℏ)

/-- The minimum is attained: at `ω = ω_min` there is a dissociation event — the
momentum quadratic has the positive double root
`p* = (2/3)(ℏω_min/c)·cos θ > 0`. -/
theorem feasibleAt_omegaMinFormula (D : OzonePhotodissociation) {θ : ℝ}
    (hθ : 0 < θ ∧ θ < Real.pi / 2)
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    D.FeasibleAt θ (D.omegaMinFormula θ) := by
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hωpos : 0 < D.omegaMinFormula θ := omegaMinFormula_pos D θ
  rw [feasibleAt_iff_quadratic D hcos hωpos]
  exact le_of_eq (quadratic_omegaMinFormula D hDisc)

/-- **T1-C1, main result.**  For an acute emission angle `θ` (the branch of
Fig. 1c) and dissociation energy below the kinematic threshold
`2ΔU(3 − 2cos²θ) ≤ 3mc²` — overwhelmingly satisfied in the actual problem,
where `ΔU ∼ 1 eV ≪ mc²` — the least angular frequency at which the
dissociation can occur with the O₂ emitted at angle `θ` is

`ω_min = 6 m c² ΔU / (ℏ (3 m c² + √(9 m²c⁴ − 6 m c² ΔU (3 − 2cos²θ))))`. -/
theorem isLeast_feasibleFreqs (D : OzonePhotodissociation) {θ : ℝ}
    (hθ : 0 < θ ∧ θ < Real.pi / 2)
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    IsLeast (D.feasibleFreqs θ) (D.omegaMinFormula θ) := by
  have hA : (0 : ℝ) < 3 - 2 * Real.cos θ ^ 2 := by
    have h := Real.cos_sq_le_one θ; nlinarith [h]
  have hAn : (3 - 2 * Real.cos θ ^ 2) ≠ 0 := ne_of_gt hA
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  refine ⟨?_, ?_⟩
  · exact ⟨omegaMinFormula_pos D θ, feasibleAt_omegaMinFormula D hθ hDisc⟩
  · intro ω hω
    obtain ⟨hωpos, hfeas⟩ := hω
    have hQ : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy ω ^ 2
        - 6 * D.m * D.c ^ 2 * D.photonEnergy ω + 6 * D.m * D.c ^ 2 * D.ΔU ≤ 0 :=
      (feasibleAt_iff_quadratic D hcos hωpos).mp hfeas
    have hQmin : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) ^ 2
        - 6 * D.m * D.c ^ 2 * D.photonEnergy (D.omegaMinFormula θ)
        + 6 * D.m * D.c ^ 2 * D.ΔU = 0 :=
      quadratic_omegaMinFormula D hDisc
    -- `a·E_min = 3mc² − R ≤ 3mc²` from the root form of `E_min`.
    have hAEmin : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ)
        ≤ 3 * D.m * D.c ^ 2 := by
      rw [photonEnergy_omegaMinFormula_root D hDisc]
      rw [mul_div_cancel₀ _ hAn]
      have hRge : (0 : ℝ) ≤ Real.sqrt (9 * D.m ^ 2 * D.c ^ 4
          - 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) := Real.sqrt_nonneg _
      linarith [hRge]
    -- The threshold energy is a lower bound for all feasible energies.
    have hEmin_le_E : D.photonEnergy (D.omegaMinFormula θ) ≤ D.photonEnergy ω := by
      by_contra hcon
      rw [not_le] at hcon
      -- `Q(E) = Q(E) − Q(E_min) = (E − E_min)·(a(E + E_min) − 6mc²) ≤ 0`.
      have hprod : (D.photonEnergy ω - D.photonEnergy (D.omegaMinFormula θ))
          * ((3 - 2 * Real.cos θ ^ 2)
              * (D.photonEnergy ω + D.photonEnergy (D.omegaMinFormula θ))
            - 6 * D.m * D.c ^ 2) ≤ 0 := by
        have hfact : ((3 - 2 * Real.cos θ ^ 2) * D.photonEnergy ω ^ 2
            - 6 * D.m * D.c ^ 2 * D.photonEnergy ω + 6 * D.m * D.c ^ 2 * D.ΔU)
            - ((3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) ^ 2
            - 6 * D.m * D.c ^ 2 * D.photonEnergy (D.omegaMinFormula θ)
            + 6 * D.m * D.c ^ 2 * D.ΔU)
            = (D.photonEnergy ω - D.photonEnergy (D.omegaMinFormula θ))
              * ((3 - 2 * Real.cos θ ^ 2)
                  * (D.photonEnergy ω + D.photonEnergy (D.omegaMinFormula θ))
                - 6 * D.m * D.c ^ 2) := by ring
        rw [hQmin] at hfact
        linarith [hQ, hfact]
      -- For `E < E_min` the second factor is negative (as `a(E+E_min) < 2aE_min ≤ 6mc²`).
      have hA2 : (3 - 2 * Real.cos θ ^ 2)
          * (D.photonEnergy ω + D.photonEnergy (D.omegaMinFormula θ))
          - 6 * D.m * D.c ^ 2 < 0 := by
        have hsum : D.photonEnergy ω + D.photonEnergy (D.omegaMinFormula θ)
            < 2 * D.photonEnergy (D.omegaMinFormula θ) := by linarith [hcon]
        have h1 : (3 - 2 * Real.cos θ ^ 2)
            * (D.photonEnergy ω + D.photonEnergy (D.omegaMinFormula θ))
            < (3 - 2 * Real.cos θ ^ 2) * (2 * D.photonEnergy (D.omegaMinFormula θ)) :=
          mul_lt_mul_of_pos_left hsum hA
        have h2 : (3 - 2 * Real.cos θ ^ 2) * (2 * D.photonEnergy (D.omegaMinFormula θ))
            ≤ 6 * D.m * D.c ^ 2 := by
          have e : (3 - 2 * Real.cos θ ^ 2) * (2 * D.photonEnergy (D.omegaMinFormula θ))
              = 2 * ((3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ)) := by ring
          rw [e]; linarith [hAEmin]
        linarith [h1, h2]
      have hf1 : D.photonEnergy ω - D.photonEnergy (D.omegaMinFormula θ) < 0 :=
        sub_neg.mpr hcon
      have hpos : 0 < (D.photonEnergy ω - D.photonEnergy (D.omegaMinFormula θ))
          * ((3 - 2 * Real.cos θ ^ 2)
              * (D.photonEnergy ω + D.photonEnergy (D.omegaMinFormula θ))
            - 6 * D.m * D.c ^ 2) := mul_pos_of_neg_of_neg hf1 hA2
      linarith [hprod, hpos]
    -- Convert the energy bound `ℏ ω_min ≤ ℏ ω` back to a frequency bound.
    have hfin : D.ℏ * D.omegaMinFormula θ ≤ D.ℏ * ω := hEmin_le_E
    exact le_of_mul_le_mul_left hfin D.hℏ

/-- The minimum angular frequency `ω_min(θ)`: the infimum of the feasible
positive frequencies (attained, by `isLeast_feasibleFreqs`). -/
noncomputable def omegaMin (D : OzonePhotodissociation) (θ : ℝ) : ℝ :=
  sInf (D.feasibleFreqs θ)

/-- `ω_min` as an infimum agrees with the closed form. -/
theorem omegaMin_eq (D : OzonePhotodissociation) {θ : ℝ}
    (hθ : 0 < θ ∧ θ < Real.pi / 2)
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    D.omegaMin θ = D.omegaMinFormula θ :=
  (isLeast_feasibleFreqs D hθ hDisc).csInf_eq

end OzonePhotodissociation

end IPhO2026.T1C1
