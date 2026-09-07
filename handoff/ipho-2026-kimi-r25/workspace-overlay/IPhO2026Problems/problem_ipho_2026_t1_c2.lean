import Mathlib

/-!
# IPhO 2026 — Theory Problem 1, Part C2
## Photodissociation of ozone: the numerical value of `ℏω_min − ΔU` at `θ = π/6`

### Physical scenario (T1-C, Fig. 1c)

A photon of angular frequency `ω` strikes an ozone molecule O₃ **at rest** and
is absorbed, dissociating it into an oxygen molecule O₂ and an oxygen atom O.
The outgoing O₂ momentum makes an angle `θ` with the incident photon direction
(in Fig. 1c the O₂ recoils above the photon axis, the O below).  The system is
isolated; the fragments are treated classically and non-relativistically
(potential energies do not contribute to the mass bookkeeping), and the photon
obeys the stipulated relation `p = E/c`, i.e. `E_γ = ℏω`, `p_γ = ℏω/c`.

* `U_i`, `U_f` — ground-state energies of O₃ and O₂; `ΔU = U_f − U_i > 0` is
  the dissociation energy.
* `m` — mass of one oxygen atom, so the O₂ fragment has mass `2m`, the O atom
  mass `m`, and the initial O₃ molecule mass `3m`.

### Subquestion T1-C2 (source: `T1_page-3.png`, printed page 6)

"If `θ = π/6`, calculate the value of `ℏω_min − ΔU`. Give your answer in
electronvolts (eV). Take `ΔU = 1.10 eV` and `m = 16.0 amu.`"

The problem page supplies the binomial-expansion hint
`(1 + x)^r = 1 + rx + r(r−1)x²/2! + ⋯`, which legitimates the leading-order
evaluation of the threshold square root (see `excessLeadingOrderEV`).

### Previous-part dependency (T1-C1)

Policy: `derive_inline_from_problem_only_material`.  The T1-C1 model — the
conservation-law event structure, feasibility, and the characterization of
`ω_min` as the least feasible positive angular frequency — is re-derived
inline in Part A below from the problem-only material (the same governing
laws); no sibling file is imported and no previous-part conclusion is assumed
as a hypothesis.  The closed form appears only in theorem conclusions.

### Numerical constants (problem-side constants-table material)

* `speedOfLightSI = 299792458 m/s` — exact SI value;
* `electronVoltSI = 1.602176634×10⁻¹⁹ J` — exact SI value (2019 SI);
* `atomicMassUnitSI = 1.66053906660×10⁻²⁷ kg` — CODATA constants-table value;
* `hbarSI = 1.054571817×10⁻³⁴ J·s` — CODATA constants-table value (agrees with
  Physlib's `Constants.ℏ`).

`ℏ` cancels from the requested excess energy (`photonEnergy_omegaMinFormula`),
so the numerical value depends only on `c`, the atomic mass unit, and the eV;
at three significant figures it is moreover insensitive to the last digits of
the constants-table values.

### Answer-blind derivation of the candidate (recorded, not assumed)

Momentum and energy conservation for an emission angle `θ` confine the photon
energy `E = ℏω` to the band `(3 − 2cos²θ)E² − 6mc²E + 6mc²ΔU ≤ 0`, so the
minimum photon energy is the smaller root
`ℏω_min = (3mc² − √(9m²c⁴ − 6mc²ΔU(3 − 2cos²θ)))/(3 − 2cos²θ)`.
At `θ = π/6` (`cos²θ = 3/4`, `Real.sq_cos_pi_div_six`) this is
`ℏω_min = 2mc²(1 − √(1 − ΔU/(mc²)))`, hence
`ℏω_min − ΔU = ΔU²/(4mc²) + O(ΔU³/(mc²)²) ≈ 2.0297×10⁻¹¹ eV`
with `mc² = 16.0 u·c² ≈ 1.4904×10¹⁰ eV`.  The source-derived rounding rule
(three significant figures, matching the data `1.10 eV` and `16.0 amu`; the
raw value is of order `10⁻¹¹ eV`, so the rounding grid is `10⁻¹³ eV`) reports
`2.03×10⁻¹¹ eV` — the statement `reportedExcessEV_value`, proved from
`reportedExcessEV_mantissa`.

### Declarations

* Part A (inline T1-C1 re-derivation): `OzonePhotodissociation`,
  `DissociationEvent` (governing-law fields), `FeasibleAt`, `feasibleFreqs`,
  `omegaMinFormula`, `omegaMin`, and the bridge lemmas
  `feasibleAt_iff_exists_p`, `feasibleAt_iff_quadratic`,
  `photonEnergy_omegaMinFormula_gt`, `feasibleAt_omegaMinFormula`,
  `isLeast_feasibleFreqs`, `omegaMin_eq`.
* Part B (T1-C2 data): the four constants, `givenAngle = π/6`,
  `givenDeltaUEV = 1.10`, `givenMassAMU = 16.0`, the instantiated bundle
  `t1c2Instance` with its discharged side conditions (`givenAngle_acute`,
  `t1c2Instance_kinematic_condition`), and `restEnergyAtomEV` (`mc²` in eV).
* Part C (target): the raw end-to-end quantity `rawExcessEV` (the physically
  characterized `ℏω_min − ΔU` in eV), the closed-form bridges
  `rawExcessEV_eq_formula` and `rawExcessEV_eq_sqrtForm`, the binomial-hint
  leading order `excessLeadingOrderEV` with `excessLeadingOrderEV_close`, the
  certified bounds `rawExcessEV_bounds`, the rounding rule
  `reportedExcessEV`, and the main result `reportedExcessEV_value`
  (blueprint `thm:physics:ipho_2026_t1_c2:target`).

All quantities are real scalars in SI units (joules, kilograms, m/s, J·s)
until the final conversion to electronvolts; momenta are Cartesian components
in the scattering plane of Fig. 1c.
-/

namespace IPhO2026.T1C2

/-! ## Part A — the photodissociation model (T1-C1 re-derived inline) -/

/-- Parameter bundle for the ozone photodissociation problem (IPhO 2026 T1-C).

* `ℏ` — reduced Planck constant (J·s),
* `c` — speed of light (m/s),
* `m` — mass of a single oxygen atom (kg),
* `Ui`, `Uf` — ground-state energies of O₃ and O₂ (J).

The sign hypotheses encode the physical setting: the constants are positive,
and dissociation costs energy (`Ui < Uf`).  All scalars are reals in SI
units. -/
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
  have hΔ : D.ΔU = D.Uf - D.Ui := rfl
  constructor
  · rintro ⟨ev⟩
    refine ⟨ev.p, ev.hp, ?_⟩
    have hqx : ev.qx = D.photonMomentum ω - ev.p * Real.cos θ := by linarith [ev.momX]
    have hqy : ev.qy = -(ev.p * Real.sin θ) := by linarith [ev.momY]
    have hE := ev.energy
    rw [hqx, hqy, neg_sq] at hE
    rw [hΔ]
    linarith [hE]
  · rintro ⟨p, hp, hE⟩
    refine ⟨⟨p, D.photonMomentum ω - p * Real.cos θ, -(p * Real.sin θ), hp,
      by ring, by ring, ?_⟩⟩
    rw [neg_sq]
    rw [hΔ] at hE
    linarith [hE]

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
  have hmO2 : D.mO2 = 2 * D.m := rfl
  have hmO : D.mO = D.m := rfl
  have hE : (0:ℝ) < D.photonEnergy ω := mul_pos D.hℏ hω
  have hP : (0:ℝ) < D.photonMomentum ω := div_pos hE D.hc
  -- Step 1: for each `p`, the energy balance is the momentum quadratic in `p`.
  have key : ∀ p : ℝ,
      (D.photonEnergy ω = D.ΔU + p ^ 2 / (2 * D.mO2) +
          ((D.photonMomentum ω - p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2) / (2 * D.mO))
      ↔ 3 * p ^ 2 - 4 * D.photonMomentum ω * Real.cos θ * p +
          (2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU - 4 * D.m * D.photonEnergy ω) = 0 := by
    intro p
    have hsum : (D.photonMomentum ω - p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
        D.photonMomentum ω ^ 2 - 2 * D.photonMomentum ω * p * Real.cos θ + p ^ 2 := by
      have hr : (D.photonMomentum ω - p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
          D.photonMomentum ω ^ 2 - 2 * D.photonMomentum ω * p * Real.cos θ +
            p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      rw [Real.cos_sq_add_sin_sq θ, mul_one] at hr
      exact hr
    rw [hmO2, hmO, hsum]
    constructor
    · intro h
      have h' : 4 * D.m * D.photonEnergy ω = 4 * D.m * (D.ΔU + p ^ 2 / (2 * (2 * D.m)) +
          (D.photonMomentum ω ^ 2 - 2 * D.photonMomentum ω * p * Real.cos θ + p ^ 2) /
            (2 * D.m)) := by
        rw [h]
      have h'' : 4 * D.m * D.photonEnergy ω = 4 * D.m * D.ΔU + 3 * p ^ 2 +
          2 * (D.photonMomentum ω ^ 2 - 2 * D.photonMomentum ω * p * Real.cos θ) := by
        rw [h']; field_simp [D.hm.ne']; ring
      linear_combination -h''
    · intro h
      have h'' : 4 * D.m * D.photonEnergy ω = 4 * D.m * D.ΔU + 3 * p ^ 2 +
          2 * (D.photonMomentum ω ^ 2 - 2 * D.photonMomentum ω * p * Real.cos θ) := by
        linear_combination -h
      have h4m : (4:ℝ) * D.m ≠ 0 := mul_ne_zero (by norm_num) D.hm.ne'
      rw [show D.photonEnergy ω = (4 * D.m * D.photonEnergy ω) / (4 * D.m) from
        (mul_div_cancel_left₀ _ h4m).symm, h'']
      field_simp [D.hm.ne']
      ring
  -- Step 2: a positive root exists iff the minimum value of the quadratic is `≤ 0`.
  have step2 : (∃ p : ℝ, 0 < p ∧ 3 * p ^ 2 - 4 * D.photonMomentum ω * Real.cos θ * p +
        (2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU - 4 * D.m * D.photonEnergy ω) = 0) ↔
      2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU - 4 * D.m * D.photonEnergy ω -
        (4:ℝ) / 3 * D.photonMomentum ω ^ 2 * Real.cos θ ^ 2 ≤ 0 := by
    have hid : ∀ p : ℝ, 3 * p ^ 2 - 4 * D.photonMomentum ω * Real.cos θ * p +
        (2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU - 4 * D.m * D.photonEnergy ω) =
        3 * (p - 2 * D.photonMomentum ω * Real.cos θ / 3) ^ 2 +
          (2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU - 4 * D.m * D.photonEnergy ω -
            (4:ℝ) / 3 * D.photonMomentum ω ^ 2 * Real.cos θ ^ 2) := fun p => by ring
    constructor
    · rintro ⟨p, _, hf⟩
      rw [hid p] at hf
      have := sq_nonneg (p - 2 * D.photonMomentum ω * Real.cos θ / 3)
      linarith
    · intro hD
      have hv : (0:ℝ) < 2 * D.photonMomentum ω * Real.cos θ / 3 :=
        div_pos (mul_pos (mul_pos (by norm_num) hP) hθ) (by norm_num)
      generalize hT : -(2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU -
          4 * D.m * D.photonEnergy ω -
            (4:ℝ) / 3 * D.photonMomentum ω ^ 2 * Real.cos θ ^ 2) / 3 = T
      have hTnn : 0 ≤ T := by
        rw [← hT]; apply div_nonneg _ (by norm_num); linarith
      refine ⟨2 * D.photonMomentum ω * Real.cos θ / 3 + Real.sqrt T,
        by linarith [hv, Real.sqrt_nonneg T], ?_⟩
      rw [hid]
      rw [show 2 * D.photonMomentum ω * Real.cos θ / 3 + Real.sqrt T -
          2 * D.photonMomentum ω * Real.cos θ / 3 = Real.sqrt T by ring,
        Real.sq_sqrt hTnn]
      linarith
  -- Step 3: the discriminant condition is the stated quadratic form in `E`.
  have hPc : D.c * D.photonMomentum ω = D.photonEnergy ω := mul_div_cancel₀ _ D.hc.ne'
  have hPc2 : D.c ^ 2 * D.photonMomentum ω ^ 2 = D.photonEnergy ω ^ 2 := by
    rw [← hPc]; ring
  have hlink : 3 * D.c ^ 2 * (2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU -
        4 * D.m * D.photonEnergy ω - (4:ℝ) / 3 * D.photonMomentum ω ^ 2 * Real.cos θ ^ 2) =
      2 * ((3 - 2 * Real.cos θ ^ 2) * D.photonEnergy ω ^ 2 -
        6 * D.m * D.c ^ 2 * D.photonEnergy ω + 6 * D.m * D.c ^ 2 * D.ΔU) := by
    linear_combination (6 - 4 * Real.cos θ ^ 2) * hPc2
  have hc2 : (0:ℝ) < 3 * D.c ^ 2 := mul_pos (by norm_num) (pow_pos D.hc 2)
  rw [feasibleAt_iff_exists_p]
  constructor
  · rintro ⟨p, hp, hE'⟩
    have hq := (key p).mp hE'
    have hD := step2.mp ⟨p, hp, hq⟩
    nlinarith [hlink, hD, hc2]
  · intro hQ
    have hD : 2 * D.photonMomentum ω ^ 2 + 4 * D.m * D.ΔU - 4 * D.m * D.photonEnergy ω -
        (4:ℝ) / 3 * D.photonMomentum ω ^ 2 * Real.cos θ ^ 2 ≤ 0 := by
      nlinarith [hlink, hQ, hc2]
    obtain ⟨p, hp, hq⟩ := step2.mpr hD
    exact ⟨p, hp, (key p).mpr hq⟩

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

/-- The photon energy at the candidate minimum is independent of `ℏ`:
`ℏω_min = 6mc²ΔU / (3mc² + √(9m²c⁴ − 6mc²ΔU(3 − 2cos²θ)))`.  This is why the
T1-C2 numerical value requires no value of `ℏ` beyond its positivity. -/
theorem photonEnergy_omegaMinFormula (D : OzonePhotodissociation) (θ : ℝ) :
    D.photonEnergy (D.omegaMinFormula θ) =
      6 * D.m * D.c ^ 2 * D.ΔU /
        (3 * D.m * D.c ^ 2 +
          Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) := by
  unfold photonEnergy omegaMinFormula
  rw [← mul_div_assoc]
  exact mul_div_mul_left _ _ D.hℏ.ne'

/-- Recoil makes the threshold strictly exceed the naive value `ΔU/ℏ`:
`ℏω_min > ΔU`.  The excess `ℏω_min − ΔU` certified positive here is exactly
the quantity that T1-C2 evaluates numerically. -/
theorem photonEnergy_omegaMinFormula_gt (D : OzonePhotodissociation) (θ : ℝ) :
    D.ΔU < D.photonEnergy (D.omegaMinFormula θ) := by
  rw [photonEnergy_omegaMinFormula]
  set A : ℝ := 3 * D.m * D.c ^ 2 with hA
  set B : ℝ := Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
    6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) with hB
  have hApos : 0 < A := mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)
  have hcosle : Real.cos θ ^ 2 ≤ 1 := by
    have h := Real.cos_sq_add_sin_sq θ
    have h2 := sq_nonneg (Real.sin θ)
    linarith
  have hBlt : B < A := by
    rw [hB, Real.sqrt_lt' hApos, hA]
    have hpos : (0:ℝ) < 6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) :=
      mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)) D.ΔU_pos)
        (by linarith)
    nlinarith [hpos]
  have hBnn : 0 ≤ B := by rw [hB]; exact Real.sqrt_nonneg _
  have hAB : (0:ℝ) < A + B := add_pos_of_pos_of_nonneg hApos hBnn
  rw [lt_div_iff₀ hAB]
  have h1 : D.ΔU * (A + B) < D.ΔU * (A + A) :=
    mul_lt_mul_of_pos_left (by linarith [hBlt]) D.ΔU_pos
  have h2 : D.ΔU * (A + A) = 6 * D.m * D.c ^ 2 * D.ΔU := by rw [hA]; ring
  linarith [h1, h2]

/-- The minimum is attained: at `ω = ω_min` there is a dissociation event — the
momentum quadratic has the positive double root
`p* = (2/3)(ℏω_min/c)·cos θ > 0`. -/
theorem feasibleAt_omegaMinFormula (D : OzonePhotodissociation) {θ : ℝ}
    (hθ : 0 < θ ∧ θ < Real.pi / 2)
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    D.FeasibleAt θ (D.omegaMinFormula θ) := by
  have hcθ : (0:ℝ) < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hωpos := D.omegaMinFormula_pos θ
  have hk : (0:ℝ) < 3 - 2 * Real.cos θ ^ 2 := by
    have h := Real.cos_sq_add_sin_sq θ
    have h2 := sq_nonneg (Real.sin θ)
    linarith
  have hApos : (0:ℝ) < 3 * D.m * D.c ^ 2 :=
    mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)
  have hDnn : 0 ≤ 9 * D.m ^ 2 * D.c ^ 4 -
      6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := by
    nlinarith [hDisc, hApos]
  have hBnn : 0 ≤ Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
      6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) := Real.sqrt_nonneg _
  have hB2 : Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) ^ 2
      = 9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) :=
    Real.sq_sqrt hDnn
  have hABpos : (0:ℝ) < 3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
      6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) :=
    add_pos_of_pos_of_nonneg hApos hBnn
  have hEB : D.photonEnergy (D.omegaMinFormula θ) * (3 * D.m * D.c ^ 2 +
        Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
          6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) =
      6 * D.m * D.c ^ 2 * D.ΔU := by
    rw [photonEnergy_omegaMinFormula]
    exact div_mul_cancel₀ _ hABpos.ne'
  have hkE : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) =
      3 * D.m * D.c ^ 2 - Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) := by
    have h1 : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) *
          (3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)))
        = (3 * D.m * D.c ^ 2 - Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) *
          (3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) := by
      linear_combination (3 - 2 * Real.cos θ ^ 2) * hEB + hB2
    exact mul_right_cancel₀ hABpos.ne' h1
  have hQ0 : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) ^ 2 -
        6 * D.m * D.c ^ 2 * D.photonEnergy (D.omegaMinFormula θ) +
        6 * D.m * D.c ^ 2 * D.ΔU = 0 := by
    linear_combination D.photonEnergy (D.omegaMinFormula θ) * hkE - hEB
  rw [D.feasibleAt_iff_quadratic hcθ hωpos]
  exact le_of_eq hQ0

/-- **T1-C1 main result, re-derived inline.**  For an acute emission angle `θ`
(the branch of Fig. 1c) and dissociation energy below the kinematic threshold
`2ΔU(3 − 2cos²θ) ≤ 3mc²` — overwhelmingly satisfied in the actual problem,
where `ΔU ∼ 1 eV ≪ mc²` — the least angular frequency at which the
dissociation can occur with the O₂ emitted at angle `θ` is

`ω_min = 6 m c² ΔU / (ℏ (3 m c² + √(9 m²c⁴ − 6 m c² ΔU (3 − 2cos²θ))))`. -/
theorem isLeast_feasibleFreqs (D : OzonePhotodissociation) {θ : ℝ}
    (hθ : 0 < θ ∧ θ < Real.pi / 2)
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    IsLeast (D.feasibleFreqs θ) (D.omegaMinFormula θ) := by
  have hcθ : (0:ℝ) < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hk : (0:ℝ) < 3 - 2 * Real.cos θ ^ 2 := by
    have h := Real.cos_sq_add_sin_sq θ
    have h2 := sq_nonneg (Real.sin θ)
    linarith
  have hApos : (0:ℝ) < 3 * D.m * D.c ^ 2 :=
    mul_pos (mul_pos (by norm_num) D.hm) (pow_pos D.hc 2)
  have hDnn : 0 ≤ 9 * D.m ^ 2 * D.c ^ 4 -
      6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) := by
    nlinarith [hDisc, hApos]
  have hBnn : 0 ≤ Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
      6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) := Real.sqrt_nonneg _
  have hB2 : Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) ^ 2
      = 9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) :=
    Real.sq_sqrt hDnn
  have hABpos : (0:ℝ) < 3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
      6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) :=
    add_pos_of_pos_of_nonneg hApos hBnn
  have hEB : D.photonEnergy (D.omegaMinFormula θ) * (3 * D.m * D.c ^ 2 +
        Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
          6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) =
      6 * D.m * D.c ^ 2 * D.ΔU := by
    rw [photonEnergy_omegaMinFormula]
    exact div_mul_cancel₀ _ hABpos.ne'
  have hkE : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) =
      3 * D.m * D.c ^ 2 - Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
        6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)) := by
    have h1 : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) *
          (3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2)))
        = (3 * D.m * D.c ^ 2 - Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) *
          (3 * D.m * D.c ^ 2 + Real.sqrt (9 * D.m ^ 2 * D.c ^ 4 -
            6 * D.m * D.c ^ 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2))) := by
      linear_combination (3 - 2 * Real.cos θ ^ 2) * hEB + hB2
    exact mul_right_cancel₀ hABpos.ne' h1
  have hQ0 : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy (D.omegaMinFormula θ) ^ 2 -
        6 * D.m * D.c ^ 2 * D.photonEnergy (D.omegaMinFormula θ) +
        6 * D.m * D.c ^ 2 * D.ΔU = 0 := by
    linear_combination D.photonEnergy (D.omegaMinFormula θ) * hkE - hEB
  refine ⟨⟨D.omegaMinFormula_pos θ, D.feasibleAt_omegaMinFormula hθ hDisc⟩, ?_⟩
  intro ω hω
  obtain ⟨hωpos, hωfeas⟩ := hω
  have hQ := (D.feasibleAt_iff_quadratic hcθ hωpos).mp hωfeas
  by_contra hlt
  push Not at hlt
  have hElt : D.photonEnergy ω < D.photonEnergy (D.omegaMinFormula θ) :=
    mul_lt_mul_of_pos_left hlt D.hℏ
  have hid : (3 - 2 * Real.cos θ ^ 2) * D.photonEnergy ω ^ 2 -
        6 * D.m * D.c ^ 2 * D.photonEnergy ω + 6 * D.m * D.c ^ 2 * D.ΔU
      = (D.photonEnergy ω - D.photonEnergy (D.omegaMinFormula θ)) *
          ((3 - 2 * Real.cos θ ^ 2) * (D.photonEnergy ω +
            D.photonEnergy (D.omegaMinFormula θ)) - 2 * (3 * D.m * D.c ^ 2)) := by
    linear_combination hQ0
  have hf1 : D.photonEnergy ω - D.photonEnergy (D.omegaMinFormula θ) < 0 :=
    sub_neg.mpr hElt
  have hf2 : (3 - 2 * Real.cos θ ^ 2) * (D.photonEnergy ω +
        D.photonEnergy (D.omegaMinFormula θ)) - 2 * (3 * D.m * D.c ^ 2) < 0 := by
    nlinarith [hElt, hk, hkE, hBnn]
  have hprod := mul_pos_of_neg_of_neg hf1 hf2
  linarith [hQ, hid, hprod]

/-- The minimum angular frequency `ω_min(θ)`: the infimum of the feasible
positive frequencies (attained, by `isLeast_feasibleFreqs`). -/
noncomputable def omegaMin (D : OzonePhotodissociation) (θ : ℝ) : ℝ :=
  sInf (D.feasibleFreqs θ)

/-- `ω_min` as an infimum agrees with the closed form
(`IsLeast.csInf_eq`). -/
theorem omegaMin_eq (D : OzonePhotodissociation) {θ : ℝ}
    (hθ : 0 < θ ∧ θ < Real.pi / 2)
    (hDisc : 2 * D.ΔU * (3 - 2 * Real.cos θ ^ 2) ≤ 3 * D.m * D.c ^ 2) :
    D.omegaMin θ = D.omegaMinFormula θ :=
  (D.isLeast_feasibleFreqs hθ hDisc).csInf_eq

end OzonePhotodissociation

/-! ## Part B — T1-C2 numerical data and the instantiated problem -/

/-- Speed of light in vacuum, exact SI value `c = 299792458 m/s`
(constants-table material). -/
noncomputable def speedOfLightSI : ℝ := 299792458

/-- Atomic mass unit in kilograms, the CODATA constants-table value
`1 u = 1.66053906660×10⁻²⁷ kg`. -/
noncomputable def atomicMassUnitSI : ℝ := 1.66053906660e-27

/-- The electronvolt in joules, the exact SI value
`1 eV = 1.602176634×10⁻¹⁹ J` (2019 SI; constants-table material).  Used to
convert the final excess energy to electronvolts, as the problem requests. -/
noncomputable def electronVoltSI : ℝ := 1.602176634e-19

/-- Reduced Planck constant, the CODATA constants-table value
`ℏ = 1.054571817×10⁻³⁴ J·s` (agrees with Physlib's `Constants.ℏ`).  It enters
the model bundle but cancels from the final excess energy
(`OzonePhotodissociation.photonEnergy_omegaMinFormula`). -/
noncomputable def hbarSI : ℝ := 1.054571817e-34

/-- The given emission angle of T1-C2: `θ = π/6` (the acute branch of
Fig. 1c). -/
noncomputable def givenAngle : ℝ := Real.pi / 6

/-- The given dissociation energy of T1-C2: `ΔU = 1.10 eV`. -/
noncomputable def givenDeltaUEV : ℝ := 1.10

/-- The given oxygen-atom mass of T1-C2: `m = 16.0 amu`. -/
noncomputable def givenMassAMU : ℝ := 16.0

/-- The instantiated T1-C2 problem: `ℏ`, `c`, the eV and the amu at their
constants-table SI values, `m = 16.0 u`, and the energy levels in the gauge
`U_i = 0`, `U_f = 1.10 eV` — only the difference `ΔU = U_f − U_i` enters the
conservation laws, so the choice of energy zero is without loss. -/
noncomputable def t1c2Instance : OzonePhotodissociation where
  ℏ := hbarSI
  c := speedOfLightSI
  m := givenMassAMU * atomicMassUnitSI
  Ui := 0
  Uf := givenDeltaUEV * electronVoltSI
  hℏ := by unfold hbarSI; norm_num
  hc := by unfold speedOfLightSI; norm_num
  hm := by unfold givenMassAMU atomicMassUnitSI; norm_num
  hU := by unfold givenDeltaUEV electronVoltSI; norm_num

/-- The instance dissociation energy is `ΔU = 1.10 eV` (in joules). -/
theorem t1c2Instance_ΔU :
    t1c2Instance.ΔU = givenDeltaUEV * electronVoltSI := by
  simp [OzonePhotodissociation.ΔU, t1c2Instance]

/-- Instance projection: the speed of light. -/
theorem t1c2Instance_c : t1c2Instance.c = speedOfLightSI := rfl

/-- Instance projection: the oxygen-atom mass `m = 16.0 u` (in kg). -/
theorem t1c2Instance_m :
    t1c2Instance.m = givenMassAMU * atomicMassUnitSI := rfl

/-- Instance projection: the reduced Planck constant. -/
theorem t1c2Instance_hbar : t1c2Instance.ℏ = hbarSI := rfl

/-- Instance projection: the ozone ground-state energy gauge `U_i = 0`. -/
theorem t1c2Instance_Ui : t1c2Instance.Ui = 0 := rfl

/-- Instance projection: the oxygen ground-state energy `U_f = 1.10 eV`
(in joules). -/
theorem t1c2Instance_Uf :
    t1c2Instance.Uf = givenDeltaUEV * electronVoltSI := rfl

/-- Figure/data readout at `θ = π/6`: `cos²(π/6) = 3/4`, so the kinematic
coefficient is `3 − 2cos²θ = 3/2`. -/
theorem cos_givenAngle_sq : Real.cos givenAngle ^ 2 = 3 / 4 :=
  Real.sq_cos_pi_div_six

/-- The given angle lies on the acute branch of Fig. 1c:
`0 < π/6 < π/2`. -/
theorem givenAngle_acute : 0 < givenAngle ∧ givenAngle < Real.pi / 2 := by
  unfold givenAngle
  constructor
  · positivity
  · exact div_lt_div_of_pos_left Real.pi_pos zero_lt_two (by norm_num)

/-- The instance satisfies the kinematic threshold condition of
`isLeast_feasibleFreqs`: `2ΔU(3 − 2cos²θ) = 3.30 eV` is dwarfed by
`3mc² ≈ 4.47×10¹⁰ eV`. -/
theorem t1c2Instance_kinematic_condition :
    2 * t1c2Instance.ΔU * (3 - 2 * Real.cos givenAngle ^ 2) ≤
      3 * t1c2Instance.m * t1c2Instance.c ^ 2 := by
  rw [cos_givenAngle_sq, t1c2Instance_ΔU, t1c2Instance_m, t1c2Instance_c]
  unfold givenDeltaUEV electronVoltSI givenMassAMU atomicMassUnitSI
    speedOfLightSI
  norm_num

/-- Rest energy of one oxygen atom of mass `m = 16.0 u`, in electronvolts:
`mc² = 16.0·u·c²/eV ≈ 1.4904×10¹⁰ eV`.  This is the energy scale controlling
the recoil excess. -/
noncomputable def restEnergyAtomEV : ℝ :=
  givenMassAMU * atomicMassUnitSI * speedOfLightSI ^ 2 / electronVoltSI

/-! ## Part C — the requested quantity, its value, and the rounding rule -/

/-- The minimum photon energy `ℏω_min` for dissociation at the T1-C2 angle
`θ = π/6`, in joules: the photon energy at the least feasible positive angular
frequency. -/
noncomputable def minPhotonEnergySI : ℝ :=
  t1c2Instance.photonEnergy (t1c2Instance.omegaMin givenAngle)

/-- **Raw end-to-end quantity of T1-C2**: the recoil excess `ℏω_min − ΔU`
expressed in electronvolts, as the problem requests ("calculate the value of
`ℏω_min − ΔU` … in electronvolts").  Its value is not pinned by this
definition; it is determined by the conservation laws through
`OzonePhotodissociation.omegaMin`. -/
noncomputable def rawExcessEV : ℝ :=
  (minPhotonEnergySI - t1c2Instance.ΔU) / electronVoltSI

/-- Bridge from the physical minimum to the closed form: the raw excess equals
the T1-C1 threshold formula evaluated on the T1-C2 instance.  Carrier chain:
`omegaMin_eq` (with `givenAngle_acute`, `t1c2Instance_kinematic_condition`) and
`photonEnergy_omegaMinFormula` (the `ℏ` cancellation). -/
theorem rawExcessEV_eq_formula :
    rawExcessEV =
      (6 * t1c2Instance.m * t1c2Instance.c ^ 2 * t1c2Instance.ΔU /
          (3 * t1c2Instance.m * t1c2Instance.c ^ 2 +
            Real.sqrt (9 * t1c2Instance.m ^ 2 * t1c2Instance.c ^ 4 -
              6 * t1c2Instance.m * t1c2Instance.c ^ 2 * t1c2Instance.ΔU *
                (3 - 2 * Real.cos givenAngle ^ 2))) -
        t1c2Instance.ΔU) / electronVoltSI := by
  unfold rawExcessEV minPhotonEnergySI
  rw [t1c2Instance.omegaMin_eq givenAngle_acute t1c2Instance_kinematic_condition,
    t1c2Instance.photonEnergy_omegaMinFormula]

/-- The closed form at `θ = π/6`, in cancellation-free ratio form: with
`cos²(π/6) = 3/4` and `x = ΔU/(mc²)`,
`ℏω_min − ΔU = ΔU·(1 − √(1 − x))/(1 + √(1 − x))` in eV
(equivalently `2mc²(1 − √(1 − x)) − ΔU`, the smaller-root form). -/
theorem rawExcessEV_eq_sqrtForm :
    rawExcessEV =
      givenDeltaUEV * (1 - Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) /
        (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) := by
  rw [rawExcessEV_eq_formula, cos_givenAngle_sq]
  have heV : (0:ℝ) < electronVoltSI := by unfold electronVoltSI; norm_num
  have hmc2pos : (0:ℝ) < t1c2Instance.m * t1c2Instance.c ^ 2 :=
    mul_pos t1c2Instance.hm (pow_pos t1c2Instance.hc 2)
  have hmc2 : t1c2Instance.m * t1c2Instance.c ^ 2 = restEnergyAtomEV * electronVoltSI := by
    rw [t1c2Instance_m, t1c2Instance_c]
    unfold restEnergyAtomEV
    rw [div_mul_cancel₀ _ heV.ne']
  have hR : restEnergyAtomEV = t1c2Instance.m * t1c2Instance.c ^ 2 / electronVoltSI := rfl
  have hRpos : (0:ℝ) < restEnergyAtomEV := by
    rw [hR]; exact div_pos hmc2pos heV
  have hΔU'pos : (0:ℝ) < givenDeltaUEV := by unfold givenDeltaUEV; norm_num
  have hxpos : (0:ℝ) < givenDeltaUEV / restEnergyAtomEV := div_pos hΔU'pos hRpos
  have hx1 : givenDeltaUEV / restEnergyAtomEV < 1 := by
    rw [div_lt_one hRpos]
    have hRge : (1e10 : ℝ) ≤ restEnergyAtomEV := by
      unfold restEnergyAtomEV givenMassAMU atomicMassUnitSI speedOfLightSI electronVoltSI
      rw [le_div_iff₀ (by norm_num)]
      norm_num
    have h3 : givenDeltaUEV < (1e10 : ℝ) := by unfold givenDeltaUEV; norm_num
    linarith
  have hspos : (0:ℝ) < Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) :=
    Real.sqrt_pos.mpr (by linarith)
  have h1spos : (0:ℝ) < 1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by linarith
  -- the threshold square root at `θ = π/6` factors as `3mc²·√(1 − ΔU/(mc²))`
  have hinside : 9 * t1c2Instance.m ^ 2 * t1c2Instance.c ^ 4 -
        6 * t1c2Instance.m * t1c2Instance.c ^ 2 * t1c2Instance.ΔU * (3 - 2 * (3 / 4 : ℝ))
      = (3 * (t1c2Instance.m * t1c2Instance.c ^ 2)) ^ 2 *
          (1 - givenDeltaUEV / restEnergyAtomEV) := by
    have h1 : 9 * t1c2Instance.m ^ 2 * t1c2Instance.c ^ 4 =
        9 * (t1c2Instance.m * t1c2Instance.c ^ 2) ^ 2 := by ring
    have h2 : 6 * t1c2Instance.m * t1c2Instance.c ^ 2 * t1c2Instance.ΔU * (3 - 2 * (3 / 4 : ℝ))
        = 9 * (t1c2Instance.m * t1c2Instance.c ^ 2) * t1c2Instance.ΔU := by ring
    rw [h1, h2, hmc2, t1c2Instance_ΔU]
    field_simp [hRpos.ne']
    ring
  have hsqrt : Real.sqrt (9 * t1c2Instance.m ^ 2 * t1c2Instance.c ^ 4 -
        6 * t1c2Instance.m * t1c2Instance.c ^ 2 * t1c2Instance.ΔU * (3 - 2 * (3 / 4 : ℝ)))
      = 3 * (t1c2Instance.m * t1c2Instance.c ^ 2) *
          Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by
    rw [hinside, Real.sqrt_mul (sq_nonneg _) _,
      Real.sqrt_sq (mul_nonneg (by norm_num) hmc2pos.le)]
  rw [hsqrt]
  have g1 : 6 * t1c2Instance.m * t1c2Instance.c ^ 2 * t1c2Instance.ΔU
      = 6 * (t1c2Instance.m * t1c2Instance.c ^ 2) * t1c2Instance.ΔU := by ring
  have g2 : 3 * t1c2Instance.m * t1c2Instance.c ^ 2 +
        3 * (t1c2Instance.m * t1c2Instance.c ^ 2) *
          Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)
      = 3 * (t1c2Instance.m * t1c2Instance.c ^ 2) *
          (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) := by ring
  rw [g1, g2, hmc2, t1c2Instance_ΔU]
  field_simp [hRpos.ne', heV.ne', h1spos.ne']
  ring

/-- The leading-order value supplied by the problem's binomial hint
(`(1 + x)^r ≈ 1 + rx` applied to `√(1 − ΔU/(mc²))`):
`ℏω_min − ΔU ≈ ΔU²/(4mc²)` in eV. -/
noncomputable def excessLeadingOrderEV : ℝ :=
  givenDeltaUEV ^ 2 / (4 * restEnergyAtomEV)

/-- The binomial-hint leading order matches the exact raw quantity to within
`10⁻²⁰ eV` (the next term is `ΔU³/(8(mc²)²) ≈ 7.5×10⁻²² eV`): the hint's
approximation is legitimate at the requested precision. -/
theorem excessLeadingOrderEV_close :
    |rawExcessEV - excessLeadingOrderEV| < 1e-20 := by
  rw [rawExcessEV_eq_sqrtForm]
  unfold excessLeadingOrderEV
  have hRpos : (0:ℝ) < restEnergyAtomEV := by
    have hmc2pos : (0:ℝ) < t1c2Instance.m * t1c2Instance.c ^ 2 :=
      mul_pos t1c2Instance.hm (pow_pos t1c2Instance.hc 2)
    have heV : (0:ℝ) < electronVoltSI := by unfold electronVoltSI; norm_num
    rw [show restEnergyAtomEV = t1c2Instance.m * t1c2Instance.c ^ 2 / electronVoltSI from rfl]
    exact div_pos hmc2pos heV
  have hRge : (1e10 : ℝ) ≤ restEnergyAtomEV := by
    unfold restEnergyAtomEV givenMassAMU atomicMassUnitSI speedOfLightSI electronVoltSI
    rw [le_div_iff₀ (by norm_num)]
    norm_num
  have hΔU'pos : (0:ℝ) < givenDeltaUEV := by unfold givenDeltaUEV; norm_num
  have hΔU'2 : givenDeltaUEV ^ 2 = 1.21 := by unfold givenDeltaUEV; norm_num
  have hxpos : (0:ℝ) < givenDeltaUEV / restEnergyAtomEV := div_pos hΔU'pos hRpos
  have hx1 : givenDeltaUEV / restEnergyAtomEV < 1 := by
    rw [div_lt_one hRpos]
    have h3 : givenDeltaUEV < (1e10 : ℝ) := by unfold givenDeltaUEV; norm_num
    linarith
  have hx : givenDeltaUEV / restEnergyAtomEV ≤ 1.1e-10 := by
    rw [div_le_iff₀ hRpos]
    have h1 : givenDeltaUEV = 1.1e-10 * (1e10 : ℝ) := by unfold givenDeltaUEV; norm_num
    rw [h1]
    exact mul_le_mul_of_nonneg_left hRge (by norm_num)
  have hspos : (0:ℝ) < Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) :=
    Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) ^ 2 =
      1 - givenDeltaUEV / restEnergyAtomEV := Real.sq_sqrt (by linarith)
  have hsle1 : Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - givenDeltaUEV / restEnergyAtomEV ≤ 1 by linarith)
    rwa [Real.sqrt_one] at h
  have hsge : 1 - givenDeltaUEV / restEnergyAtomEV ≤
      Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by
    rw [Real.le_sqrt (by linarith) (by linarith)]
    nlinarith [hxpos]
  have h1spos : (0:ℝ) < 1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by linarith
  have hkey : givenDeltaUEV * (1 - Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) /
        (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV))
      = givenDeltaUEV * (givenDeltaUEV / restEnergyAtomEV) /
          (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
    have h1 : (1 - Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) *
          (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV))
        = givenDeltaUEV / restEnergyAtomEV := by
      linear_combination -hs2
    rw [div_eq_div_iff h1spos.ne' (pow_pos h1spos 2).ne']
    linear_combination
      givenDeltaUEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) * h1
  have hdiff : givenDeltaUEV * (givenDeltaUEV / restEnergyAtomEV) /
        (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 -
        givenDeltaUEV ^ 2 / (4 * restEnergyAtomEV)
      = givenDeltaUEV ^ 2 *
          (4 - (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2) /
          (4 * restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2) := by
    field_simp [hRpos.ne', h1spos.ne']
  have hbrnn : 0 ≤ 4 - (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
    nlinarith [hsle1, Real.sqrt_nonneg (1 - givenDeltaUEV / restEnergyAtomEV)]
  have hbrub : 4 - (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 ≤
      3 * (givenDeltaUEV / restEnergyAtomEV) := by
    linarith [hs2, hsge]
  have hB3 : 4 - (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 ≤ 3 * 1.1e-10 := by
    linarith [hbrub, hx]
  have hden : (0:ℝ) < 4 * restEnergyAtomEV *
      (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 :=
    mul_pos (mul_pos (by norm_num) hRpos) (pow_pos h1spos 2)
  have hdiffnn : 0 ≤ givenDeltaUEV ^ 2 *
        (4 - (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2) /
        (4 * restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2) := by
    apply div_nonneg (mul_nonneg (sq_nonneg _) hbrnn)
    exact mul_nonneg (mul_nonneg (by norm_num) hRpos.le)
      (pow_nonneg (by linarith [Real.sqrt_nonneg (1 - givenDeltaUEV / restEnergyAtomEV)]) 2)
  rw [hkey, hdiff, abs_of_nonneg hdiffnn]
  -- cross-multiplying by the positive denominator: it suffices to bound the numerator
  have h1sge1 : (1:ℝ) ≤ (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
    have h1 := Real.sqrt_nonneg (1 - givenDeltaUEV / restEnergyAtomEV)
    have h2 := sq_nonneg (Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV))
    linarith
  have hDge : (4e10 : ℝ) ≤ 4 * restEnergyAtomEV *
      (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
    have hR1s : (1e10 : ℝ) ≤ restEnergyAtomEV *
        (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
      calc (1e10 : ℝ) = 1e10 * 1 := by norm_num
        _ ≤ restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 :=
          mul_le_mul hRge h1sge1 zero_le_one hRpos.le
    have h4 := mul_le_mul_of_nonneg_left hR1s (by norm_num : (0:ℝ) ≤ 4)
    have h5 : (4e10 : ℝ) = 4 * 1e10 := by norm_num
    linarith [h4, h5]
  have hNub : givenDeltaUEV ^ 2 * (4 - (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2)
      ≤ 1.21 * (3 * 1.1e-10) :=
    mul_le_mul hΔU'2.le hB3 hbrnn (by norm_num)
  have h1 : (1.21 : ℝ) * (3 * 1.1e-10) = 3.993e-10 := by norm_num
  have h2 : (3.993e-10 : ℝ) < 4e-10 := by norm_num
  have h3 : (1e-20 : ℝ) * 4e10 = 4e-10 := by norm_num
  have h4 : (1e-20 : ℝ) * 4e10 ≤ 1e-20 * (4 * restEnergyAtomEV *
      (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2) :=
    mul_le_mul_of_nonneg_left hDge (by norm_num)
  have hNlt : givenDeltaUEV ^ 2 * (4 - (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2)
      < 1e-20 * (4 * restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2) := by
    linarith [hNub, h1, h2, h3, h4]
  exact (div_lt_iff₀ hden).mpr hNlt

/-- Certified numerical bounds on the raw quantity:
`ℏω_min − ΔU ∈ (2.025, 2.035)×10⁻¹¹ eV`. -/
theorem rawExcessEV_bounds :
    rawExcessEV ∈ Set.Ioo (2.025e-11 : ℝ) (2.035e-11 : ℝ) := by
  rw [rawExcessEV_eq_sqrtForm]
  have hRpos : (0:ℝ) < restEnergyAtomEV := by
    have hmc2pos : (0:ℝ) < t1c2Instance.m * t1c2Instance.c ^ 2 :=
      mul_pos t1c2Instance.hm (pow_pos t1c2Instance.hc 2)
    have heV : (0:ℝ) < electronVoltSI := by unfold electronVoltSI; norm_num
    rw [show restEnergyAtomEV = t1c2Instance.m * t1c2Instance.c ^ 2 / electronVoltSI from rfl]
    exact div_pos hmc2pos heV
  have hRge : (1.4865e10 : ℝ) ≤ restEnergyAtomEV := by
    unfold restEnergyAtomEV givenMassAMU atomicMassUnitSI speedOfLightSI electronVoltSI
    rw [le_div_iff₀ (by norm_num)]
    norm_num
  have hRle : restEnergyAtomEV ≤ (1.4938e10 : ℝ) := by
    unfold restEnergyAtomEV givenMassAMU atomicMassUnitSI speedOfLightSI electronVoltSI
    rw [div_le_iff₀ (by norm_num)]
    norm_num
  have hΔU'pos : (0:ℝ) < givenDeltaUEV := by unfold givenDeltaUEV; norm_num
  have hΔU'2 : givenDeltaUEV ^ 2 = 1.21 := by unfold givenDeltaUEV; norm_num
  have hxpos : (0:ℝ) < givenDeltaUEV / restEnergyAtomEV := div_pos hΔU'pos hRpos
  have hx1 : givenDeltaUEV / restEnergyAtomEV < 1 := by
    rw [div_lt_one hRpos]
    have h3 : givenDeltaUEV < (1.4865e10 : ℝ) := by unfold givenDeltaUEV; norm_num
    linarith
  have hx : givenDeltaUEV / restEnergyAtomEV ≤ 1.1e-10 := by
    rw [div_le_iff₀ hRpos]
    have h1 : givenDeltaUEV = 1.1e-10 * (1e10 : ℝ) := by unfold givenDeltaUEV; norm_num
    have hR10 : (1e10 : ℝ) ≤ restEnergyAtomEV := by linarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left hR10 (by norm_num)
  have hspos : (0:ℝ) < Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) :=
    Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) ^ 2 =
      1 - givenDeltaUEV / restEnergyAtomEV := Real.sq_sqrt (by linarith)
  have hsle1 : Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - givenDeltaUEV / restEnergyAtomEV ≤ 1 by linarith)
    rwa [Real.sqrt_one] at h
  have hsge : 1 - givenDeltaUEV / restEnergyAtomEV ≤
      Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by
    rw [Real.le_sqrt (by linarith) (by linarith)]
    nlinarith [hxpos]
  have hsge' : 1 - 1.1e-10 ≤ Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by
    linarith [hsge, hx]
  have h1spos : (0:ℝ) < 1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by linarith
  have hkey : givenDeltaUEV * (1 - Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) /
        (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV))
      = givenDeltaUEV * (givenDeltaUEV / restEnergyAtomEV) /
          (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
    have h1 : (1 - Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) *
          (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV))
        = givenDeltaUEV / restEnergyAtomEV := by
      linear_combination -hs2
    rw [div_eq_div_iff h1spos.ne' (pow_pos h1spos 2).ne']
    linear_combination
      givenDeltaUEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) * h1
  constructor
  · -- lower bound: raw > ΔU'²/(4R) ≥ 2.025e-11
    have h1s4 : (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 ≤ 4 := by
      nlinarith [hsle1, Real.sqrt_nonneg (1 - givenDeltaUEV / restEnergyAtomEV)]
    have hrawge : givenDeltaUEV ^ 2 / (4 * restEnergyAtomEV) ≤
        givenDeltaUEV * (givenDeltaUEV / restEnergyAtomEV) /
          (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hRpos) (pow_pos h1spos 2)]
      have hcan : givenDeltaUEV * (givenDeltaUEV / restEnergyAtomEV) * (4 * restEnergyAtomEV)
          = 4 * givenDeltaUEV ^ 2 := by
        field_simp [hRpos.ne']
      have hs1 : givenDeltaUEV ^ 2 * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2
          ≤ givenDeltaUEV ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left h1s4 (sq_nonneg _)
      have hs2' : givenDeltaUEV ^ 2 * 4 = 4 * givenDeltaUEV ^ 2 := by ring
      linarith [hs1, hs2', hcan]
    have hLO : (2.025e-11 : ℝ) < givenDeltaUEV ^ 2 / (4 * restEnergyAtomEV) := by
      rw [hΔU'2, lt_div_iff₀ (mul_pos (by norm_num) hRpos)]
      have he : (2.025e-11 : ℝ) * (4 * restEnergyAtomEV) = 8.1e-11 * restEnergyAtomEV := by ring
      rw [he]
      have h2 := mul_le_mul_of_nonneg_left hRle (by norm_num : (0:ℝ) ≤ 8.1e-11)
      have h3 : (8.1e-11 : ℝ) * 1.4938e10 = 1.209978 := by norm_num
      linarith [h2, h3]
    rw [hkey]
    exact lt_of_lt_of_le hLO hrawge
  · -- upper bound: raw ≤ ΔU'²/(R·3.99999999956) < 2.035e-11
    have h1s2ge : (3.99999999956 : ℝ) ≤
        (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 := by
      have h10 : (2:ℝ) - 1.1e-10 = 1.99999999989 := by norm_num
      have h1 : (1.99999999989 : ℝ) ≤ 1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV) := by
        linarith [hsge', h10]
      have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.99999999989) h1 2
      have h3 : (3.99999999956 : ℝ) ≤ 1.99999999989 ^ 2 := by norm_num
      linarith [h2, h3]
    have hrawle : givenDeltaUEV * (givenDeltaUEV / restEnergyAtomEV) /
          (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2
        ≤ givenDeltaUEV ^ 2 /
            (restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2) :=
      le_of_eq (by field_simp [hRpos.ne', h1spos.ne'])
    have hC : (0:ℝ) < restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 :=
      mul_pos hRpos (pow_pos h1spos 2)
    have hle : restEnergyAtomEV * (3.99999999956 : ℝ) ≤
        restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1s2ge hRpos.le
    have hrawle2 : givenDeltaUEV ^ 2 /
          (restEnergyAtomEV * (1 + Real.sqrt (1 - givenDeltaUEV / restEnergyAtomEV)) ^ 2)
        ≤ givenDeltaUEV ^ 2 / (restEnergyAtomEV * 3.99999999956) :=
      div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos hRpos (by norm_num)) hle
    have hHI : givenDeltaUEV ^ 2 / (restEnergyAtomEV * 3.99999999956) < (2.035e-11 : ℝ) := by
      rw [hΔU'2, div_lt_iff₀ (mul_pos hRpos (by norm_num))]
      have h1 := mul_le_mul_of_nonneg_left hRge (by norm_num : (0:ℝ) ≤ 3.99999999956)
      have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2.035e-11)
      have h3 : (1.21 : ℝ) < 2.035e-11 * (1.4865e10 * 3.99999999956) := by norm_num
      linarith [h2, h3]
    rw [hkey]
    exact lt_of_le_of_lt (le_trans hrawle hrawle2) hHI

/-- **Source-derived rounding rule.**  The data are given to three significant
figures (`ΔU = 1.10 eV`, `m = 16.0 amu`, `θ = π/6` exact) and the raw value is
of order `10⁻¹¹ eV`, so the reported value rounds the raw quantity to the
nearest multiple of `10⁻¹³ eV` (three significant figures in eV, the unit the
problem requests). -/
noncomputable def reportedExcessEV : ℝ :=
  (round (rawExcessEV * 1e13) : ℝ) * 1e-13

/-- The mantissa of the reported value: `rawExcessEV·10¹³` rounds to `203`. -/
theorem reportedExcessEV_mantissa : round (rawExcessEV * 1e13) = 203 := by
  obtain ⟨hlow, hhigh⟩ := rawExcessEV_bounds
  have h5 : (2.025e-11 : ℝ) * 1e13 < rawExcessEV * 1e13 :=
    mul_lt_mul_of_pos_right hlow (by norm_num : (0:ℝ) < 1e13)
  have h6 : rawExcessEV * 1e13 < (2.035e-11 : ℝ) * 1e13 :=
    mul_lt_mul_of_pos_right hhigh (by norm_num : (0:ℝ) < 1e13)
  have h7 : (2.025e-11 : ℝ) * 1e13 = 202.5 := by norm_num
  have h8 : (2.035e-11 : ℝ) * 1e13 = 203.5 := by norm_num
  rw [round_eq, Int.floor_eq_iff]
  constructor
  · have h203 : ((203 : ℤ) : ℝ) = 203 := by norm_num
    rw [h203]
    linarith [h5, h7]
  · have h204 : ((203 : ℤ) : ℝ) + 1 = 204 := by norm_num
    rw [h204]
    linarith [h6, h8]

/-- **T1-C2 main result** (blueprint `thm:physics:ipho_2026_t1_c2:target`):
the recoil excess at `θ = π/6`, `ΔU = 1.10 eV`, `m = 16.0 amu`, reported to
three significant figures in electronvolts, is

`ℏω_min − ΔU ≈ 2.03×10⁻¹¹ eV`. -/
theorem reportedExcessEV_value : reportedExcessEV = 2.03e-11 := by
  rw [reportedExcessEV, reportedExcessEV_mantissa]
  norm_num

end IPhO2026.T1C2

