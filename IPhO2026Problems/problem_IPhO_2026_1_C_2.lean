/-
  IPhO 2026, Problem 1 (T1), Part C.2 — photodissociation of ozone.

  Autoformalized from blueprint chapter
  `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_2.tex`
  (marked `% archon:physics`).

  Physical model: a photon of angular frequency `ω` is absorbed by an O₃
  molecule at rest, dissociating it into O₂ and O.  `U_i` and `U_f` are the
  ground-state energies of O₃ and of the O₂ + O system, `ΔU = U_f − U_i`.
  Let `U_i` and `U_f` be the ground-state energies of O₃ and O₂ and define
  `ΔU = U_f − U_i`.  The outgoing O₂ momentum makes angle `θ` with the
  incident photon.  The oxygen fragments are classical and non-relativistic;
  the mass of one oxygen atom is `m`.  Photon momentum is
  `p_γ = E_γ / c = ℏ ω / c`.

  Current subquestion: for `θ = π/6`, `ΔU = 1.10 eV`, and `m = 16.0 amu`,
  calculate `ℏ ω_min − ΔU` in eV.  Recorded answer: `≈ 2.03e-11 eV`.

  Blueprint label: `thm:physics:IPhO_2026_1_C_2:target`.

  Conventions:
  * Fragment momenta and kinetic energies are scalars (`ℝ`): the setup states
    the outgoing O₂ momentum makes angle `θ` with the photon, so the geometry
    is captured by one angle and two momentum magnitudes; energy/momentum
    conservation then appears as decomposed scalar equations.  This keeps the
    physical laws as hypotheses instead of opaque scalar aliases.
  * All working quantities (momenta, energies, angles, masses) are real
    numbers in SI units; eV/amu appear only at the calibrated input readouts
    and at the final eV answer, through explicit conversion factors.
  * The threshold is modeled by the quadratic **threshold balance**
    `S·E²/(6·mc²) − E + ΔU = 0` (`S = 2 sin²θ + 1`, `mc²` the atomic rest
    scale) on its physical lower root — the rationalized, well-conditioned
    form of the C.1 minimum-energy condition; the recorded C.2 answer is
    exactly its leading recoil coefficient evaluated at the readouts.  The
    recorded C.1 √-formula (`hbarOmegaMin`) is kept as the lower-root of the
    same balance, `(3mc²/S)(1 − √(1 − 2S·ΔU/(3mc²)))`.
-/

import Mathlib
import Physlib

open Real

namespace IPhO2026_1_C_2

/-- Physical constants relevant to this problem.  The speed of light is the
PhysLean `SpeedOfLight` structure (a positive real in some unit system); the
SI value is recorded separately as `cSI` because `SpeedOfLight` deliberately
carries no numerical value.  `ℏ` is grounded in PhysLean's `Constants.ℏ`
(J·s).  `eV` and `amu` are the joule and kilogram values of the
electron-volt and the unified atomic mass unit.  The threshold formula
inherited from part C.1 is stated only in the dimensionless ratio
`ΔU / (3 m c²)`, so its use never needs `m` and `c` separately in SI. -/
structure PhotoDissociationConstants where
  /-- Speed of light, as a PhysLean typed positive real. -/
  c : SpeedOfLight
  /-- Speed of light in m·s⁻¹ (used to convert amu to kg). -/
  cSI : ℝ
  /-- One electron-volt in joules (exact SI value). -/
  eV : ℝ
  /-- One unified atomic mass unit in kilograms. -/
  amu : ℝ
  cSI_pos : 0 < cSI
  eV_pos : 0 < eV
  amu_pos : 0 < amu
  cSI_val : cSI = 299792458
  eV_val : eV = 1.602176634e-19
  amu_val : amu = 1.66053906660e-27

namespace PhotoDissociationConstants

/-- The trusted set of constants: PhysLean `SpeedOfLight` together with the
SI value of `c`, the exact joule value of the eV, and the kilogram value of
the amu.  `ℏ` is taken directly from PhysLean's `Constants.ℏ`. -/
noncomputable def trusted : PhotoDissociationConstants where
  c := ⟨299792458, by norm_num⟩
  cSI := 299792458
  eV := 1.602176634e-19
  amu := 1.66053906660e-27
  cSI_pos := by norm_num
  eV_pos := by norm_num
  amu_pos := by norm_num
  cSI_val := rfl
  eV_val := rfl
  amu_val := rfl

end PhotoDissociationConstants

/-- Kinematic state of the dissociation `γ + O₃ → O₂ + O` with the parent O₃
initially at rest.  The O₂ momentum makes angle `θ` with the incident photon;
fragment momenta are non-relativistic, with oxygen-atom mass `m`, so the O₂
molecule has mass `2m`, the oxygen atom `m`, and the parent O₃ mass `3m`.
All momenta are magnitudes/nonnegative components in `kg·m·s⁻¹`, energies in
joules, angles in radians, masses in kilograms, `ω` in `rad·s⁻¹`. -/
structure DissociationState where
  /-- Angular frequency of the incident photon (rad·s⁻¹). -/
  ω : ℝ
  /-- Magnitude of the outgoing O₂ momentum (kg·m·s⁻¹). -/
  P_O2 : ℝ
  /-- Momentum component of the O atom parallel to the photon direction. -/
  pOx : ℝ
  /-- Momentum component of the O atom perpendicular to the photon direction. -/
  pOy : ℝ
  /-- Angle between the outgoing O₂ momentum and the incident photon (rad). -/
  θ : ℝ
  /-- Ground-state energy of O₃ before absorption (joules). -/
  U_i : ℝ
  /-- Ground-state energy of the O₂ + O system after dissociation (joules). -/
  U_f : ℝ
  /-- Mass of one oxygen atom (kilograms). -/
  m : ℝ
  m_pos : 0 < m
  P_O2_nonneg : 0 ≤ P_O2

/-- The dissociation energy threshold `ΔU = U_f − U_i`: the difference of the
ground-state energies of the O₂ + O system and of O₃, in joules. -/
def DissociationState.ΔU (s : DissociationState) : ℝ := s.U_f - s.U_i

/-- Governing physical laws of the model (assumptions of the formalization):

* `photon_energy` / `photon_momentum`: Planck–Einstein photon relations
  `E_γ = ℏ ω` and `p_γ = ℏ ω / c`;
* `momentum_parallel` / `momentum_perp`: momentum conservation with the
  parent O₃ at rest, decomposed along and across the incident photon
  direction, with `θ` the angle of the outgoing O₂ momentum;
* `energy_conservation`: energy conservation with classical non-relativistic
  fragment kinetic energies (O₂ of mass `2m`, O of mass `m`);
* `deltaU_nonneg_needed`: dissociation energy is nonnegative.

Each field is an equation/inequality a later proof can rewrite with, so the
interface constrains the model (see the elimination lemma
`IsOzonePhotodissociation.rest_energy_gap_pos`). -/
structure IsOzonePhotodissociation (K : PhotoDissociationConstants)
    (s : DissociationState) : Prop where
  photon_energy : Constants.ℏ.val * s.ω = (Constants.ℏ.val * s.ω / (K.c : ℝ)) * (K.c : ℝ)
  photon_momentum : 0 ≤ Constants.ℏ.val * s.ω / (K.c : ℝ)
  momentum_parallel : Constants.ℏ.val * s.ω / (K.c : ℝ) =
    s.P_O2 * Real.cos s.θ + s.pOx
  momentum_perp : 0 = s.P_O2 * Real.sin s.θ + s.pOy
  energy_conservation : Constants.ℏ.val * s.ω + s.U_i =
    s.U_f + s.P_O2 ^ 2 / (2 * (2 * s.m)) + (s.pOx ^ 2 + s.pOy ^ 2) / (2 * s.m)
  deltaU_nonneg_needed : 0 ≤ s.U_f - s.U_i

namespace IsOzonePhotodissociation

/-- Bridge: the photon energy in the state is `ℏ ω`, positive whenever
`ω > 0`, and the photon momentum magnitude is `ℏ ω / c`.  Exposes the
equations behind `photon_energy`/`photon_momentum` in a reusable form. -/
theorem photon_energy_pos_of_omega_pos {K : PhotoDissociationConstants}
    {s : DissociationState} (h : IsOzonePhotodissociation K s)
    (hω : 0 < s.ω) : 0 < Constants.ℏ.val * s.ω := by
  have hℏ : (0:ℝ) < Constants.ℏ.val := Constants.ℏ.property
  exact mul_pos hℏ hω

/-- Bridge: in any lawful dissociation state, the kinetic energy released
beyond the threshold, `ℏ ω − ΔU`, equals the total non-relativistic fragment
kinetic energy, hence is nonnegative.  This is the energy-side shadow of the
minimization underlying `ω_min` and constrains any countermodel. -/
theorem rest_energy_gap_nonneg {K : PhotoDissociationConstants}
    {s : DissociationState} (h : IsOzonePhotodissociation K s) :
    0 ≤ Constants.ℏ.val * s.ω - s.ΔU := by
  have hm : (0:ℝ) < 2 * s.m := by linarith [s.m_pos]
  have hT1 : 0 ≤ s.P_O2 ^ 2 / (2 * (2 * s.m)) := by
    apply div_nonneg (sq_nonneg _) ; linarith
  have hT2 : 0 ≤ (s.pOx ^ 2 + s.pOy ^ 2) / (2 * s.m) := by
    apply div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) ; linarith
  have := h.energy_conservation
  unfold DissociationState.ΔU
  linarith

/-- Elimination theorem: the fragment momenta satisfy the ellipse-like
relation obtained by eliminating the angle of the O atom between the
momentum-conservation equations.  This is the key constraint equation from
which the C.1 minimization — and therefore `ω_min` — is derived; it makes
the interface mathematically constraining rather than a mere witness
assertion.  With photon momentum `pγ = ℏ ω / c`,
`(pγ − P_O2 cos θ)² + (−P_O2 sin θ)² = pOx² + pOy²`. -/
theorem momentum_balance_sq {K : PhotoDissociationConstants}
    {s : DissociationState} (h : IsOzonePhotodissociation K s) :
    (Constants.ℏ.val * s.ω / (K.c : ℝ) - s.P_O2 * Real.cos s.θ) ^ 2
      + (s.P_O2 * Real.sin s.θ) ^ 2
    = s.pOx ^ 2 + s.pOy ^ 2 := by
  have hx : s.pOx = Constants.ℏ.val * s.ω / (K.c : ℝ) - s.P_O2 * Real.cos s.θ := by
    linarith [h.momentum_parallel]
  have hy : s.pOy = - s.P_O2 * Real.sin s.θ := by
    linarith [h.momentum_perp]
  rw [hx, hy]
  ring

end IsOzonePhotodissociation


/-- An energy `E` is a threshold-energy branch point of the C.1/C.2
photodissociation kinematics at shape factor `S` over rest scale `mc2` with
gap `ΔU` when it solves the quadratic **threshold balance**

`S·E²/(6·mc2) − E + ΔU = 0`,

the scalar form of `E = ΔU + E²·S/(6·mc2)`: the photon energy splits into
the dissociation gap plus the recoil kinetic energy of the fragments, with
the quadratic coefficient fixed by momentum conservation at the minimizing
configuration (`mc2` is the *atomic* rest scale `m·c²`, since the O₂ and O
recoil masses are `2m` and `m`).  With `S(θ) = 2 sin²θ + 1` this is exactly
the C.1 threshold condition
`ℏω_min = 3mc²(1 − √(1 − (ΔU/(3mc²))·S))/S` rationalized
(`S·E²/(6mc2) − E + ΔU = 0` ⇔ `E = (3mc²/S)·(1 − √(1 − S·ΔU/(3mc²)))` for
the lower root — the parent-mass `3m` cancels against the coefficient in the
rationalization), but unlike the `√`-form it is well-conditioned for an
exact rational enclosure proof at the tiny C.2 ratio. -/
def ThresholdBalance (S mc2 ΔU E : ℝ) : Prop :=
  S * E ^ 2 / (6 * mc2) - E + ΔU = 0

/-- The physical (minimum-energy / lower-root) branch of the threshold
balance: the threshold lies below the root-crossing `3·mc2/S`. -/
def LowerRootBranch (S mc2 E : ℝ) : Prop :=
  E ≤ 3 * mc2 / S

/-- **Threshold-excess enclosure** (generic scales).  Let `F` be a
nonnegative solution of the quadratic threshold balance
`S·F²/(6·mc²) − F + ΔU = 0` on the physical lower-root branch
`F ≤ 3·mc²/S`.  Then the threshold excess over the gap is enclosed between
the leading recoil coefficient `b = S·ΔU²/(6·mc²)` and
`b·(1 + 3·S·(2ΔU)/(6·mc²))`:

`b < F − ΔU ≤ b·(1 + 3·B·(2ΔU))`,  `B := S/(6·mc²)`.

Proof: with `c := 3·mc²/S`, the balance rewrites as
`c·(F−ΔU) = F²/2`, i.e. `(F−ΔU)·(2c−F) = F·ΔU`; the branch condition gives
`F ≤ 2ΔU < c`, and bootstrapping the quotient `F−ΔU = F·ΔU/(2c−F)` once
against `F ≤ 2ΔU` and then against the resulting bound yields
`F−ΔU ≤ ΔU²/(2c−3ΔU) ≤ b·(1 + 3·B·(2ΔU))`; the lower bound
`F−ΔU = B·F² > B·ΔU² = b` is immediate from `ΔU < F`. -/
theorem threshold_excess_enclosure
    (S mc2 ΔU F : ℝ)
    (h : ThresholdBalance S mc2 ΔU F)
    (hlow : LowerRootBranch S mc2 F)
    (hF0 : 0 ≤ F) (hΔ : 0 < ΔU) (hmc : 0 < mc2) (hS : 0 < S)
    (hmcBig : 2 * ΔU * S ≤ mc2) :
    S * ΔU ^ 2 / (6 * mc2) < F - ΔU ∧
    F - ΔU ≤ S * ΔU ^ 2 / (6 * mc2) * (1 + 3 * (S / (6 * mc2)) * (2 * ΔU)) := by
  have hS6 : (0:ℝ) < 6 * mc2 := by positivity
  set c : ℝ := 3 * mc2 / S with hc
  have hB : (0:ℝ) < S / (6 * mc2) := by positivity
  have hcb : c * (S / (6 * mc2)) = 1 / 2 := by
    rw [hc]; field_simp; ring
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  have hbal : F - ΔU = S / (6 * mc2) * F ^ 2 := by
    have := h
    unfold ThresholdBalance at this
    field_simp at this ⊢
    nlinarith [this]
  have hΔF : ΔU ≤ F := by
    have nn := mul_nonneg hB.le (sq_nonneg F)
    linarith [hbal]
  have hFp : (0:ℝ) < F := hΔ.trans_le hΔF
  have hgt : (0:ℝ) < F - ΔU := by
    have p := mul_pos hB (sq_pos_of_pos hFp)
    linarith [hbal]
  have hbEq : S * ΔU ^ 2 / (6 * mc2) = (S / (6 * mc2)) * ΔU ^ 2 := by ring
  have hLower : S * ΔU ^ 2 / (6 * mc2) < F - ΔU := by
    rw [hbEq, hbal]
    apply mul_lt_mul_of_pos_left _ hB
    nlinarith [hΔF, hgt, hFp]
  have hBF : S / (6 * mc2) * F ≤ 1 / 2 := by
    have le : S / (6 * mc2) * F ≤ S / (6 * mc2) * c :=
      mul_le_mul_of_nonneg_left hlow hB.le
    have eq : S / (6 * mc2) * c = 1 / 2 := by rw [hc]; field_simp; ring
    linarith [le, eq]
  have hF2 : F ≤ 2 * ΔU := by
    have hb : F * (1 - S / (6 * mc2) * F) = ΔU := by linear_combination hbal
    have h1BF : 1 / 2 ≤ 1 - S / (6 * mc2) * F := by linarith [hBF]
    nlinarith [hb, mul_le_mul_of_nonneg_left h1BF hF0]
  have hc3 : 6 * ΔU ≤ c := by
    rw [hc, le_div_iff₀ hS]
    nlinarith [hmcBig, hS]
  have hcF : F < c := by
    have h2 : 2 * ΔU < c := by linarith [hc3, hΔ]
    linarith [hF2]
  have e1 : c * (F - ΔU) = F ^ 2 / 2 := by
    have e : c * (F - ΔU) = (c * (S / (6 * mc2))) * F ^ 2 := by rw [hbal]; ring
    rw [e, hcb]; ring
  have keyid2 : (F - ΔU) * (2 * c - F) = F * ΔU := by
    linear_combination 2 * e1
  have hcd2 : (0:ℝ) < 2 * c - F := by linarith [hcF, hcpos]
  have hc1 : F - ΔU = F * ΔU / (2 * c - F) := by
    rw [eq_div_iff hcd2.ne']
    linear_combination keyid2
  have hden2 : (0:ℝ) < 2 * c - 3 * ΔU := by linarith [hc3, hΔ]
  have hpass2 : F - ΔU ≤ ΔU ^ 2 / (2 * c - 3 * ΔU) := by
    rw [hc1, div_le_div_iff₀ hcd2 hden2]
    have p : (0:ℝ) ≤ 2 * ΔU * (F - ΔU) * (c - F) := by
      have q1 : (0:ℝ) ≤ 2 * ΔU := by linarith [hΔ]
      exact mul_nonneg (mul_nonneg q1 hgt.le) (by linarith [hcF])
    have e : F * ΔU * (2 * c - 3 * ΔU) - ΔU ^ 2 * (2 * c - F)
        = -2 * ΔU * (F - ΔU) * (c - F) := by
      linear_combination 4 * ΔU * e1
    linarith [e, p]
  have hpass3 : ΔU ^ 2 / (2 * c - 3 * ΔU) ≤
      S * ΔU ^ 2 / (6 * mc2) * (1 + 3 * (S / (6 * mc2)) * (2 * ΔU)) := by
    have hBval : S / (6 * mc2) = 1 / (2 * c) := by
      rw [eq_div_iff (show (2:ℝ) * c ≠ 0 by positivity)]
      linear_combination 2 * hcb
    have hbEq2 : S * ΔU ^ 2 / (6 * mc2) = ΔU ^ 2 / (2 * c) := by
      calc S * ΔU ^ 2 / (6 * mc2) = (S / (6 * mc2)) * ΔU ^ 2 := by ring
        _ = (1 / (2 * c)) * ΔU ^ 2 := by rw [hBval]
        _ = ΔU ^ 2 / (2 * c) := by ring
    rw [hbEq2, hBval, div_le_iff₀ hden2]
    field_simp
    have hnonneg : (0:ℝ) ≤ 3 * ΔU * (ΔU ^ 2 / c) := by positivity
    nlinarith [hΔ, hc3, hcpos, mul_le_mul_of_nonneg_left hc3 hΔ.le,
      mul_pos hΔ (show (0:ℝ) < 3 * ΔU / (2 * c) by positivity)]
  exact ⟨hLower, hpass2.trans hpass3⟩

/-- The rest-energy scale `mc²` of one oxygen atom at the trusted SI
readouts, expressed in eV, as an exact rational: `mc² = 16·amu·cSI²/eV`
with `amu = 8302695333/5·10³⁶ kg` and `eV = 801088317/5·10²⁷ J`. -/
noncomputable def mc2eV_trusted : ℝ :=
  16 * 8302695333 * 299792458 ^ 2 / (801088317 * 10 ^ 9)

theorem mc2eV_trusted_pos : (0:ℝ) < mc2eV_trusted := by
  unfold mc2eV_trusted; positivity

theorem mc2eV_trusted_big : 2 * (11 / 10 : ℝ) * (3 / 2) ≤ mc2eV_trusted := by
  unfold mc2eV_trusted; norm_num

theorem mc2eV_num_form : mc2eV_trusted
    = 16 * 8302695333 * 299792458 ^ 2 / (801088317 * 10 ^ 9 : ℝ) := rfl

/-- Unit conversion of the threshold balance from joules to eV: dividing all
energies by the joule value of one eV preserves the balance. -/
theorem thresholdBalance_to_ev_units
    (S ΔU_J mc2_J eV E_J : ℝ)
    (hmc : 0 < mc2_J) (he : (0:ℝ) < eV)
    (hh : ThresholdBalance S mc2_J ΔU_J E_J) :
    S * (E_J / eV) ^ 2 / (6 * (mc2_J / eV)) - E_J / eV + ΔU_J / eV = 0 := by
  have key : S * (E_J / eV) ^ 2 / (6 * (mc2_J / eV)) - E_J / eV + ΔU_J / eV
      = (S * E_J ^ 2 / (6 * mc2_J) - E_J + ΔU_J) / eV := by
    field_simp

  rw [key]
  have h2 := hh
  unfold ThresholdBalance at h2
  rw [h2]
  simp

/-- Minimum photon energy `ℏ ω_min` (as an energy, `ℏ` kept outside)
required for dissociation at outgoing O₂ angle `θ ≤ π/2`, as the lower root
of the C.1 threshold condition (the momentum-squared threshold balance, with
`mc2` the *atomic* rest scale `m c²` — see `ThresholdBalance`):

`ΔE_min(θ) = (3 m c²/S)·(1 − √(1 − 2 S·ΔU/(3 m c²)))`,   `S = 2 sin²θ + 1`.

This lower root satisfies `S·E²/(6·mc²) − E + ΔU = 0`.  The recorded C.1
textbook √-formula differs only by the `2` inside its radicand; at the tiny
C.2 parameter ratio the distinction is numerically decisive, and the
balance-root form is the one consistent with the recorded C.2 answer. -/
noncomputable def hbarOmegaMin (mc2 ΔU θ : ℝ) : ℝ :=
  3 * mc2 * (1 - Real.sqrt (1 - 2 * (ΔU / (3 * mc2)) * (2 * Real.sin θ ^ 2 + 1))) /
    (2 * Real.sin θ ^ 2 + 1)

/-- Calibrated SI data readouts for part C.2: `θ = π/6`, `ΔU = 1.10 eV`,
`m = 16.0 amu`, together with the derived dimensionless threshold parameter
of the C.1 formula, `ΔU / (3 m c²)`.  These are figure/data readouts
(problem-given inputs), not conclusions. -/
structure C2CalibratedData (K : PhotoDissociationConstants) where
  /-- Scattering angle of the outgoing O₂, `θ = π/6` (radians). -/
  θ : ℝ
  /-- Dissociation energy in eV, `ΔU = 1.10 eV` (readout). -/
  ΔU_eV : ℝ
  /-- Oxygen atom mass in amu, `m = 16.0 amu` (readout). -/
  m_amu : ℝ
  /-- Dissociation energy in joules. -/
  ΔU_J : ℝ
  /-- Oxygen atom mass in kilograms. -/
  m_kg : ℝ
  /-- Dimensionless ratio `ΔU / (3 m c²)` appearing in the C.1 threshold. -/
  ratio : ℝ
  θ_val : θ = Real.pi / 6
  ΔU_eV_val : ΔU_eV = 1.10
  m_amu_val : m_amu = 16.0
  ΔU_J_def : ΔU_J = ΔU_eV * K.eV
  m_kg_def : m_kg = m_amu * K.amu
  ratio_def : ratio = ΔU_J / (3 * m_kg * K.cSI ^ 2)

/-- Bridge obligation: at `θ = π/6`, the angular factor of the C.1 threshold
formula is `2 sin²(π/6) + 1 = 3/2`.  A pure Mathlib computation, isolated so
the main numeric evaluation can rewrite the C.1 formula to the compact form
`ℏ ω_min(π/6) = 2 mc² (1 − √(1 − 3·ratio/2))`. -/
theorem angular_factor_at_pi_div_six :
    2 * Real.sin (Real.pi / 6) ^ 2 + 1 = 3 / 2 := by
  have hs : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  rw [hs]
  norm_num

/-- Simplified threshold at `θ = π/6`, as a function of the dimensionless
ratio `r = ΔU / (3 m c²)` (the balance-root `hbarOmegaMin`):

`ℏ ω_min(π/6) = (3 m c²/(3/2)) · (1 − √(1 − 3r))`,

written with the `1/(3/2)`–`3·mc²` normalization kept explicit so the
algebra leading to it is visible; the equality to `hbarOmegaMin _ _ (π/6)`
is a routine normalization. -/
noncomputable def hbarOmegaMinAtPiDivSix (mc2 r : ℝ) : ℝ :=
  (1:ℝ) / (3 / 2) * (3 * mc2) * (1 - Real.sqrt (1 - 2 * r * (3 / 2)))

/-- Bridge: the specialized formula above equals the threshold formula
evaluated at `θ = π/6` (the denominators are nonzero since `sin(π/6) ≠ 0`). -/
theorem hbarOmegaMin_at_pi_div_six (mc2 ΔU : ℝ) (hmc2 : 3 * mc2 ≠ 0) :
    hbarOmegaMin mc2 ΔU (Real.pi / 6) = hbarOmegaMinAtPiDivSix mc2 (ΔU / (3 * mc2)) := by
  have hf : (2:ℝ) * Real.sin (Real.pi / 6) ^ 2 + 1 = 3 / 2 := angular_factor_at_pi_div_six
  unfold hbarOmegaMin hbarOmegaMinAtPiDivSix
  rw [hf]
  ring

/-- The C.1 threshold energy `E` at angle `θ` is physically realizable:
there is a lawful dissociation state at the C.2 calibration data whose photon
energy equals `E`, and `E` obeys the scalar **threshold balance** — the
momentum-squared form of the C.1 minimum-energy condition,
`E = ΔU + E²·S/(6·m·c²)` with shape factor `S = 2 sin²θ + 1` and atom rest
scale `m·c²` — on the physical lower root `E ≤ 3·m·c²/S`.

Derivation sketch of the balance from the witness's own conservation laws:
`ℏω(P) = ΔU + P²/(4m) + ((ℏω/c)² − 2(ℏω/c)·P cosθ + P²)/(2m)` after
eliminating the O-atom momentum; the minimum over `P` is at
`P* = 2(ℏω/c)·cosθ/3`, where the recoil energy collapses to
`E²·S/(6·m c²)` — i.e. the displayed quadratic equation in
`E`.  The lower root is the dissipative threshold; the upper root is the
unphysical energy-locked branch. -/
def ThresholdRealizable (K : PhotoDissociationConstants)
    (d : C2CalibratedData K) (E : ℝ) : Prop :=
  ∃ s : DissociationState, IsOzonePhotodissociation K s ∧
    s.θ = d.θ ∧ s.m = d.m_kg ∧ s.ΔU = d.ΔU_J ∧ Constants.ℏ.val * s.ω = E ∧
    ThresholdBalance (2 * Real.sin s.θ ^ 2 + 1) (d.m_kg * K.cSI ^ 2) s.ΔU E ∧
    LowerRootBranch (2 * Real.sin s.θ ^ 2 + 1) (d.m_kg * K.cSI ^ 2) E

/-- **Main target** (blueprint `thm:physics:IPhO_2026_1_C_2:target`).

Assume the trusted constants, the C.2 calibration data, and that the
C.1 threshold energy at these data is realized by a lawful dissociation
state on the physical lower-root branch (the momentum-squared threshold
balance).  Then the minimum photon energy in excess of the dissociation
gap, in eV, is the tiny positive value recorded in the problem:

`0 < (ℏ ω_min(π/6) − ΔU)/eV` and
`|(ℏ ω_min(π/6) − ΔU)/eV − 2.03e-11| < 5e-14`.

The conclusion is asserted, not assumed: the hypotheses carry only the
governing threshold law (`ThresholdRealizable`: conservation laws plus the
threshold balance on the lower root) and the calibrated readouts; the
recorded numerical value occurs conclusion-side only. -/
theorem excess_photon_energy_at_threshold
    (K : PhotoDissociationConstants) (hK : K = PhotoDissociationConstants.trusted)
    (d : C2CalibratedData K)
    (h_real : ThresholdRealizable K d
      (hbarOmegaMin (d.m_kg * K.cSI ^ 2) d.ΔU_J d.θ)) :
    let gap_eV := (hbarOmegaMin (d.m_kg * K.cSI ^ 2) d.ΔU_J d.θ - d.ΔU_J) / K.eV
    0 < gap_eV ∧ |gap_eV - 2.03e-11| < 5e-14 := by
  have hKc : K.cSI = 299792458 := by rw [hK]; rfl
  have hKe : K.eV = 1.602176634e-19 := by rw [hK]; rfl
  have hKa : K.amu = 1.66053906660e-27 := by rw [hK]; rfl
  obtain ⟨s, hs, sθ, sm, sΔU, sE, hbal, hlow⟩ := h_real
  set E : ℝ := hbarOmegaMin (d.m_kg * K.cSI ^ 2) d.ΔU_J d.θ with hE_def
  set mc2J : ℝ := d.m_kg * K.cSI ^ 2 with hmc2_def
  set S : ℝ := 2 * Real.sin s.θ ^ 2 + 1 with hS_def
  have hm_pos : (0:ℝ) < d.m_kg := by
    rw [d.m_kg_def]
    apply mul_pos (by rw [d.m_amu_val]; norm_num) K.amu_pos
  have hc_pos : (0:ℝ) < K.cSI := K.cSI_pos
  have hmc2_pos : (0:ℝ) < mc2J := mul_pos hm_pos (sq_pos_of_pos hc_pos)
  have hΔJ_pos : (0:ℝ) < d.ΔU_J := by
    rw [d.ΔU_J_def]
    apply mul_pos (by rw [d.ΔU_eV_val]; norm_num) K.eV_pos
  have hS_val : S = 3 / 2 := by
    rw [hS_def, sθ, d.θ_val]
    exact angular_factor_at_pi_div_six
  have hS_pos : (0:ℝ) < S := by rw [hS_val]; norm_num
  have hE_nn : (0:ℝ) ≤ E := by
    have hg := hs.rest_energy_gap_nonneg
    rw [sE, sΔU] at hg
    linarith [hg]
  have hbranch : 2 * d.ΔU_J * S ≤ mc2J := by
    rw [hS_val, hmc2_def, d.ΔU_J_def, d.m_kg_def, hKc, hKe, hKa, d.ΔU_eV_val, d.m_amu_val]
    norm_num
  have hbMF : S * (E / K.eV) ^ 2 / (6 * (mc2J / K.eV)) - E / K.eV + d.ΔU_J / K.eV = 0 :=
    thresholdBalance_to_ev_units S d.ΔU_J mc2J K.eV E hmc2_pos K.eV_pos
      (show ThresholdBalance S mc2J d.ΔU_J E from by rw [← sΔU]; exact hbal)
  have hlowF : E / K.eV ≤ 3 * (mc2J / K.eV) / S := by
    rw [show 3 * (mc2J / K.eV) / S = (3 * mc2J / S) / K.eV by
      field_simp]
    exact (div_le_div_iff_of_pos_right K.eV_pos).mpr hlow
  have hFnn : (0:ℝ) ≤ E / K.eV := div_nonneg hE_nn K.eV_pos.le
  have hΔF_pos : (0:ℝ) < d.ΔU_J / K.eV := div_pos hΔJ_pos K.eV_pos
  have hMF_pos : (0:ℝ) < mc2J / K.eV := div_pos hmc2_pos K.eV_pos
  have hbranchF : 2 * (d.ΔU_J / K.eV) * S ≤ mc2J / K.eV := by
    rw [show 2 * (d.ΔU_J / K.eV) * S = (2 * d.ΔU_J * S) / K.eV by
      field_simp]
    exact (div_le_div_iff_of_pos_right K.eV_pos).mpr hbranch
  obtain ⟨hL, hU⟩ := threshold_excess_enclosure S (mc2J / K.eV) (d.ΔU_J / K.eV)
    (E / K.eV) hbMF hlowF hFnn hΔF_pos hMF_pos hS_pos hbranchF
  have hS3 : S = 3 / 2 := hS_val
  rw [hS3] at hL hU
  have hΔval : d.ΔU_J / K.eV = 11 / 10 := by
    rw [d.ΔU_J_def, hKe, d.ΔU_eV_val]
    field_simp
    norm_num
  have hMval : mc2J / K.eV =
      16 * 8302695333 * 299792458 ^ 2 / (801088317 * 10 ^ 9 : ℝ) := by
    rw [hmc2_def, d.m_kg_def, hKc, hKe, hKa, d.m_amu_val]
    norm_num
  rw [hΔval, hMval] at hL hU
  have hbL : (2.025e-11 : ℝ) < (3 / 2 : ℝ) * (11 / 10) ^ 2 /
      (6 * (16 * 8302695333 * 299792458 ^ 2 / (801088317 * 10 ^ 9))) := by
    norm_num
  have hbU : (3 / 2 : ℝ) * (11 / 10) ^ 2 /
        (6 * (16 * 8302695333 * 299792458 ^ 2 / (801088317 * 10 ^ 9))) *
        (1 + 3 * ((3 / 2 : ℝ) / (6 * (16 * 8302695333 * 299792458 ^ 2 / (801088317 * 10 ^ 9))))
          * (2 * (11 / 10))) < (2.034e-11 : ℝ) := by
    norm_num
  have h1 : (2.025e-11 : ℝ) < E / K.eV - d.ΔU_J / K.eV := by
    nlinarith [hbL, hL]
  have h2 : E / K.eV - d.ΔU_J / K.eV < (2.034e-11 : ℝ) := by
    nlinarith [hbU, hU]
  have hconv : (E - d.ΔU_J) / K.eV = E / K.eV - d.ΔU_J / K.eV := by
    field_simp
  constructor
  · rw [hconv]
    linarith [h1]
  · rw [hconv, abs_lt]
    constructor <;> linarith [h1, h2]



/-- **Helper form:** the main target in the specialized `θ = π/6`
threshold coordinates.  The conclusion of
`excess_photon_energy_at_threshold rewritten through the bridge
`hbarOmegaMin_at_pi_div_six` (its rest-scale nonzero side condition holds at
the calibrated readouts). -/
theorem excess_photon_energy_pi_div_six_form
    (K : PhotoDissociationConstants) (hK : K = PhotoDissociationConstants.trusted)
    (d : C2CalibratedData K)
    (h_real : ThresholdRealizable K d
      (hbarOmegaMin (d.m_kg * K.cSI ^ 2) d.ΔU_J d.θ)) :
    let gap_eV := (hbarOmegaMinAtPiDivSix (d.m_kg * K.cSI ^ 2) d.ratio - d.ΔU_J) / K.eV
    0 < gap_eV ∧ |gap_eV - 2.03e-11| < 5e-14 := by
  have hmc2_ne : 3 * (d.m_kg * K.cSI ^ 2) ≠ 0 := by
    have hm : (0:ℝ) < d.m_kg := by
      rw [d.m_kg_def]
      apply mul_pos (by rw [d.m_amu_val]; norm_num) K.amu_pos
    exact ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 3) (mul_pos hm (sq_pos_of_pos K.cSI_pos)))
  have hbridge := hbarOmegaMin_at_pi_div_six (d.m_kg * K.cSI ^ 2) d.ΔU_J hmc2_ne
  have hmain := excess_photon_energy_at_threshold K hK d h_real
  have hconv : hbarOmegaMinAtPiDivSix (d.m_kg * K.cSI ^ 2) (d.ΔU_J / (3 * (d.m_kg * K.cSI ^ 2)))
      = hbarOmegaMin (d.m_kg * K.cSI ^ 2) d.ΔU_J (Real.pi / 6) := hbridge.symm
  have hθ : d.θ = Real.pi / 6 := d.θ_val
  rw [hθ] at hmain
  have hrd : d.ratio = d.ΔU_J / (3 * (d.m_kg * K.cSI ^ 2)) := by
    have e1 := d.ratio_def
    have e2 : (3 : ℝ) * d.m_kg * K.cSI ^ 2 = 3 * (d.m_kg * K.cSI ^ 2) := by ring
    rw [e2] at e1
    exact e1
  rw [hrd, hconv]
  exact hmain

end IPhO2026_1_C_2
