import Mathlib

/-!
# IChO 2026, Theory Problem T8, subquestion 8.9 — photosensitizer quenching

Source: 58th International Chemistry Olympiad, Tashkent, Uzbekistan, 2026,
Theory Problem 8 ("Recycling of Carbon Dioxide"), page Q8-5.

A photosensitiser PS undergoes reductive quenching of its singlet (S1) and
triplet (T1) excited states by a reductant Red:

* `PS(S1) + Red → PS•− + Red•+` with `kS = 2.7 × 10⁹ M⁻¹ s⁻¹`,
* `PS(T1) + Red → PS•− + Red•+` with `kT = 1.5 × 10⁸ M⁻¹ s⁻¹`.

The Jablonski diagram on the source page gives the competing unimolecular
channels: out of S1, fluorescence (`kF`), internal conversion (`kIC`) and
intersystem crossing (`kISC`); out of T1, phosphorescence (`kP`), non-radiative
decay (`kN`) and reverse intersystem crossing (`kRISC`).  The unquenched
emission lifetimes are `τ₀(S1) = 2.9 ns` and `τ₀(T1) = 84 μs`.

Subquestion 8.9 asks for the percentage of quenching `ηq` (in %) of the S1 and
T1 states at `[Red] = 0.1 M`, with the note `kF ≫ kISC`.

Following the recorded marking scheme (its equations 8.10.1–8.10.4), the
quenched fraction of an excited state is the share of the pseudo-first-order
quenching channel in the total first-order decay, `kq·[Red] / (k₀ + kq·[Red])`
with `k₀ = τ₀⁻¹`; equivalently the Stern–Volmer form
`kq·τ₀·[Red] / (1 + kq·τ₀·[Red])`.

All scalar quantities are represented by their real numerical readouts in the
source units (molar concentrations in `M`, first-order constants in `s⁻¹`,
second-order constants in `M⁻¹ s⁻¹`, lifetimes in `s`), matching the
conventions of the shared `IChO2026Chem` modules.
-/

namespace IChO2026.T8.A9

/-- A molar concentration is its numerical readout in the source's `M` scale. -/
abbrev MolarConcentration := ℝ

/-- A first-order rate constant is its numerical readout in `s⁻¹`. -/
abbrev FirstOrderRateConstant := ℝ

/-- A second-order rate constant is its numerical readout in `M⁻¹ s⁻¹`. -/
abbrev SecondOrderRateConstant := ℝ

/-- A lifetime is its numerical readout in seconds. -/
abbrev LifetimeSeconds := ℝ

/-- The two excited states of the photosensitiser that the reductant quenches:
the lowest excited singlet state `S1` and the lowest excited triplet state `T1`
of the source's Jablonski diagram. -/
inductive ExcitedState where
  | S1
  | T1
  deriving DecidableEq, Repr

/-- The unimolecular decay channels out of S1 on the Jablonski diagram. -/
structure S1Channels where
  /-- Fluorescence `S1 → S0 + hν` rate constant (s⁻¹ readout). -/
  kF : FirstOrderRateConstant
  /-- Internal conversion `S1 ⇝ S0` rate constant (s⁻¹ readout). -/
  kIC : FirstOrderRateConstant
  /-- Intersystem crossing `S1 ⇝ T1` rate constant (s⁻¹ readout). -/
  kISC : FirstOrderRateConstant

/-- The unimolecular decay channels out of T1 on the Jablonski diagram. -/
structure T1Channels where
  /-- Phosphorescence `T1 → S0 + hν` rate constant (s⁻¹ readout). -/
  kP : FirstOrderRateConstant
  /-- Non-radiative decay `T1 ⇝ S0` rate constant (s⁻¹ readout). -/
  kN : FirstOrderRateConstant
  /-- Reverse intersystem crossing `T1 ⇝ S1` rate constant (s⁻¹ readout). -/
  kRISC : FirstOrderRateConstant

/-- The exact first-order decay constant of S1, `kF + kIC + kISC`: the recorded
eq. 8.10.1 reads `−d[S1]/dt = (kF + kIC + kISC)·[S1]` before the approximation. -/
def intrinsicDecayS1 (J : S1Channels) : FirstOrderRateConstant :=
  J.kF + J.kIC + J.kISC

/-- The effective first-order decay constant of S1 under the problem's note
`kF ≫ kISC`, which licenses neglecting the intersystem-crossing channel:
`kF + kIC` (the recorded eq. 8.10.1 approximation).  The unquenched S1 emission
lifetime is then `τ₀(S1) = (kF + kIC)⁻¹`. -/
def effectiveDecayS1 (J : S1Channels) : FirstOrderRateConstant :=
  J.kF + J.kIC

/-- The first-order decay constant of T1, `kP + kN + kRISC`: the recorded
eq. 8.10.2 reads `−d[T1]/dt = (kP + kN + kRISC)·[T1]`, so the unquenched T1
emission lifetime is `τ₀(T1) = (kP + kN + kRISC)⁻¹`. -/
def intrinsicDecayT1 (J : T1Channels) : FirstOrderRateConstant :=
  J.kP + J.kN + J.kRISC

/-- First-order decay of an excited-state concentration readout `c` with
constant `k0`: `dc/dt = −k0·c`, the shape of the recorded eqs. 8.10.1 and
8.10.2. -/
def FirstOrderDecay (c : ℝ → ℝ) (k0 : FirstOrderRateConstant) : Prop :=
  ∀ t : ℝ, HasDerivAt c (-(k0 * c t)) t

/-- The formula for the lifetime of a reagent in a first-order reaction, as
invoked by the marking scheme: the concentration trajectory is exponential,
`c(t) = c(0)·exp(−k0·t)`. -/
theorem FirstOrderDecay_trajectory (c : ℝ → ℝ) (k0 : FirstOrderRateConstant)
    (h : FirstOrderDecay c k0) (t : ℝ) :
    c t = c 0 * Real.exp (-(k0 * t)) := by
  have hexp : ∀ s : ℝ,
      HasDerivAt (fun u => Real.exp (k0 * u)) (Real.exp (k0 * s) * k0) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => k0 * u) k0 s := hasDerivAt_const_mul k0
    have h2 := HasDerivAt.comp (x := s) (Real.hasDerivAt_exp (k0 * s)) h1
    simpa only [Function.comp_def] using h2
  -- The product `t ↦ c(t)·exp(k0·t)` has zero derivative everywhere ...
  have hg : ∀ s : ℝ, HasDerivAt (fun u => c u * Real.exp (k0 * u)) 0 s := by
    intro s
    have hm := (h s).mul (hexp s)
    rw [show -(k0 * c s) * Real.exp (k0 * s) + c s * (Real.exp (k0 * s) * k0) = 0
        from by ring] at hm
    exact hm
  -- ... hence is constant, equal to `c(0)`.
  have hgt : c t * Real.exp (k0 * t) = c 0 := by
    have hc0 := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt)
      (fun x => (hg x).deriv) t 0
    simp only [mul_zero, Real.exp_zero, mul_one] at hc0
    exact hc0
  have key : Real.exp (k0 * t) * Real.exp (-(k0 * t)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc c t = c t * (Real.exp (k0 * t) * Real.exp (-(k0 * t))) := by rw [key, mul_one]
    _ = (c t * Real.exp (k0 * t)) * Real.exp (-(k0 * t)) := by rw [mul_assoc]
    _ = c 0 * Real.exp (-(k0 * t)) := by rw [hgt]

/-- The unquenched emission lifetime `τ₀ = k0⁻¹` of a first-order reagent is the
time at which the concentration has fallen to `c(0)·e⁻¹`. -/
theorem FirstOrderDecay_at_lifetime (c : ℝ → ℝ) (k0 : FirstOrderRateConstant)
    (hk0 : 0 < k0) (h : FirstOrderDecay c k0) :
    c k0⁻¹ = c 0 * Real.exp (-1) := by
  rw [FirstOrderDecay_trajectory c k0 h k0⁻¹, mul_inv_cancel₀ (ne_of_gt hk0)]

/-- The fraction of an excited state quenched by the reductant: the share of the
pseudo-first-order quenching channel `kq·Q` in the total first-order decay
`k0 + kq·Q`, where `k0` is the intrinsic first-order decay constant of the
state, `kq` the bimolecular quenching constant, and `Q = [Red]`.  This rate
competition is the governing relation behind the recorded eqs. 8.10.3 and
8.10.4. -/
noncomputable def quenchedFraction (k0 : FirstOrderRateConstant)
    (kq : SecondOrderRateConstant) (Q : MolarConcentration) : ℝ :=
  kq * Q / (k0 + kq * Q)

/-- Recorded eqs. 8.10.3/8.10.4 in ratio-of-rates form: with excited-state
concentration readout `c ≠ 0`, the quenched fraction written as
`kq·c·Q / (k0·c + kq·c·Q)` is independent of `c`. -/
theorem quenchedFraction_eq_ratio (k0 : FirstOrderRateConstant)
    (kq : SecondOrderRateConstant) (Q c : MolarConcentration)
    (hk0 : 0 < k0) (hkq : 0 ≤ kq) (hQ : 0 ≤ Q) (hc : c ≠ 0) :
    kq * c * Q / (k0 * c + kq * c * Q) = quenchedFraction k0 kq Q := by
  unfold quenchedFraction
  have h1 : kq * c * Q = c * (kq * Q) := by ring
  have h2 : k0 * c + kq * c * Q = c * (k0 + kq * Q) := by ring
  rw [h2, h1, mul_div_mul_left _ _ hc]

/-- The Stern–Volmer form of the quenched fraction: with the unquenched emission
lifetime `τ₀ = k0⁻¹`, `ηq = kq·τ₀·Q / (1 + kq·τ₀·Q)`. -/
theorem quenchedFraction_sternVolmer (k0 : FirstOrderRateConstant)
    (kq : SecondOrderRateConstant) (Q : MolarConcentration)
    (hk0 : 0 < k0) (hkq : 0 ≤ kq) (hQ : 0 ≤ Q) :
    quenchedFraction k0 kq Q = kq * k0⁻¹ * Q / (1 + kq * k0⁻¹ * Q) := by
  have hk0' : k0 ≠ 0 := ne_of_gt hk0
  have key : 1 + kq * k0⁻¹ * Q = (k0 + kq * Q) * k0⁻¹ := by
    rw [add_mul, mul_inv_cancel₀ hk0']
    ring
  unfold quenchedFraction
  rw [key, mul_right_comm kq k0⁻¹ Q, mul_div_mul_right _ _ (inv_ne_zero hk0')]

/-- Recorded eq. 8.10.3: the S1 quenched fraction at reductant concentration `Q`
and S1 concentration readout `c`, written as the ratio of rates
`kS·c·Q / ((kF + kIC)·c + kS·c·Q)`, equals the Stern–Volmer form with
`τ₀(S1) = (kF + kIC)⁻¹`.  Using `kF + kIC` as the S1 decay constant is the
approximation licensed by the problem's note `kF ≫ kISC`. -/
theorem eq_8_10_3 (J : S1Channels) (c : MolarConcentration) (hc : c ≠ 0)
    (kS : SecondOrderRateConstant) (Q : MolarConcentration)
    (hk : 0 < J.kF + J.kIC) (hkS : 0 ≤ kS) (hQ : 0 ≤ Q) :
    kS * c * Q / ((J.kF + J.kIC) * c + kS * c * Q)
      = kS * (J.kF + J.kIC)⁻¹ * Q / (1 + kS * (J.kF + J.kIC)⁻¹ * Q) := by
  rw [quenchedFraction_eq_ratio (J.kF + J.kIC) kS Q c hk hkS hQ hc,
    quenchedFraction_sternVolmer (J.kF + J.kIC) kS Q hk hkS hQ]

/-- Recorded eq. 8.10.4: the T1 quenched fraction at reductant concentration `Q`
and T1 concentration readout `c`, written as the ratio of rates
`kT·c·Q / ((kP + kN + kRISC)·c + kT·c·Q)`, equals the Stern–Volmer form with
`τ₀(T1) = (kP + kN + kRISC)⁻¹`. -/
theorem eq_8_10_4 (J : T1Channels) (c : MolarConcentration) (hc : c ≠ 0)
    (kT : SecondOrderRateConstant) (Q : MolarConcentration)
    (hk : 0 < J.kP + J.kN + J.kRISC) (hkT : 0 ≤ kT) (hQ : 0 ≤ Q) :
    kT * c * Q / ((J.kP + J.kN + J.kRISC) * c + kT * c * Q)
      = kT * (J.kP + J.kN + J.kRISC)⁻¹ * Q
          / (1 + kT * (J.kP + J.kN + J.kRISC)⁻¹ * Q) := by
  rw [quenchedFraction_eq_ratio (J.kP + J.kN + J.kRISC) kT Q c hk hkT hQ hc,
    quenchedFraction_sternVolmer (J.kP + J.kN + J.kRISC) kT Q hk hkT hQ]

/-- The bimolecular reductive-quenching constants given on the source page:
`kS = 2.7 × 10⁹ M⁻¹ s⁻¹` for the S1 state and `kT = 1.5 × 10⁸ M⁻¹ s⁻¹` for the
T1 state. -/
def quenchingConstant : ExcitedState → SecondOrderRateConstant
  | .S1 => 2.7e9
  | .T1 => 1.5e8

/-- The unquenched emission lifetimes given on the source page, converted to
seconds: `τ₀(S1) = 2.9 ns` and `τ₀(T1) = 84 μs`. -/
def tau0 : ExcitedState → LifetimeSeconds
  | .S1 => 2.9e-9
  | .T1 => 84e-6

/-- The reductant concentration prescribed by subquestion 8.9: `[Red] = 0.1 M`. -/
def redConcentration : MolarConcentration := 0.1

/-- The requested percentage of quenching `ηq` (in %) of excited state `s` at
reductant concentration `Q`: 100 times the quenched fraction, with the intrinsic
first-order decay constant of the state given by `τ₀⁻¹` (the lifetime of a
first-order reagent is the inverse of its decay constant). -/
noncomputable def quenchingPercent (s : ExcitedState) (Q : MolarConcentration) : ℝ :=
  100 * quenchedFraction (tau0 s)⁻¹ (quenchingConstant s) Q

/-- The exact S1 percentage of quenching from the given readouts:
`ηq(S1) = 100 · (2.7×10⁹ · 2.9×10⁻⁹ · 0.1) / (1 + 2.7×10⁹ · 2.9×10⁻⁹ · 0.1)
= 78300/1783 %`. -/
theorem quenchingPercent_S1_exact :
    quenchingPercent .S1 redConcentration = 78300 / 1783 := by
  norm_num [quenchingPercent, quenchedFraction, quenchingConstant, tau0,
    redConcentration]

/-- The exact T1 percentage of quenching from the given readouts:
`ηq(T1) = 100 · (1.5×10⁸ · 84×10⁻⁶ · 0.1) / (1 + 1.5×10⁸ · 84×10⁻⁶ · 0.1)
= 126000/1261 %`. -/
theorem quenchingPercent_T1_exact :
    quenchingPercent .T1 redConcentration = 126000 / 1261 := by
  norm_num [quenchingPercent, quenchedFraction, quenchingConstant, tau0,
    redConcentration]

/-- Subquestion 8.9: the percentages of quenching of the S1 and T1 states at
`[Red] = 0.1 M` are `44 %` and `99.9 %` to the recorded precision. -/
theorem quenching_percentages :
    |quenchingPercent .S1 redConcentration - 44| ≤ 0.5 ∧
    |quenchingPercent .T1 redConcentration - 99.9| ≤ 0.05 := by
  rw [quenchingPercent_S1_exact, quenchingPercent_T1_exact]
  constructor <;> rw [abs_le] <;> constructor <;> norm_num

end IChO2026.T8.A9
