import Mathlib

/-!
# IPhO 2026, Experimental Problem 1 (E1), Part B — Vapor Pressure, Subquestion B.4

Physical situation (official pages 11–12, Fig. 19). The inner cylinder (**IC**)
contains dry air plus water vapor in equilibrium with liquid water. A syringe
arrangement keeps the **total** gas pressure inside the IC equal to the
atmospheric pressure `P_atm`. As the temperature `T` of the water falls, the
water level inside the IC is recorded via its height `H` (initial level
`h = 5.0 cm` at the start of the measurement). At the reference temperature
`T₀ = 0 °C = 273.15 K`, the extrapolated height is `H₀` and the vapor pressure
may be taken as zero. In the surrounding context, the vapor pressure obeys the
Clausius–Clapeyron relation `P_v(T) = P_v0 * exp (-(Q_v/R) * (1/T - 1/T₀))`
(Eq. (3) of the exam), where `Q_v` is the molar latent heat of vaporization of
water and `R ≈ 8.31 J/(mol·K)` is the universal gas constant.

**Current subquestion (B.4, 1 pt).** Assuming that the IC contains both dry air
and water vapor, deduce an algebraic expression for the vapor pressure `P_v` in
terms of `P_atm`, `H₀`, `H`, `T₀` and `T`, assuming the vapor pressure at
`0 °C` is zero.

**Recorded official answer.** `P_v = P_atm * (1 - (H₀ * T) / (H * T₀))`.

Modeling notes (assumption/target split):
* The gas column has a uniform cross-section `A`, so the trapped gas volume is
  `A * H`; hence `H` plays the role of the volume per unit cross-sectional
  area in the gas laws (`gasVolume H = A * H`).
* **Dalton's law plus the syringe arrangement**: the dry-air partial pressure
  and the vapor pressure sum to the constant total pressure `P_atm`.
* **Ideal-gas law** for each trapped gas component; the dry-air molar content
  is fixed because the IC is sealed after valve E is closed.
* At `T₀` the vapor pressure vanishes, so at `T₀` the dry air alone fills the
  headspace at pressure `P_atm`.
* The target conclusion is only the B.4 relation above; the Clausius–Clapeyron
  relation itself belongs to the context and to later parts (B.5/B.6), so it
  is recorded as a separate predicate `ClausiusClapeyron` for reuse, and is
  **not** a hypothesis of the B.4 target theorem.
-/

namespace IPhO2026_4_B_4

/-- Geometry of the gas column trapped in the inner cylinder (IC), Fig. 19:
a uniform cross-sectional area `crossSectionalArea` (in m²), so that the gas
volume is determined by the recorded water-level height `H`. The height `H`
acts as the volume per unit cross-sectional area of the headspace. -/
structure GasColumnGeometry where
  crossSectionalArea : ℝ
  area_pos : 0 < crossSectionalArea

/-- Volume of the trapped gas (headspace) as a function of the recorded
water-level height `H` (in m if the area is in m²). Defined for arbitrary
`H`; the physical law fields below are restricted to positive heights. -/
def gasVolume (G : GasColumnGeometry) (H : ℝ) : ℝ :=
  G.crossSectionalArea * H

/-- Clausius–Clapeyron vapor-pressure relation, Eq. (3) of the exam:
at absolute temperature `T`, the equilibrium vapor pressure equals
`P_v0 * exp (-(Q_v / R) * (1 / T - 1 / T₀))`, where `Q_v` is the molar latent
heat of vaporization of water, `R` the universal gas constant, and `P_v0` the
vapor pressure at the reference temperature `T₀`.

This relation is **context** for subquestion B.4 (it drives parts B.5/B.6);
B.4 itself only needs the modeling hypothesis that the vapor pressure
vanishes at `T₀`, see `vaporPressure_zero_at_T₀` below. -/
def ClausiusClapeyron (R Q_v T₀ P_v0 : ℝ) (P_v : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T →
    P_v T = P_v0 * Real.exp (-(Q_v / R) * (1 / T - 1 / T₀))

/-- Physical data for subquestion B.4: the trapped gas mixture of dry air and
water vapor inside the inner cylinder (IC) of Fig. 19, recorded through the
height `H` of the water column at absolute temperature `T`.

Scalar contents (all physical scalars are `ℝ`):
* `P_atm` — atmospheric (total) pressure held constant by the syringe
  arrangement (Pa);
* `T₀`, `H₀` — reference temperature `0 °C = 273.15 K` and the extrapolated
  water-level height at `T₀` (B.3 result; official sample `H₀ = 5.9 cm`);
* `dryAirMoles` — fixed molar content of dry air trapped in the headspace
  (the IC is sealed after valve E is closed);
* `vaporMoles` — molar content of the water vapor at each admitted state;
* `R` — universal gas constant, reference value `≈ 8.31 J/(mol·K)`;
* `dryAirPartialPressure`, `vaporPressure` — component partial pressures (Pa)
  at each physically admitted state `(T', H')`.

Physics fields:
* `total_pressure_eq_atm` — Dalton's law plus the syringe arrangement:
  the dry-air partial pressure and the vapor pressure sum to the constant
  total pressure `P_atm` at every admitted state (procedure, page 11);
* `vaporPressure_zero_at_T₀` — vapor pressure at `T₀` is taken as zero
  (explicit B.4 hypothesis);
* `idealGas` — each trapped gas component satisfies the ideal-gas law at
  every admitted state `(T', H')`; for the dry air the molar content is the
  fixed `dryAirMoles`.

The current B.4 target `P_v = P_atm * (1 - (H₀ * T) / (H * T₀))` is **not**
a field; it is the conclusion of `vaporPressure_eq` below. -/
structure VaporPressureB4Data where
  /-- Trapped gas column geometry (uniform cross-section) of the IC, Fig. 19. -/
  geometry : GasColumnGeometry
  /-- Atmospheric (total) pressure inside the IC, held fixed by the syringe (Pa). -/
  P_atm : ℝ
  P_atm_pos : 0 < P_atm
  /-- Universal gas constant, reference value `R ≈ 8.31 J/(mol·K)`. -/
  R : ℝ
  R_pos : 0 < R
  /-- Fixed dry-air content of the sealed headspace (mol), strictly positive. -/
  dryAirMoles : ℝ
  dryAirMoles_pos : 0 < dryAirMoles
  /-- Reference temperature `T₀ = 0 °C = 273.15 K`. -/
  T₀ : ℝ
  T₀_val : T₀ = 273.15
  /-- Extrapolated water-level height `H₀` at `T₀`, in the same length units as
  `H` (B.3 result; official sample `H₀ = 5.9 cm`). -/
  H₀ : ℝ
  H₀_pos : 0 < H₀
  /-- Dry-air partial pressure at an admitted state `(T', H')` (Pa). -/
  dryAirPartialPressure : ℝ → ℝ → ℝ
  /-- Molar content of the trapped water vapor at an admitted state `(T', H')`
  (mol); the vapor is in equilibrium with the liquid water in the IC. -/
  vaporMoles : ℝ → ℝ → ℝ
  /-- Vapor pressure of the water vapor in the IC at an admitted state
  `(T', H')` (Pa). -/
  vaporPressure : ℝ → ℝ → ℝ
  /-- The vapor molar content is nonnegative at every admitted state. -/
  vaporMoles_nonneg :
    ∀ {T' H' : ℝ}, 0 < T' → 0 < H' → 0 ≤ vaporMoles T' H'
  /-- Dalton's law plus the syringe arrangement: the dry-air partial pressure
  and the vapor pressure sum to the constant total pressure `P_atm` at every
  admitted state (experimental procedure, page 11). -/
  total_pressure_eq_atm :
    ∀ {T' H' : ℝ}, 0 < T' → 0 < H' →
      dryAirPartialPressure T' H' + vaporPressure T' H' = P_atm
  /-- Vapor pressure at the reference temperature `T₀` is taken as zero
  (B.4 hypothesis: "you can assume that the vapor pressure at 0 °C is zero"). -/
  vaporPressure_zero_at_T₀ : vaporPressure T₀ H₀ = 0
  /-- Ideal-gas law for each trapped gas component at every admitted state:
  `p_component * (A * H) = n_component * R * T`. For the dry air the molar
  content is the fixed `dryAirMoles`. -/
  idealGas :
    ∀ {T' H' : ℝ}, 0 < T' → 0 < H' →
      dryAirPartialPressure T' H' * gasVolume geometry H' = dryAirMoles * R * T' ∧
      vaporPressure T' H' * gasVolume geometry H' = vaporMoles T' H' * R * T'

namespace VaporPressureB4Data

/-- Admissible measured state for B.4: a temperature `T` together with the
recorded water-level height `H` at that temperature (data table of B.1–B.2).
Both are strictly positive physical readouts (absolute temperature in K,
height in the length unit of the experiment). -/
structure MeasuredState (D : VaporPressureB4Data) where
  T : ℝ
  T_pos : 0 < T
  H : ℝ
  H_pos : 0 < H

/-- The reference state `(T₀, H₀)` is an admissible measured state; it carries
the positivity facts needed to apply the physical law fields at `(T₀, H₀)`. -/
def referenceState (D : VaporPressureB4Data) : D.MeasuredState where
  T := D.T₀
  T_pos := D.T₀_val ▸ (by norm_num : (0 : ℝ) < 273.15)
  H := D.H₀
  H_pos := D.H₀_pos

/-- Since the vapor pressure vanishes at `T₀`, Dalton's law forces the dry air
alone to carry the whole total pressure at the reference state `(T₀, H₀)`. -/
lemma dryAirPartialPressure_at_T₀ (D : VaporPressureB4Data) (hT₀ : 0 < D.T₀) :
    D.dryAirPartialPressure D.T₀ D.H₀ = D.P_atm := by
  have h := D.total_pressure_eq_atm hT₀ D.H₀_pos
  rw [D.vaporPressure_zero_at_T₀, add_zero] at h
  exact h

/-- Combined gas-law form at an admitted state (Dalton + ideal gas for both
components): the total pressure times the headspace volume equals the total
trapped molar content times `R * T'`. -/
lemma total_pressure_mul_volume (D : VaporPressureB4Data)
    {T' H' : ℝ} (hT : 0 < T') (hH : 0 < H') :
    D.P_atm * gasVolume D.geometry H' =
      (D.dryAirMoles + D.vaporMoles T' H') * D.R * T' := by
  have htot := D.total_pressure_eq_atm hT hH
  have hgas := D.idealGas hT hH
  calc D.P_atm * gasVolume D.geometry H'
      = (D.dryAirPartialPressure T' H' + D.vaporPressure T' H') *
          gasVolume D.geometry H' := by rw [htot]
    _ = D.dryAirPartialPressure T' H' * gasVolume D.geometry H' +
          D.vaporPressure T' H' * gasVolume D.geometry H' := by ring
    _ = D.dryAirMoles * D.R * T' + D.vaporMoles T' H' * D.R * T' := by
        rw [hgas.1, hgas.2]
    _ = (D.dryAirMoles + D.vaporMoles T' H') * D.R * T' := by ring

/-- Consistency checkpoint between Eq. (3) and the B.4 zero-vapor-pressure
hypothesis: under the Clausius–Clapeyron context with reference value `P_v0`,
the hypothesis `P_v0 = 0` forces the vapor pressure to vanish at every
temperature. (Context lemma for B.5/B.6; not used by the B.4 target.) -/
theorem eq_zero_of_clausiusClapeyron_zero (D : VaporPressureB4Data)
    (Q_v P_v0 : ℝ)
    (hCC : ClausiusClapeyron D.R Q_v D.T₀ P_v0 (fun T => D.vaporPressure T D.H₀))
    (hP_v0 : P_v0 = 0)
    {T : ℝ} (hT : 0 < T) :
    D.vaporPressure T D.H₀ = 0 := by
  have h := hCC T hT
  rw [hP_v0, zero_mul] at h
  exact h

/-- **Physics formalization target (B.4).** At every admissible measured state
`(T, H)` of the trapped dry-air/water-vapor mixture, the vapor pressure is

`P_v = P_atm * (1 - (H₀ * T) / (H * T₀))`.

The Clausius–Clapeyron relation is **not** assumed here: B.4 only uses
Dalton's law with constant total pressure `P_atm`, the ideal-gas law for the
fixed dry-air content, and the vanishing of the vapor pressure at `T₀`. -/
theorem vaporPressure_eq (D : VaporPressureB4Data) (s : D.MeasuredState) :
    D.vaporPressure s.T s.H =
      D.P_atm * (1 - (D.H₀ * s.T) / (s.H * D.T₀)) := by
  have hT₀ : 0 < D.T₀ := D.T₀_val ▸ (by norm_num : (0 : ℝ) < 273.15)
  have hA : D.geometry.crossSectionalArea ≠ 0 := ne_of_gt D.geometry.area_pos
  have hHne : s.H ≠ 0 := ne_of_gt s.H_pos
  have hT₀ne : D.T₀ ≠ 0 := ne_of_gt hT₀
  have href : D.P_atm * gasVolume D.geometry D.H₀ = D.dryAirMoles * D.R * D.T₀ := by
    rw [← D.dryAirPartialPressure_at_T₀ hT₀]
    exact (D.idealGas hT₀ D.H₀_pos).1
  have hstate : D.dryAirPartialPressure s.T s.H * gasVolume D.geometry s.H =
      D.dryAirMoles * D.R * s.T := (D.idealGas s.T_pos s.H_pos).1
  simp only [gasVolume] at href hstate
  have hmul : D.geometry.crossSectionalArea *
        (D.dryAirPartialPressure s.T s.H * (s.H * D.T₀)) =
      D.geometry.crossSectionalArea * (D.P_atm * (D.H₀ * s.T)) := by
    calc D.geometry.crossSectionalArea * (D.dryAirPartialPressure s.T s.H * (s.H * D.T₀))
        = (D.dryAirPartialPressure s.T s.H * (D.geometry.crossSectionalArea * s.H)) * D.T₀ := by
          ring
      _ = (D.dryAirMoles * D.R * s.T) * D.T₀ := by rw [hstate]
      _ = (D.dryAirMoles * D.R * D.T₀) * s.T := by ring
      _ = (D.P_atm * (D.geometry.crossSectionalArea * D.H₀)) * s.T := by rw [← href]
      _ = D.geometry.crossSectionalArea * (D.P_atm * (D.H₀ * s.T)) := by ring
  have hkey : D.dryAirPartialPressure s.T s.H * (s.H * D.T₀) =
      D.P_atm * (D.H₀ * s.T) := mul_left_cancel₀ hA hmul
  have hd := D.total_pressure_eq_atm s.T_pos s.H_pos
  have hPv : D.vaporPressure s.T s.H =
      D.P_atm - D.dryAirPartialPressure s.T s.H := by linarith
  rw [hPv]
  field_simp
  linarith [hkey]

/-- Blueprint theorem environment `thm:physics:IPhO_2026_4_B_4:target`:
the B.4 target relation at an arbitrary admissible measured state, matching
the recorded official answer `P_v = P_atm * (1 - (H₀ * T) / (H * T₀))`. -/
theorem target (D : VaporPressureB4Data) (s : D.MeasuredState) :
    D.vaporPressure s.T s.H =
      D.P_atm * (1 - (D.H₀ * s.T) / (s.H * D.T₀)) := by
  exact D.vaporPressure_eq s

end VaporPressureB4Data

end IPhO2026_4_B_4
