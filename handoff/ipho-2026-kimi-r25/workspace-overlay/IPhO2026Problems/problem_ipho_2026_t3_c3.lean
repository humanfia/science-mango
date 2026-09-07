import Mathlib

/-!
# IPhO 2026 · Theory problem T3-C3 — "Carnot refrigerator of the Pm-T":
the helium temperature after one operating cycle

Autoformalization of IPhO 2026 T3-C3 (source:
`reports/ipho_2026/problem_ipho_2026_t3_c3.source.json`; problem page
`ipho_2026_source/image/T3_page-4.png` (the T3-C3 statement with the
potassium-chromate and liquid-helium data), with the cycle diagram Fig. 3b on
`ipho_2026_source/image/T3_page-3.png` and the T3-B model table on
`ipho_2026_source/image/T3_page-2.png`).

## Subquestion T3-C3 (page 14, 0.8 pts)

"Suppose that to cool 1.00 L of liquid helium initially at 1.00 K, we utilize a
2.0 moles Pm-T made of *potassium chromate*.  For this material,
`K = 1.87×10⁻⁶ K·m³/mol`, its density is `2730 kg/m³` and its molar mass is
`0.19 kg/mol`.  The Pm-T performs a Carnot refrigeration cycle with
`H₁ = 411624 A/m`, `H₂ = 311306 A/m`, `H₃ = 204618 A/m` and
`H₄ = 240446 A/m`.  After one operating cycle, calculate the final temperature
of the liquid helium.  Assume that for the liquid helium both the specific heat
capacity `c = 100 J/(kg·K)` and the density `ρ = 130 kg/m³` remain constant."

## Physical model

The Pm-T executes the Carnot refrigeration cycle `1 → 2 → 3 → 4 → 1` of
Fig. 3b (T3-C shared context): the legs `2 → 3` (at `T_c`, field magnitude
decreasing) and `4 → 1` (at `T_h`, field magnitude increasing) are isothermal;
the legs `1 → 2` and `3 → 4` are adiabatic.  The *cold reservoir is the liquid
helium bath itself*: during the single operating cycle the bath plays the role
of the cold reservoir at its current temperature `T_c = T_0 = 1.00 K` (the heat
extracted per cycle, about `0.13 J`, is small against the bath's heat content
`ρ·V·c·T_0 = 13 J`, so treating the bath as the reservoir within one cycle is
the modeling reading of "after one operating cycle"), and after the cycle the
bath temperature is updated by the constant-`c` calorimetry law.  The hot
reservoir (environment at `T_h`) receives `Q_h`; its temperature is fixed by
the Carnot consistency of the four supplied vertex fields
(`hot_reservoir_temperature_sq`, `T_h ≈ 1.424 K`) but does not enter the
helium balance.

## Supplied data (page 14)

* helium: volume `1.00 L = 1.00×10⁻³ m³` (exact litre conversion), initial
  temperature `T_0 = 1.00 K`, specific heat `c = 100 J/(kg·K)` and density
  `ρ = 130 kg/m³`, both constant;
* Pm-T (potassium chromate): `n = 2.0 mol`, `K = 1.87×10⁻⁶ K·m³/mol`, density
  `2730 kg/m³`, molar mass `0.19 kg/mol` — the last two determine the torus
  volume `V = n·(molar mass)/(density) ≈ 1.392×10⁻⁴ m³` (`pmTVolume`), which
  cancels out of the T3-B1 isothermal heat `Q = (μ₀·n·K/(2T))·(H_i² − H_f²)`
  (cf. the magnetization route `heat_cold_leg_magnetization_form`), so they do
  not appear in the final temperature;
* vertex field magnitudes `H₁ = 411624`, `H₂ = 311306`, `H₃ = 204618`,
  `H₄ = 240446 A/m` — realizing the Fig. 3b refrigerator orientation
  (`H₃ < H₂`, `H₄ < H₁`, checked numerically in
  `givenField3_lt_givenField2`, `givenField4_lt_givenField1`);
* constants-table value `μ₀ = 4π×10⁻⁷ N/A²` (`vacuumPermeabilitySI`).

## Previous-part dependencies (policy: derive_inline_from_problem_only_material)

* **T3-B1** (isothermal heat relation), explicitly licensed for reuse by the
  T3-C shared context ("the isothermal heat relation from part B may be
  reused"): at constant temperature `T`, changing the field magnitude from
  `H_i` to `H_f` transfers the signed heat `Q = (μ₀·n·K/(2T))·(H_i² − H_f²)`
  *into* the torus — the predicate `IsothermalHeatIntoTorus`.  No sibling file
  is imported.
* **T3-C2** (vertex-magnetization closure `M_1² = M_2² − M_3² + M_4²`):
  through the equation of state `T·M·V = n·K·H` this closure is the Carnot
  consistency condition on the vertex fields,
  `(H_1² − H_4²)/T_h² = (H_2² − H_3²)/T_c²`, which fixes `T_h` from the
  supplied fields (`hot_reservoir_temperature_sq`); the magnetization-language
  form of the cold-leg heat, in which the torus volume `V` appears and cancels,
  is `heat_cold_leg_magnetization_form`.

## Governing laws (assumption side)

1. `IsothermalHeatIntoTorus` on the two isothermal legs (T3-B1 reuse).
2. `AdiabaticLeg` on `1 → 2` and `3 → 4`: no heat exchanged on the adiabats.
3. `CarnotReservoirHeatRelation`: `Q_h/T_h = Q_c/T_c` (Clausius equality for
   the reversible two-isotherm cycle — the adiabats contribute no heat).
4. Reservoir identification: the cold reservoir is the helium bath, so the
   cycle's cold temperature is the bath's current temperature, `T_c = T_0`.
5. `ConstantDensityMass`: the helium mass follows from its constant density,
   `m = ρ·V`.
6. `ConstantSpecificHeatCooling` (stipulated: "both the specific heat capacity
   `c` and the density `ρ` remain constant"): the heat `Q` extracted from the
   bath lowers its temperature from `T_i` to `T_f` with `Q = m·c·(T_i − T_f)`.
7. Physical ranges and Fig. 3b branch readouts: `μ₀, n, K, T_h, T_c, T_0,
   ρ_He, V_He, c > 0`, `T_c < T_h`, `H₃ < H₂` (cold leg demagnetizes),
   `H₄ < H₁` (hot leg magnetizes).

## Derivation (answer-blind, from the laws above only)

* Cold leg `2 → 3` at `T_c = T_0`: `Q_c = (μ₀·n·K/(2T_0))·(H_2² − H_3²)`
  (`heat_absorbed_on_cold_leg`), positive on the demagnetizing branch
  (`cold_leg_heat_pos`) — heat flows from the helium into the torus.
* Helium calorimetry: `T_0 − T_f = Q_c/(ρ_He·V_He·c)`
  (`helium_temperature_drop`).
* Hence `T_f = T_0 − (μ₀·n·K/(2T_0))·(H_2² − H_3²)/(ρ_He·V_He·c)`
  (`helium_final_temperature`), the helium's temperature after one cycle.

## Current target (conclusion side only)

`helium_final_temperature` (symbolic closed form; blueprint
`thm:physics:ipho_2026_t3_c3:target`) and its packaged form
`helium_final_temperature_eq_expr` with the raw requested combination
`heliumFinalTemperatureExpr`.  The numerical section evaluates the closed form
at the supplied data: `rawFinalHeliumTemperature`, the instantiation bridge
`final_temperature_at_data`, certified bounds
`rawFinalHeliumTemperature_bounds`, the source-derived rounding rule
`reportedHeliumTemperature` (nearest `0.01 K`, the decimal precision at which
the source reports the temperature data — "initially at 1.00 K"; at this
magnitude two significant figures coincide with the 0.01 K grid) with
`reportedHeliumTemperature_mantissa`, and the reported value
`reportedHeliumTemperature_value`.  No hypothesis, premise structure or local
definition mentions the value of `T_f` or the rounded answer.

*Branch/orientation record*: `H₃ < H₂` (cold leg demagnetizes) makes the
extracted heat positive, `HeatFlowsIntoSystem Q_c` (`cold_leg_heat_pos`), so
the helium indeed cools, `T_f < T_0` (`helium_cools_after_one_cycle`);
`rawFinalHeliumTemperature_bounds` certifies the direction numerically.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`T_h, T_c, T_0, T_f` in K; `H_i, M_i` in A/m; `V` (torus) and `V_He` (helium)
in m³; `n` in mol; `K` in K·m³/mol (from `T·M·V = n·K·H`); `μ₀` in N/A²;
`ρ_He` in kg/m³; `c` in J/(kg·K); `m_He` in kg; `Q_c, Q_h, Q_12, Q_23, Q_34,
Q_41` in J.  Consistency of the target: `(μ₀·n·K/T)·H²` is in J (T3-B1:
(N/A²)·mol·(K·m³/mol)·(A/m)²/K = N·m) and `ρ·V·c` is in
(kg/m³)·m³·J/(kg·K) = J/K, so the subtractand carries K ✓.

## Uncertainty

The source reports no `±` uncertainties; all data are nominal values, so
uncertainty propagation is *not applicable*.  Reporting precision is handled by
the explicit source-derived rounding rule `reportedHeliumTemperature`.

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no Carnot-cycle/refrigerator, paramagnet-thermodynamics or
calorimetry API: Physlib's `adiabatic_relation_log` and
`adiabatic_relation_UaUbVaVb` are ideal-gas relations,
`CanonicalEnsemble.heatCapacity` is statistical-ensemble machinery, and
`Electromagnetism.FreeSpace.μ₀` is an abstract positive constant of the
spacetime EM model carrying no numeric value — all near misses for the
problem's scalar state-function model, as recorded in the sibling files
`IPhO2026.T3B1`, `IPhO2026.T3B2`, `IPhO2026.T3C2`.  The laws are therefore
kept as faithful local governing predicates (verbatim-compatible with the
siblings).  The numerics are grounded in Mathlib's `round` (`round_eq`),
`Set.Ioo`, and `Real.pi` (for `μ₀ = 4π×10⁻⁷ N/A²`).
-/

namespace IPhO2026.T3C3

/-! ## Governing laws I — the Pm-T cycle (shared with the T3-B/T3-C files) -/

/-- Sign convention for heat (shared context of T3): a signed heat value `Q`
represents energy flowing *into* the paramagnetic torus exactly when it is
positive.  The `Q_h`, `Q_c` of T3-C are *magnitudes* of the heats exchanged
with the reservoirs; their signed into-system counterparts on the isothermal
legs are `Q_23 = Q_c` (leg `2 → 3`) and `Q_41 = −Q_h` (leg `4 → 1`).
Units: J. -/
def HeatFlowsIntoSystem (Q : ℝ) : Prop := 0 < Q

/-- **Equation of state of the paramagnetic torus** (T3-B table law, given):
at every equilibrium state, `T·M·V = n·K·H`, with `T` the temperature (K),
`M` the magnetization magnitude (A/m), `V` the (fixed) torus volume (m³), `n`
the mole count (mol), `K` the material constant (K·m³/mol) and `H` the field
magnitude (A/m).  In T3-C3 it underlies the magnetization route to the
cold-leg heat (`heat_cold_leg_magnetization_form`) and the T3-C2 closure
relation behind `hot_reservoir_temperature_sq`. -/
def EquationOfState (T M V n K H : ℝ) : Prop := T * M * V = n * K * H

/-- **Isothermal heat relation** (the T3-B1 result, explicitly licensed for
reuse by the T3-C shared context): changing the field magnitude from `H_i` to
`H_f` at the constant temperature `T` transfers the signed heat
`Q = (μ₀·n·K/(2T))·(H_i² − H_f²)` *into* the torus (into-system sign
convention; `μ₀` is the vacuum permeability, N/A²).  The torus volume has
cancelled out of this relation.  Units: J —
(N/A²)·mol·(K·m³/mol)·(A/m)²/K = N·m ✓. -/
def IsothermalHeatIntoTorus (Q μ₀ n K T H_i H_f : ℝ) : Prop :=
  Q = μ₀ * n * K / (2 * T) * (H_i ^ 2 - H_f ^ 2)

/-- **Adiabatic leg** (structure of the Carnot cycle of Fig. 3b: the curved
legs `1 → 2` and `3 → 4`): the signed heat `Q` exchanged with the environment
along an adiabatic leg vanishes, so `Q_h` and `Q_c` are the only heat
exchanges of the cycle.  Units: J. -/
def AdiabaticLeg (Q : ℝ) : Prop := Q = 0

/-- **Carnot (Clausius) heat relation** (governing law carried by the name of
the cycle: a reversible cycle whose only heat exchanges are with the hot
reservoir at `T_h` and the cold reservoir at `T_c`): the heat magnitudes
satisfy `Q_h/T_h = Q_c/T_c`.  Units: J/K on both sides. -/
def CarnotReservoirHeatRelation (Q_h T_h Q_c T_c : ℝ) : Prop :=
  Q_h / T_h = Q_c / T_c

/-! ## Governing laws II — the liquid-helium load (new to T3-C3) -/

/-- **Constant-density mass law** (T3-C3 stipulation: the helium density
`ρ` "remains constant"): the mass of the helium bath of volume `V` at density
`ρ` is `m = ρ·V`.  Units: (kg/m³)·m³ = kg. -/
def ConstantDensityMass (m ρ V : ℝ) : Prop := m = ρ * V

/-- **Constant-specific-heat calorimetry** (T3-C3 stipulation: the helium
specific heat capacity `c` "remains constant"): extracting the heat
`Q_removed` from a bath of mass `m` and specific heat `c` lowers its
temperature from `T_i` to `T_f` according to `Q_removed = m·c·(T_i − T_f)`.
This is the exact integrated form of `đQ = m·c·dT` at constant `c`.
Units: kg·(J/(kg·K))·K = J. -/
def ConstantSpecificHeatCooling (Q_removed m c T_i T_f : ℝ) : Prop :=
  Q_removed = m * c * (T_i - T_f)

/-! ## Bridge lemmas -/

/-- **Heat absorbed from the cold reservoir per cycle** (bridge 1, assembly):
identifying the cold-leg heat with the heat absorbed from the cold reservoir
(`hQc : Q_c = Q_23`, the Fig. 3b/T3-C1 label) and applying the T3-B1 relation
on leg `2 → 3` at `T_c` gives `Q_c = (μ₀·n·K/(2T_c))·(H_2² − H_3²)`.
Units: J. -/
theorem heat_absorbed_on_cold_leg {μ₀ n K T_c H_2 H_3 Q_23 Q_c : ℝ}
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_c H_2 H_3)
    (hQc : Q_c = Q_23) :
    Q_c = μ₀ * n * K / (2 * T_c) * (H_2 ^ 2 - H_3 ^ 2) := by
  rw [hQc]; exact hQ23

/-- **Cold-leg orientation** (bridge 2, branch record): on the demagnetizing
branch `0 ≤ H_3 < H_2` of Fig. 3b the T3-B1 heat on leg `2 → 3` is positive,
so the heat absorbed from the cold reservoir (the helium) flows *into* the
torus, `HeatFlowsIntoSystem Q_c`.
Proof route: unfold both predicates; the prefactor `μ₀·n·K/(2T_c)` is positive
(`div_pos`, `mul_pos`) and `H_3² < H_2²` by `pow_lt_pow_left₀`. -/
theorem cold_leg_heat_pos {μ₀ n K T_c H_2 H_3 Q_23 Q_c : ℝ}
    (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K) (hTc : 0 < T_c)
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_c H_2 H_3)
    (hQc : Q_c = Q_23) (hH3 : 0 ≤ H_3) (hH23 : H_3 < H_2) :
    HeatFlowsIntoSystem Q_c := by
  have hQ : Q_23 = μ₀ * n * K / (2 * T_c) * (H_2 ^ 2 - H_3 ^ 2) := hQ23
  have hpos1 : 0 < μ₀ * n * K / (2 * T_c) :=
    div_pos (mul_pos (mul_pos hμ₀ hn) hK) (mul_pos zero_lt_two hTc)
  have hpos2 : 0 < H_2 ^ 2 - H_3 ^ 2 := by
    have hsq : H_3 ^ 2 < H_2 ^ 2 := pow_lt_pow_left₀ hH23 hH3 two_ne_zero
    linarith
  have hmain : 0 < Q_23 := by
    rw [hQ]
    exact mul_pos hpos1 hpos2
  change 0 < Q_c
  rw [hQc]
  exact hmain

/-- **Cold-leg heat in magnetization form** (bridge 3; the T3-C2 language):
eliminating the endpoint fields of leg `2 → 3` through the equation of state
at vertices 2 and 3 (`H_i = T_c·M_i·V/(n·K)`, `i = 2, 3`) gives
`Q_c = (μ₀·V²/(2nK))·T_c·(M_2² − M_3²)`.  Equality with the field form of
`IsothermalHeatIntoTorus` exhibits the cancellation of the torus volume `V`:
the chromate density and molar mass (which fix `V`, cf. `pmTVolume`) drop out
of the per-cycle heat.  Units: J.
Proof route: solve each EOS for `H_i` (`eq_div_iff`, `n·K ≠ 0`), substitute
into `hQc` and clear fractions (`field_simp`, `ring`). -/
theorem heat_cold_leg_magnetization_form {μ₀ V n K T_c : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hTc : 0 < T_c)
    {M_2 M_3 H_2 H_3 Q_c : ℝ}
    (hEOS2 : EquationOfState T_c M_2 V n K H_2)
    (hEOS3 : EquationOfState T_c M_3 V n K H_3)
    (hQc : IsothermalHeatIntoTorus Q_c μ₀ n K T_c H_2 H_3) :
    Q_c = μ₀ * V ^ 2 / (2 * n * K) * T_c * (M_2 ^ 2 - M_3 ^ 2) := by
  have _ : 0 < μ₀ := hμ₀
  have _ : 0 < V := hV
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hTc0 : T_c ≠ 0 := ne_of_gt hTc
  have hnK : n * K ≠ 0 := mul_ne_zero hn0 hK0
  have h2Tc : (2 : ℝ) * T_c ≠ 0 := mul_ne_zero two_ne_zero hTc0
  have h2nK : (2 : ℝ) * n * K ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hn0) hK0
  have hE2 : T_c * M_2 * V = n * K * H_2 := hEOS2
  have hE3 : T_c * M_3 * V = n * K * H_3 := hEOS3
  have hH2 : H_2 = T_c * M_2 * V / (n * K) := by
    rw [eq_div_iff hnK]
    linear_combination -hE2
  have hH3 : H_3 = T_c * M_3 * V / (n * K) := by
    rw [eq_div_iff hnK]
    linear_combination -hE3
  have hQ : Q_c = μ₀ * n * K / (2 * T_c) * (H_2 ^ 2 - H_3 ^ 2) := hQc
  rw [hQ, hH2, hH3]
  field_simp

/-- **Hot-reservoir temperature determined by Carnot consistency** (bridge 4;
the T3-C2 closure relation in field language): substituting the two
isothermal-leg heats into the Clausius relation `Q_h/T_h = Q_c/T_c` and
cancelling the common factor `μ₀·n·K/2` gives
`(H_1² − H_4²)/T_h² = (H_2² − H_3²)/T_c²`, i.e. the four supplied vertex
fields fix the operating temperature of the hot reservoir,
`T_h² = T_c²·(H_1² − H_4²)/(H_2² − H_3²)`.  (At the supplied data this is
`T_h ≈ 1.424 K`; the helium balance itself does not involve `T_h`.)
Proof route: `div_eq_div_iff` on `hCarnot` (needs `T_h, T_c ≠ 0`), substitute
`hQ23`, `hQ41` via `hQc`, `hQh`, cancel `μ₀·n·K/2 ≠ 0` and
`H_2² − H_3² ≠ 0` (from `0 ≤ H_3 < H_2` via `pow_lt_pow_left₀`), and
rearrange (`field_simp`, `ring`). -/
theorem hot_reservoir_temperature_sq {μ₀ n K T_h T_c : ℝ}
    (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K) (hTh : 0 < T_h) (hTc : 0 < T_c)
    {H_1 H_2 H_3 H_4 Q_23 Q_41 Q_h Q_c : ℝ}
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_c H_2 H_3)
    (hQ41 : IsothermalHeatIntoTorus Q_41 μ₀ n K T_h H_4 H_1)
    (hQc : Q_c = Q_23) (hQh : Q_h = -Q_41)
    (hCarnot : CarnotReservoirHeatRelation Q_h T_h Q_c T_c)
    (hH3 : 0 ≤ H_3) (hH23 : H_3 < H_2) :
    T_h ^ 2 = T_c ^ 2 * (H_1 ^ 2 - H_4 ^ 2) / (H_2 ^ 2 - H_3 ^ 2) := by
  have hTh0 : T_h ≠ 0 := ne_of_gt hTh
  have hTc0 : T_c ≠ 0 := ne_of_gt hTc
  have h2Th : (2 : ℝ) * T_h ≠ 0 := mul_ne_zero two_ne_zero hTh0
  have h2Tc : (2 : ℝ) * T_c ≠ 0 := mul_ne_zero two_ne_zero hTc0
  have hTh2 : T_h ^ 2 ≠ 0 := pow_ne_zero 2 hTh0
  have hTc2 : T_c ^ 2 ≠ 0 := pow_ne_zero 2 hTc0
  have hA : μ₀ * n * K / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt hμ₀) (ne_of_gt hn)) (ne_of_gt hK))
      two_ne_zero
  have hsq : H_3 ^ 2 < H_2 ^ 2 := pow_lt_pow_left₀ hH23 hH3 two_ne_zero
  have hB : H_2 ^ 2 - H_3 ^ 2 ≠ 0 := ne_of_gt (by linarith)
  have hQ23' : Q_23 = μ₀ * n * K / (2 * T_c) * (H_2 ^ 2 - H_3 ^ 2) := hQ23
  have hQ41' : Q_41 = μ₀ * n * K / (2 * T_h) * (H_4 ^ 2 - H_1 ^ 2) := hQ41
  have hC : Q_h / T_h = Q_c / T_c := hCarnot
  rw [hQh, hQc, hQ23', hQ41'] at hC
  have e1 : μ₀ * n * K / 2 * ((H_1 ^ 2 - H_4 ^ 2) / T_h ^ 2)
      = -(μ₀ * n * K / (2 * T_h) * (H_4 ^ 2 - H_1 ^ 2)) / T_h := by
    field_simp
    ring
  have e2 : μ₀ * n * K / (2 * T_c) * (H_2 ^ 2 - H_3 ^ 2) / T_c
      = μ₀ * n * K / 2 * ((H_2 ^ 2 - H_3 ^ 2) / T_c ^ 2) := by
    field_simp
  have step0 : μ₀ * n * K / 2 * ((H_1 ^ 2 - H_4 ^ 2) / T_h ^ 2)
      = μ₀ * n * K / 2 * ((H_2 ^ 2 - H_3 ^ 2) / T_c ^ 2) := by
    rw [e1, hC, e2]
  have step : (H_1 ^ 2 - H_4 ^ 2) / T_h ^ 2 = (H_2 ^ 2 - H_3 ^ 2) / T_c ^ 2 :=
    mul_left_cancel₀ hA step0
  rw [div_eq_div_iff (pow_ne_zero 2 hTh0) (pow_ne_zero 2 hTc0)] at step
  rw [eq_div_iff hB]
  linear_combination -step

/-- **Helium temperature drop** (bridge 5, calorimetry assembly): the heat
`Q_c` extracted from the helium bath of mass `m_He = ρ_He·V_He` and constant
specific heat `c` lowers the bath temperature by
`T_0 − T_f = Q_c/(ρ_He·V_He·c)`.  Units: J / (J/K) = K.
Proof route: unfold `ConstantDensityMass` and `ConstantSpecificHeatCooling`,
divide by `ρ_He·V_He·c ≠ 0` (`field_simp`, `linear_combination`). -/
theorem helium_temperature_drop {Q_c m_He ρ_He V_He c T_0 T_f : ℝ}
    (hρ : 0 < ρ_He) (hVHe : 0 < V_He) (hc : 0 < c)
    (hm : ConstantDensityMass m_He ρ_He V_He)
    (hcal : ConstantSpecificHeatCooling Q_c m_He c T_0 T_f) :
    T_0 - T_f = Q_c / (ρ_He * V_He * c) := by
  have hne : ρ_He * V_He * c ≠ 0 := ne_of_gt (mul_pos (mul_pos hρ hVHe) hc)
  have hm' : m_He = ρ_He * V_He := hm
  have hcal' : Q_c = m_He * c * (T_0 - T_f) := hcal
  rw [hm'] at hcal'
  rw [eq_div_iff hne]
  linear_combination -hcal'

/-! ## Main target (T3-C3): the final helium temperature, symbolic form -/

/-- Raw end-to-end expression requested by T3-C3 (derived candidate): the
final helium temperature as a combination of the cycle and bath parameters,
`T_0 − (μ₀·n·K/(2T_0))·(H_2² − H_3²)/(ρ_He·V_He·c)`.  The definition merely
records the derived combination; that the actual final temperature equals it
is the content of `helium_final_temperature` — no hypothesis or premise
mentions this expression.  Units: K (J / (J/K)). -/
noncomputable def heliumFinalTemperatureExpr
    (μ₀ n K T_0 H_2 H_3 ρ_He V_He c : ℝ) : ℝ :=
  T_0 - μ₀ * n * K / (2 * T_0) * (H_2 ^ 2 - H_3 ^ 2) / (ρ_He * V_He * c)

/-- **T3-C3 main target, symbolic form.**  For the paramagnetic torus
executing the Carnot refrigeration cycle `1 → 2 → 3 → 4 → 1` of Fig. 3b —
isothermal legs `2 → 3` at `T_c` (demagnetizing) and `4 → 1` at `T_h`
(magnetizing) with the T3-B1 heat relation, adiabatic legs `1 → 2`, `3 → 4`,
the Clausius relation `Q_h/T_h = Q_c/T_c` — whose cold reservoir is the
liquid-helium bath at its current temperature (`T_c = T_0`), the helium having
constant density and specific heat: after one operating cycle the helium
temperature is

    `T_f = T_0 − (μ₀·n·K/(2T_0))·(H_2² − H_3²)/(ρ_He·V_He·c)`.

Derivation chain: `heat_absorbed_on_cold_leg` (with `hTc0`) gives the heat
extracted per cycle; `helium_temperature_drop` converts it into the bath
temperature drop; rearrangement gives `T_f`.  The hot-side hypotheses
(`hQ41`, `hQh`, `hCarnot`, the adiabats) frame the Carnot cycle and fix
`T_h` (`hot_reservoir_temperature_sq`); the per-cycle helium cooling is
exhausted by the cold-leg heat, so `H_1`, `H_4` and `T_h` do not appear in
the closed form. -/
theorem helium_final_temperature
    {μ₀ n K : ℝ} (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K)
    {T_h T_c T_0 : ℝ} (hTh : 0 < T_h) (hTc : 0 < T_c) (hTcth : T_c < T_h)
    (hT0 : 0 < T_0) (hTc0 : T_c = T_0)
    {H_1 H_2 H_3 H_4 : ℝ} (hH23 : H_3 < H_2) (hH41 : H_4 < H_1)
    {Q_12 Q_23 Q_34 Q_41 Q_h Q_c : ℝ}
    (hAd12 : AdiabaticLeg Q_12) (hAd34 : AdiabaticLeg Q_34)
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_c H_2 H_3)
    (hQ41 : IsothermalHeatIntoTorus Q_41 μ₀ n K T_h H_4 H_1)
    (hQc : Q_c = Q_23) (hQh : Q_h = -Q_41)
    (hCarnot : CarnotReservoirHeatRelation Q_h T_h Q_c T_c)
    {ρ_He V_He c m_He T_f : ℝ}
    (hρ : 0 < ρ_He) (hVHe : 0 < V_He) (hc : 0 < c)
    (hm : ConstantDensityMass m_He ρ_He V_He)
    (hcal : ConstantSpecificHeatCooling Q_c m_He c T_0 T_f) :
    T_f = T_0 - μ₀ * n * K / (2 * T_0) * (H_2 ^ 2 - H_3 ^ 2) / (ρ_He * V_He * c) := by
  -- The hot-side and structural hypotheses frame the Carnot cycle (they fix
  -- `T_h`, see `hot_reservoir_temperature_sq`); the per-cycle helium balance
  -- below is exhausted by the cold-leg heat, so the algebra does not use them.
  have _ : 0 < μ₀ := hμ₀
  have _ : 0 < n := hn
  have _ : 0 < K := hK
  have _ : 0 < T_h := hTh
  have _ : 0 < T_c := hTc
  have _ : T_c < T_h := hTcth
  have _ : 0 < T_0 := hT0
  have _ : H_3 < H_2 := hH23
  have _ : H_4 < H_1 := hH41
  have _ : Q_12 = 0 := hAd12
  have _ : Q_34 = 0 := hAd34
  have _ : IsothermalHeatIntoTorus Q_41 μ₀ n K T_h H_4 H_1 := hQ41
  have _ : Q_h = -Q_41 := hQh
  have _ : CarnotReservoirHeatRelation Q_h T_h Q_c T_c := hCarnot
  -- Heat extracted from the helium per cycle (bridge 1 at `T_c = T_0`).
  have hQc' : Q_c = μ₀ * n * K / (2 * T_c) * (H_2 ^ 2 - H_3 ^ 2) :=
    heat_absorbed_on_cold_leg hQ23 hQc
  -- Calorimetry converts the extracted heat into the bath temperature drop.
  have hdrop : T_0 - T_f = Q_c / (ρ_He * V_He * c) :=
    helium_temperature_drop hρ hVHe hc hm hcal
  rw [hQc', hTc0] at hdrop
  linarith

/-- Packaged form of the main target (naming expansion): the final helium
temperature equals the raw requested expression `heliumFinalTemperatureExpr`.
Proof route: `helium_final_temperature`; `heliumFinalTemperatureExpr` unfolds
definitionally to the closed form. -/
theorem helium_final_temperature_eq_expr
    {μ₀ n K : ℝ} (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K)
    {T_h T_c T_0 : ℝ} (hTh : 0 < T_h) (hTc : 0 < T_c) (hTcth : T_c < T_h)
    (hT0 : 0 < T_0) (hTc0 : T_c = T_0)
    {H_1 H_2 H_3 H_4 : ℝ} (hH23 : H_3 < H_2) (hH41 : H_4 < H_1)
    {Q_12 Q_23 Q_34 Q_41 Q_h Q_c : ℝ}
    (hAd12 : AdiabaticLeg Q_12) (hAd34 : AdiabaticLeg Q_34)
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_c H_2 H_3)
    (hQ41 : IsothermalHeatIntoTorus Q_41 μ₀ n K T_h H_4 H_1)
    (hQc : Q_c = Q_23) (hQh : Q_h = -Q_41)
    (hCarnot : CarnotReservoirHeatRelation Q_h T_h Q_c T_c)
    {ρ_He V_He c m_He T_f : ℝ}
    (hρ : 0 < ρ_He) (hVHe : 0 < V_He) (hc : 0 < c)
    (hm : ConstantDensityMass m_He ρ_He V_He)
    (hcal : ConstantSpecificHeatCooling Q_c m_He c T_0 T_f) :
    T_f = heliumFinalTemperatureExpr μ₀ n K T_0 H_2 H_3 ρ_He V_He c := by
  unfold heliumFinalTemperatureExpr
  exact helium_final_temperature hμ₀ hn hK hTh hTc hTcth hT0 hTc0 hH23 hH41
    hAd12 hAd34 hQ23 hQ41 hQc hQh hCarnot hρ hVHe hc hm hcal

/-- **Cooling direction** (branch record): one operating cycle of the
refrigerator genuinely cools the helium, `T_f < T_0` — the extracted heat is
positive (`cold_leg_heat_pos` supplies `0 < Q_c`) and the calorimetry law
converts it into a temperature decrease.
Proof route: `helium_temperature_drop`; the right-hand side is positive by
`div_pos`/`mul_pos`; `sub_pos`. -/
theorem helium_cools_after_one_cycle {T_0 Q_c m_He ρ_He V_He c T_f : ℝ}
    (hT0 : 0 < T_0) (hQc : 0 < Q_c)
    (hρ : 0 < ρ_He) (hVHe : 0 < V_He) (hc : 0 < c)
    (hm : ConstantDensityMass m_He ρ_He V_He)
    (hcal : ConstantSpecificHeatCooling Q_c m_He c T_0 T_f) :
    T_f < T_0 := by
  have _ : 0 < T_0 := hT0
  have hdrop : T_0 - T_f = Q_c / (ρ_He * V_He * c) :=
    helium_temperature_drop hρ hVHe hc hm hcal
  have hpos : (0:ℝ) < Q_c / (ρ_He * V_He * c) :=
    div_pos hQc (mul_pos (mul_pos hρ hVHe) hc)
  linarith

/-! ## Supplied data (T3-C3 statement, page 14) and numerical evaluation -/

/-- Vacuum permeability, the constants-table value used throughout T3
(`dW = μ₀·V·H·dM`, hence the T3-B1 heat, are proportional to it):
`μ₀ = 4π×10⁻⁷ N/A²`. -/
noncomputable def vacuumPermeabilitySI : ℝ := 4 * Real.pi * 1e-7

/-- Supplied helium volume: `1.00 L = 1.00×10⁻³ m³` (exact litre conversion;
page 14). -/
noncomputable def givenHeliumVolume : ℝ := 1.00e-3

/-- Supplied initial helium temperature: `T_0 = 1.00 K` (page 14).  The bath
is the cold reservoir, so this is the `T_c` of the first operating cycle. -/
noncomputable def givenInitialHeliumTemperature : ℝ := 1.00

/-- Supplied Pm-T amount of substance: `n = 2.0 mol` (page 14). -/
noncomputable def givenPmTMoles : ℝ := 2.0

/-- Supplied potassium-chromate material constant: `K = 1.87×10⁻⁶ K·m³/mol`
(page 14) — the `K` of the equation of state `T·M·V = n·K·H`. -/
noncomputable def givenMaterialConstantK : ℝ := 1.87e-6

/-- Supplied potassium-chromate density: `2730 kg/m³` (page 14). -/
noncomputable def givenChromateDensity : ℝ := 2730

/-- Supplied potassium-chromate molar mass: `0.19 kg/mol` (page 14). -/
noncomputable def givenChromateMolarMass : ℝ := 0.19

/-- Supplied vertex-1 field magnitude: `H₁ = 411624 A/m` (page 14). -/
noncomputable def givenField1 : ℝ := 411624

/-- Supplied vertex-2 field magnitude: `H₂ = 311306 A/m` (page 14). -/
noncomputable def givenField2 : ℝ := 311306

/-- Supplied vertex-3 field magnitude: `H₃ = 204618 A/m` (page 14). -/
noncomputable def givenField3 : ℝ := 204618

/-- Supplied vertex-4 field magnitude: `H₄ = 240446 A/m` (page 14). -/
noncomputable def givenField4 : ℝ := 240446

/-- Supplied helium specific heat capacity, stipulated constant:
`c = 100 J/(kg·K)` (page 14). -/
noncomputable def givenHeliumSpecificHeat : ℝ := 100

/-- Supplied helium density, stipulated constant: `ρ = 130 kg/m³` (page 14). -/
noncomputable def givenHeliumDensity : ℝ := 130

/-- The torus volume implied by the chromate data,
`V = n·(molar mass)/(density) ≈ 1.392×10⁻⁴ m³`.  Recorded as part of the
setup: it cancels out of the T3-B1 isothermal heat (see
`heat_cold_leg_magnetization_form`), so it does not enter the final helium
temperature.  Units: mol·(kg/mol)/(kg/m³) = m³. -/
noncomputable def pmTVolume : ℝ :=
  givenPmTMoles * givenChromateMolarMass / givenChromateDensity

/-- The supplied vertex fields realize the cold-leg (demagnetizing) branch of
Fig. 3b: `H₃ < H₂` (`204618 < 311306`). -/
theorem givenField3_lt_givenField2 : givenField3 < givenField2 := by
  norm_num [givenField3, givenField2]

/-- The supplied vertex fields realize the hot-leg (magnetizing) branch of
Fig. 3b: `H₄ < H₁` (`240446 < 411624`). -/
theorem givenField4_lt_givenField1 : givenField4 < givenField1 := by
  norm_num [givenField4, givenField1]

/-- **Raw end-to-end quantity of T3-C3**: the final helium temperature (K)
obtained from the closed form of `helium_final_temperature` evaluated at the
supplied data,
`1.00 − (μ₀·2.0·1.87×10⁻⁶/(2·1.00))·(311306² − 204618²)/(130·1.00×10⁻³·100)`
with `μ₀ = 4π×10⁻⁷`.  Its value is not pinned by this definition beyond the
data; that the physical final temperature equals it is the content of
`final_temperature_at_data`.  Units: K. -/
noncomputable def rawFinalHeliumTemperature : ℝ :=
  givenInitialHeliumTemperature -
    vacuumPermeabilitySI * givenPmTMoles * givenMaterialConstantK /
      (2 * givenInitialHeliumTemperature) * (givenField2 ^ 2 - givenField3 ^ 2) /
        (givenHeliumDensity * givenHeliumVolume * givenHeliumSpecificHeat)

/-- **Instantiation bridge** (`helium_final_temperature` specialized to the
supplied data, with the reservoir identification `T_c = T_0` applied): any
final helium temperature compatible with the T3-B1 cold-leg heat law and the
helium calorimetry law at the supplied data equals the raw quantity
`rawFinalHeliumTemperature`.
Proof route: unfold the data definitions and the three law predicates; solve
for `T_f` (`field_simp` with the positivity of the data discharged by
`norm_num`, then `linear_combination`). -/
theorem final_temperature_at_data {Q_c m_He T_f : ℝ}
    (hQc : IsothermalHeatIntoTorus Q_c vacuumPermeabilitySI givenPmTMoles
      givenMaterialConstantK givenInitialHeliumTemperature givenField2 givenField3)
    (hm : ConstantDensityMass m_He givenHeliumDensity givenHeliumVolume)
    (hcal : ConstantSpecificHeatCooling Q_c m_He givenHeliumSpecificHeat
      givenInitialHeliumTemperature T_f) :
    T_f = rawFinalHeliumTemperature := by
  have hρ : (0:ℝ) < givenHeliumDensity := by norm_num [givenHeliumDensity]
  have hV : (0:ℝ) < givenHeliumVolume := by norm_num [givenHeliumVolume]
  have hc : (0:ℝ) < givenHeliumSpecificHeat := by norm_num [givenHeliumSpecificHeat]
  have hdrop : givenInitialHeliumTemperature - T_f
      = Q_c / (givenHeliumDensity * givenHeliumVolume * givenHeliumSpecificHeat) :=
    helium_temperature_drop hρ hV hc hm hcal
  have hQ : Q_c = vacuumPermeabilitySI * givenPmTMoles * givenMaterialConstantK
      / (2 * givenInitialHeliumTemperature) * (givenField2 ^ 2 - givenField3 ^ 2) := hQc
  rw [hQ] at hdrop
  unfold rawFinalHeliumTemperature
  linarith

/-- Certified numerical bounds on the raw final temperature:
`0.989 K < T_f < 0.991 K` (the raw value is `≈ 0.99005 K`).  Certifiable from
`Real.pi_gt_31415` / `Real.pi_lt_31416` and `norm_num`. -/
theorem rawFinalHeliumTemperature_bounds :
    rawFinalHeliumTemperature ∈ Set.Ioo (0.989 : ℝ) (0.991 : ℝ) := by
  have hπlo : (3.1415:ℝ) < Real.pi := Real.pi_gt_d4
  have hπhi : Real.pi < 3.1416 := Real.pi_lt_d4
  unfold rawFinalHeliumTemperature vacuumPermeabilitySI givenInitialHeliumTemperature
    givenPmTMoles givenMaterialConstantK givenField2 givenField3 givenHeliumDensity
    givenHeliumVolume givenHeliumSpecificHeat
  rw [Set.mem_Ioo]
  constructor <;> nlinarith [hπlo, hπhi]

/-- **Source-derived rounding rule.**  The source reports the temperature data
to the nearest `0.01 K` ("liquid helium initially at 1.00 K") and the
remaining data to two or three significant figures; the reported final
temperature therefore rounds the raw quantity to the nearest `0.01 K` (at
this magnitude the two-significant-figure report coincides with the 0.01 K
grid). -/
noncomputable def reportedHeliumTemperature : ℝ :=
  (round (rawFinalHeliumTemperature * 1e2) : ℝ) * 1e-2

/-- The mantissa of the reported value: `T_f·10² ≈ 99.005` rounds to `99`.
Proof route: `round_eq` (`Int.le_floor`, `Int.floor_lt`) with the bounds of
`rawFinalHeliumTemperature_bounds` sharpened to `0.985 ≤ T_f < 0.995`. -/
theorem reportedHeliumTemperature_mantissa :
    round (rawFinalHeliumTemperature * 1e2) = 99 := by
  obtain ⟨hlo, hhi⟩ := rawFinalHeliumTemperature_bounds
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> push_cast <;> nlinarith [hlo, hhi]

/-- **T3-C3 main result** (blueprint `thm:physics:ipho_2026_t3_c3:target`):
after one operating cycle of the potassium-chromate Carnot refrigerator, the
liquid helium has cooled from `1.00 K` to

    `T_f = 0.99 K`

(to the nearest 0.01 K; raw value `≈ 0.99005 K`).
Proof route: `rw [reportedHeliumTemperature, reportedHeliumTemperature_mantissa]`;
`norm_num`. -/
theorem reportedHeliumTemperature_value :
    reportedHeliumTemperature = 0.99 := by
  unfold reportedHeliumTemperature
  rw [reportedHeliumTemperature_mantissa]
  norm_num

end IPhO2026.T3C3
