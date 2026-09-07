import Mathlib

/-!
# IPhO 2026 · Theory problem T3-C2 — "Carnot refrigerator of the Pm-T":
the magnetization relation between the vertices of the cycle

Autoformalization of IPhO 2026 T3-C2 (source:
`reports/ipho_2026/problem_ipho_2026_t3_c2.source.json`; problem page
`ipho_2026_source/image/T3_page-3.png`: Figure 3b — the `H`-vs-`T` diagram of
the cycle — together with the T3-C preamble and the T3-C1/T3-C2 statements).

## Shared problem context (page 13, T3-C preamble and Figure 3b)

The paramagnetic torus (Pm-T) of parts T3-A/B performs the Carnot
refrigeration cycle `1 → 2 → 3 → 4 → 1` drawn in the `H`-versus-`T` plane
(Fig. 3b):

* vertices 1 (top right) and 4 (middle right) lie on the right-hand dashed
  vertical line — the higher temperature `T_h` (hot reservoir); vertices 2
  (middle left) and 3 (bottom left) lie on the left-hand dashed vertical
  line — the lower temperature `T_c` (cold reservoir);
* the legs `2 → 3` (field magnitude decreases) and `4 → 1` (field magnitude
  increases) are vertical, hence *isothermal*; the legs `1 → 2` and `3 → 4`
  are the curved *adiabatic* legs of the Carnot cycle;
* `Q_h` is the *absolute value* of the heat transferred to the hot reservoir
  and `Q_c` the *absolute value* of the heat absorbed from the cold reservoir;
* the equation of state `T·M·V = n·K·H` holds at every equilibrium state
  (T3-B table law), and "the isothermal heat relation from part B may be
  reused" (shared context).

**Subquestion T3-C2 (page 13, 1.5 pts).**  "Let `M_1`, `M_2`, `M_3`, and
`M_4` be the magnitudes of `M⃗` at the vertices of this cycle.  Write `M_1` in
terms of `M_2`, `M_3`, and `M_4`."

## Previous-part dependencies (policy: derive_inline_from_problem_only_material)

* **T3-B1** (isothermal heat relation): at constant temperature `T`, changing
  the field magnitude from `H_i` to `H_f` transfers the signed heat
  `Q = (μ₀·n·K/(2T))·(H_i² − H_f²)` into the torus (into-system sign
  convention).  Reused here as the governing predicate
  `IsothermalHeatIntoTorus` — explicitly licensed by the shared context ("the
  isothermal heat relation from part B may be reused"); no sibling file is
  imported.
* **T3-C1** (labels on Fig. 3b): the figure fixes `T_h` on the right dashed
  line (vertices 1, 4) and `T_c` on the left dashed line (vertices 2, 3), and
  the isothermal legs are `2 → 3` and `4 → 1`.  Since the field *decreases*
  along `2 → 3` and *increases* along `4 → 1`, the T3-B1 sign of the
  isothermal heat identifies leg `2 → 3` as heat-absorbing (from the cold
  reservoir: `Q_c = Q_23`, heat into the torus) and leg `4 → 1` as
  heat-rejecting (to the hot reservoir: `Q_h = −Q_41`).  These
  identifications are recorded as the hypotheses `hQc`, `hQh`, and the
  derived positivity statements `cold_leg_absorbs_heat` /
  `hot_leg_rejects_heat`.

## Governing laws and model assumptions

1. `EquationOfState` at each vertex (T3-B table law):
   `T_i·M_i·V = n·K·H_i` for `i = 1, …, 4`.
2. `IsothermalHeatIntoTorus` on the two isothermal legs (T3-B1 result,
   reused as licensed).
3. `AdiabaticLeg`: no heat is exchanged on the curved legs `1 → 2` and
   `3 → 4` (the adiabats of the Carnot cycle), so `Q_h` and `Q_c` are the
   only heat exchanges of the cycle.
4. `CarnotReservoirHeatRelation`: for the reversible Carnot cycle running
   between the two reservoirs, `Q_h/T_h = Q_c/T_c` — the Clausius equality
   for a reversible two-isotherm cycle (the adiabatic legs contribute no
   heat); this is the content of the cycle being a *Carnot* cycle.
5. Physical ranges and figure readouts: `μ₀, V, n, K, T_h, T_c > 0`,
   `T_c < T_h`, field orderings `H_3 < H_2` (demagnetizing cold leg) and
   `H_4 < H_1` (magnetizing hot leg) read off Fig. 3b, and the vertex
   temperature identifications `T_1 = T_4 = T_h`, `T_2 = T_3 = T_c`.
   Magnetizations `M_i` are magnitudes (`0 ≤ M_i`; only `0 ≤ M_1` is needed
   for the square-root form).

## Derivation (answer-blind, from the laws above only)

* Cold isotherm `2 → 3` at `T_c`: the T3-B1 relation gives
  `Q_c = Q_23 = (μ₀·n·K/(2T_c))·(H_2² − H_3²)`, and the equation of state at
  vertices 2, 3 gives `H_i = T_c·M_i·V/(n·K)`, hence
  `Q_c = (μ₀·V²·T_c/(2nK))·(M_2² − M_3²)` (`heat_cold_leg_magnetization_form`).
* Hot isotherm `4 → 1` at `T_h`: similarly
  `Q_h = −Q_41 = (μ₀·n·K/(2T_h))·(H_1² − H_4²)
  = (μ₀·V²·T_h/(2nK))·(M_1² − M_4²)` (`heat_hot_leg_magnetization_form`).
* Carnot (Clausius) relation `Q_h·T_c = Q_c·T_h`
  (`CarnotReservoirHeatRelation.cross_mul`): the common factor
  `μ₀·V²/(2nK)` and the reservoir temperatures cancel
  (`magnetization_balance_of_heats`), leaving `M_1² − M_4² = M_2² − M_3²`.

## Current target (conclusion side only)

    `M_1² = M_2² − M_3² + M_4²`   (`magnetization_vertex_one_sq`),
equivalently, since `M_1 ≥ 0` is a magnitude,
    `M_1 = √(M_2² − M_3² + M_4²)` (`magnetization_vertex_one`).

The raw requested combination is recorded as `vertexOneMagnetizationExpr`;
no hypothesis, premise structure or local definition mentions it, and the
squared relation itself appears only on the conclusion side.

*Branch/orientation record*: the refrigerator orientation is fixed by the
identification hypotheses (`Q_c = Q_23`: heat *into* the torus on the
demagnetizing cold leg; `Q_h = −Q_41`: heat *out of* the torus on the
magnetizing hot leg) and the field orderings of Fig. 3b; the bridge lemmas
`cold_leg_absorbs_heat` and `hot_leg_rejects_heat` derive that the declared
heat magnitudes are indeed positive on these branches.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`T_h, T_c, T_i` in K; `H_i, M_i` in A/m; `V` in m³; `n` in mol; the material
constant `K` in K·m³/mol (from `T·M·V = n·K·H`); `μ₀` in N/A² (H/m);
`Q_h, Q_c, Q_12, Q_23, Q_34, Q_41` in J.  Consistency of the bridge formula:
`μ₀·V²·T·M²/(n·K)` has units
(N/A²)·m⁶·K·(A/m)²/(mol·K·m³/mol) = N·m = J ✓.  The target relation is
homogeneous of degree 2 in the magnetizations, (A/m)² ✓.

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no Carnot-cycle / Clausius-equality / paramagnet-
thermodynamics API: Physlib's thermodynamics offers the *ideal-gas* adiabatic
relations `adiabatic_relation_log`, `adiabatic_relation_UaUbVaVb` and the
statistical-ensemble `CanonicalEnsemble.thermodynamicEntropy` /
`CanonicalEnsemble.heatCapacity`, and its electromagnetism is the spacetime
vector-field machinery (`Electromagnetism.MagneticField`,
`Electromagnetism.ElectromagneticPotential.magneticField`) — all near misses
for the problem's scalar state-function model (`T·M·V = n·K·H`, scalar heats).
The laws are therefore kept as faithful local governing predicates, mirroring
the sibling files `IPhO2026.T3B1` and `IPhO2026.T3B2`.  The square-root
packaging is grounded in Mathlib's `Real.sqrt`, `Real.sqrt_sq`; the ratio
form of the Carnot relation is cross-multiplied with `div_eq_div_iff`.
-/

namespace IPhO2026.T3C2

/-! ## Sign convention, state law and process laws -/

/-- Sign convention for heat (shared context of T3): a signed heat value `Q`
represents energy flowing *into* the paramagnetic torus exactly when it is
positive.  The `Q_h`, `Q_c` of T3-C are *magnitudes* (absolute values) of the
heats exchanged with the reservoirs; their signed into-system counterparts on
the isothermal legs are `Q_23 = Q_c` (leg `2 → 3`) and `Q_41 = −Q_h`
(leg `4 → 1`).  Units: J. -/
def HeatFlowsIntoSystem (Q : ℝ) : Prop := 0 < Q

/-- **Equation of state of the paramagnetic torus** (T3-B table law, given):
at every equilibrium state, `T·M·V = n·K·H`, with `T` the temperature (K),
`M` the magnetization magnitude (A/m), `V` the (fixed) torus volume (m³), `n`
the mole count (mol), `K` the material constant (K·m³/mol) and `H` the field
magnitude (A/m).  In T3-C2 the law is imposed at the four vertices of the
cycle. -/
def EquationOfState (T M V n K H : ℝ) : Prop := T * M * V = n * K * H

/-- **Isothermal heat relation** (the T3-B1 result, explicitly licensed for
reuse by the T3-C shared context: "the isothermal heat relation from part B
may be reused"): changing the field magnitude from `H_i` to `H_f` at the
constant temperature `T` transfers the signed heat
`Q = (μ₀·n·K/(2T))·(H_i² − H_f²)` *into* the torus (into-system sign
convention; `μ₀` is the vacuum permeability, N/A²).  Units: J —
(N/A²)·mol·(K·m³/mol)·(A/m)²/K = N·m ✓. -/
def IsothermalHeatIntoTorus (Q μ₀ n K T H_i H_f : ℝ) : Prop :=
  Q = μ₀ * n * K / (2 * T) * (H_i ^ 2 - H_f ^ 2)

/-- **Adiabatic leg** (structure of the Carnot cycle of Fig. 3b: the curved
legs `1 → 2` and `3 → 4`): the signed heat `Q` exchanged with the
environment along an adiabatic leg vanishes.  With the two isothermal legs
this makes `Q_h` and `Q_c` the only heat exchanges of the cycle — the
hypothesis under which the Clausius relation `CarnotReservoirHeatRelation`
applies to these two heats.  Units: J. -/
def AdiabaticLeg (Q : ℝ) : Prop := Q = 0

/-- **Carnot (Clausius) heat relation** (governing law carried by the name of
the cycle: the cycle of Fig. 3b is a *Carnot* refrigeration cycle, i.e. a
reversible cycle whose only heat exchanges are with the hot reservoir at
`T_h` and the cold reservoir at `T_c`): the heat magnitudes satisfy
`Q_h/T_h = Q_c/T_c`.  For a reversible cycle the entropy balance
`∮ đQ/T = 0` over the two isothermal legs (the adiabatic legs contribute no
heat) is exactly this relation.  Units: J/K on both sides. -/
def CarnotReservoirHeatRelation (Q_h T_h Q_c T_c : ℝ) : Prop :=
  Q_h / T_h = Q_c / T_c

/-! ## Bridge lemmas -/

/-- Cross-multiplied form of the Carnot relation (reservoir temperatures are
positive): `Q_h·T_c = Q_c·T_h`.
Proof route: unfold the relation and rewrite with `div_eq_div_iff`. -/
theorem CarnotReservoirHeatRelation.cross_mul {Q_h T_h Q_c T_c : ℝ}
    (hTh : 0 < T_h) (hTc : 0 < T_c)
    (h : CarnotReservoirHeatRelation Q_h T_h Q_c T_c) :
    Q_h * T_c = Q_c * T_h := by
  have h' : Q_h / T_h = Q_c / T_c := h
  rw [div_eq_div_iff (ne_of_gt hTh) (ne_of_gt hTc)] at h'
  exact h'

/-- **Heat absorbed on the cold isotherm, magnetization form** (bridge 1):
the T3-B1 isothermal heat for leg `2 → 3` at the cold temperature `T_c`,
with the endpoint field values eliminated through the equation of state at
vertices 2 and 3 (`H_i = T_c·M_i·V/(n·K)` for `i = 2, 3`), is
`Q_23 = (μ₀·V²/(2nK))·T_c·(M_2² − M_3²)`.  Units: J.
Proof route: solve each EOS for `H_i` (`eq_div_iff`, `n·K ≠ 0`), substitute
into the T3-B1 relation and clear fractions (`field_simp`, `ring`). -/
theorem heat_cold_leg_magnetization_form {μ₀ V n K T_c : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hTc : 0 < T_c)
    {M_2 M_3 H_2 H_3 Q_23 : ℝ}
    (hEOS2 : EquationOfState T_c M_2 V n K H_2)
    (hEOS3 : EquationOfState T_c M_3 V n K H_3)
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_c H_2 H_3) :
    Q_23 = μ₀ * V ^ 2 / (2 * n * K) * T_c * (M_2 ^ 2 - M_3 ^ 2) := by
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
  have hQ : Q_23 = μ₀ * n * K / (2 * T_c) * (H_2 ^ 2 - H_3 ^ 2) := hQ23
  rw [hQ, hH2, hH3]
  field_simp

/-- **Heat rejected on the hot isotherm, magnetization form** (bridge 2):
the T3-B1 isothermal heat for leg `4 → 1` at the hot temperature `T_h`,
with the endpoint field values eliminated through the equation of state at
vertices 4 and 1 (`H_i = T_h·M_i·V/(n·K)` for `i = 4, 1`), is
`Q_41 = (μ₀·V²/(2nK))·T_h·(M_4² − M_1²)` (negative on the physical branch:
heat leaves the torus).  Units: J.
Proof route: as `heat_cold_leg_magnetization_form`. -/
theorem heat_hot_leg_magnetization_form {μ₀ V n K T_h : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hTh : 0 < T_h)
    {M_1 M_4 H_1 H_4 Q_41 : ℝ}
    (hEOS4 : EquationOfState T_h M_4 V n K H_4)
    (hEOS1 : EquationOfState T_h M_1 V n K H_1)
    (hQ41 : IsothermalHeatIntoTorus Q_41 μ₀ n K T_h H_4 H_1) :
    Q_41 = μ₀ * V ^ 2 / (2 * n * K) * T_h * (M_4 ^ 2 - M_1 ^ 2) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hTh0 : T_h ≠ 0 := ne_of_gt hTh
  have hnK : n * K ≠ 0 := mul_ne_zero hn0 hK0
  have h2Th : (2 : ℝ) * T_h ≠ 0 := mul_ne_zero two_ne_zero hTh0
  have h2nK : (2 : ℝ) * n * K ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hn0) hK0
  have hE4 : T_h * M_4 * V = n * K * H_4 := hEOS4
  have hE1 : T_h * M_1 * V = n * K * H_1 := hEOS1
  have hH4 : H_4 = T_h * M_4 * V / (n * K) := by
    rw [eq_div_iff hnK]
    linear_combination -hE4
  have hH1 : H_1 = T_h * M_1 * V / (n * K) := by
    rw [eq_div_iff hnK]
    linear_combination -hE1
  have hQ : Q_41 = μ₀ * n * K / (2 * T_h) * (H_4 ^ 2 - H_1 ^ 2) := hQ41
  rw [hQ, hH4, hH1]
  field_simp

/-- **Vertex-magnetization balance from the Carnot relation** (bridge 3, pure
algebra): if the heats exchanged with the reservoirs factor as
`Q_c = A·T_c·(M_2² − M_3²)` and `Q_h = A·T_h·(M_1² − M_4²)` with a common
nonzero prefactor `A` (instantiated by `μ₀·V²/(2nK)` in the main theorem),
then the Carnot relation `Q_h/T_h = Q_c/T_c` forces
`M_1² = M_2² − M_3² + M_4²`.
Proof route: `CarnotReservoirHeatRelation.cross_mul`, substitute the
factorized heats, cancel `A·T_h·T_c ≠ 0`, and rearrange
(`mul_eq_mul_left_iff`-style cancellation, `linear_combination`). -/
theorem magnetization_balance_of_heats {A T_h T_c M_1 M_2 M_3 M_4 Q_h Q_c : ℝ}
    (hA : A ≠ 0) (hTh : T_h ≠ 0) (hTc : T_c ≠ 0)
    (hQh : Q_h = A * T_h * (M_1 ^ 2 - M_4 ^ 2))
    (hQc : Q_c = A * T_c * (M_2 ^ 2 - M_3 ^ 2))
    (hCarnot : CarnotReservoirHeatRelation Q_h T_h Q_c T_c) :
    M_1 ^ 2 = M_2 ^ 2 - M_3 ^ 2 + M_4 ^ 2 := by
  have hC : Q_h / T_h = Q_c / T_c := hCarnot
  rw [div_eq_div_iff hTh hTc] at hC
  rw [hQh, hQc] at hC
  -- hC : A * T_h * (M_1 ^ 2 - M_4 ^ 2) * T_c = A * T_c * (M_2 ^ 2 - M_3 ^ 2) * T_h
  have h2 : M_1 ^ 2 - M_4 ^ 2 = M_2 ^ 2 - M_3 ^ 2 := by
    have h3 : A * T_h * T_c * (M_1 ^ 2 - M_4 ^ 2)
        = A * T_h * T_c * (M_2 ^ 2 - M_3 ^ 2) := by
      linear_combination hC
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hA hTh) hTc) h3
  linear_combination h2

/-- **Cold-leg orientation** (bridge 4, sign record): on the demagnetizing
branch `0 ≤ H_3 < H_2` of Fig. 3b the T3-B1 isothermal heat on leg `2 → 3` is
positive, so the heat magnitude absorbed from the cold reservoir is positive
and flows *into* the torus, `HeatFlowsIntoSystem Q_c`.
Proof route: `hQc` reduces to `0 < Q_23`; unfold `IsothermalHeatIntoTorus`;
the prefactor `μ₀·n·K/(2T_c)` is positive (`div_pos`, `mul_pos`) and
`H_3² < H_2²` by `pow_lt_pow_left₀`, so the product is positive. -/
theorem cold_leg_absorbs_heat {μ₀ n K T_c H_2 H_3 Q_23 Q_c : ℝ}
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

/-- **Hot-leg orientation** (bridge 5, sign record): on the magnetizing
branch `0 ≤ H_4 < H_1` of Fig. 3b the T3-B1 isothermal heat on leg `4 → 1` is
negative (heat leaves the torus), so the heat magnitude delivered to the hot
reservoir is positive, `0 < Q_h`.
Proof route: `hQh` reduces to `0 < −Q_41`; unfold `IsothermalHeatIntoTorus`;
the prefactor is positive and `H_4² − H_1² < 0` by `pow_lt_pow_left₀`. -/
theorem hot_leg_rejects_heat {μ₀ n K T_h H_1 H_4 Q_41 Q_h : ℝ}
    (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K) (hTh : 0 < T_h)
    (hQ41 : IsothermalHeatIntoTorus Q_41 μ₀ n K T_h H_4 H_1)
    (hQh : Q_h = -Q_41) (hH4 : 0 ≤ H_4) (hH41 : H_4 < H_1) :
    0 < Q_h := by
  have hQ : Q_41 = μ₀ * n * K / (2 * T_h) * (H_4 ^ 2 - H_1 ^ 2) := hQ41
  have hpos1 : 0 < μ₀ * n * K / (2 * T_h) :=
    div_pos (mul_pos (mul_pos hμ₀ hn) hK) (mul_pos zero_lt_two hTh)
  have hneg : H_4 ^ 2 - H_1 ^ 2 < 0 := by
    have hsq : H_4 ^ 2 < H_1 ^ 2 := pow_lt_pow_left₀ hH41 hH4 two_ne_zero
    linarith
  have hmain : Q_41 < 0 := by
    rw [hQ]
    exact mul_neg_of_pos_of_neg hpos1 hneg
  rw [hQh]
  linarith

/-! ## Raw requested expression and main targets (T3-C2) -/

/-- Raw end-to-end expression requested by T3-C2 (derived candidate):
`√(M_2² − M_3² + M_4²)`, built from the vertex magnetizations `M_2, M_3, M_4`
only.  The definition merely records the derived combination; that the actual
vertex-1 magnetization equals it is the content of `magnetization_vertex_one`
— nothing in the model assumptions mentions this expression.  Units: A/m
(the square root of a homogeneous squared-magnetization combination). -/
noncomputable def vertexOneMagnetizationExpr (M_2 M_3 M_4 : ℝ) : ℝ :=
  Real.sqrt (M_2 ^ 2 - M_3 ^ 2 + M_4 ^ 2)

/-- **T3-C2 main target, squared form.**  For the paramagnetic torus
executing the Carnot refrigeration cycle `1 → 2 → 3 → 4 → 1` of Fig. 3b —
equation of state at the four vertices; the T3-B1 isothermal heat relation on
the vertical legs `2 → 3` (at `T_c`) and `4 → 1` (at `T_h`); no heat
exchanged on the adiabatic legs `1 → 2`, `3 → 4`; the Clausius relation
`Q_h/T_h = Q_c/T_c` between the heat magnitudes delivered to the hot
reservoir and absorbed from the cold one — the vertex magnetizations satisfy

    `M_1² = M_2² − M_3² + M_4²`.

Derivation chain: `heat_cold_leg_magnetization_form` and
`heat_hot_leg_magnetization_form` express the two isothermal-leg heats
through the vertex magnetizations (via the vertex EOS and the temperature
identifications `hT1`–`hT4`); with `Q_c = Q_23`, `Q_h = −Q_41` and the common
prefactor `μ₀·V²/(2nK) ≠ 0`, `magnetization_balance_of_heats` turns the
Carnot relation into the squared-magnetization balance. -/
theorem magnetization_vertex_one_sq
    {μ₀ V n K T_h T_c : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K)
    (hTh : 0 < T_h) (hTc : 0 < T_c) (hTcth : T_c < T_h)
    {T_1 T_2 T_3 T_4 H_1 H_2 H_3 H_4 M_1 M_2 M_3 M_4 : ℝ}
    (hT1 : T_1 = T_h) (hT2 : T_2 = T_c) (hT3 : T_3 = T_c) (hT4 : T_4 = T_h)
    (hEOS1 : EquationOfState T_1 M_1 V n K H_1)
    (hEOS2 : EquationOfState T_2 M_2 V n K H_2)
    (hEOS3 : EquationOfState T_3 M_3 V n K H_3)
    (hEOS4 : EquationOfState T_4 M_4 V n K H_4)
    {Q_12 Q_23 Q_34 Q_41 Q_h Q_c : ℝ}
    (hAd12 : AdiabaticLeg Q_12) (hAd34 : AdiabaticLeg Q_34)
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_2 H_2 H_3)
    (hQ41 : IsothermalHeatIntoTorus Q_41 μ₀ n K T_4 H_4 H_1)
    (hQc : Q_c = Q_23) (hQh : Q_h = -Q_41)
    (hCarnot : CarnotReservoirHeatRelation Q_h T_h Q_c T_c)
    (hH23 : H_3 < H_2) (hH41 : H_4 < H_1) :
    M_1 ^ 2 = M_2 ^ 2 - M_3 ^ 2 + M_4 ^ 2 := by
  -- The remaining structural hypotheses record the physical consistency of
  -- the cycle of Fig. 3b (adiabatic legs carry no heat; reservoir ordering;
  -- field orderings along the isothermal legs); the algebraic derivation
  -- below does not need them, but they are part of the model.
  have _ : Q_12 = 0 := hAd12
  have _ : Q_34 = 0 := hAd34
  have _ : T_c < T_h := hTcth
  have _ : H_3 < H_2 := hH23
  have _ : H_4 < H_1 := hH41
  -- Identify the vertex temperatures with the reservoir temperatures
  -- (`T_1 = T_4 = T_h`, `T_2 = T_3 = T_c`) in the vertex laws.
  rw [hT2] at hEOS2 hQ23
  rw [hT3] at hEOS3
  rw [hT1] at hEOS1
  rw [hT4] at hEOS4 hQ41
  -- Isothermal-leg heats in magnetization form (bridges 1 and 2).
  have hcold : Q_23 = μ₀ * V ^ 2 / (2 * n * K) * T_c * (M_2 ^ 2 - M_3 ^ 2) :=
    heat_cold_leg_magnetization_form hμ₀ hV hn hK hTc hEOS2 hEOS3 hQ23
  have hhot : Q_41 = μ₀ * V ^ 2 / (2 * n * K) * T_h * (M_4 ^ 2 - M_1 ^ 2) :=
    heat_hot_leg_magnetization_form hμ₀ hV hn hK hTh hEOS4 hEOS1 hQ41
  -- The common prefactor is nonzero.
  have hA : μ₀ * V ^ 2 / (2 * n * K) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (ne_of_gt hμ₀) (pow_ne_zero 2 (ne_of_gt hV))
    · exact mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hn)) (ne_of_gt hK)
  -- Factorized reservoir heats (`Q_c = Q_23`, `Q_h = -Q_41`).
  have hQcf : Q_c = μ₀ * V ^ 2 / (2 * n * K) * T_c * (M_2 ^ 2 - M_3 ^ 2) := by
    rw [hQc]
    exact hcold
  have hQhf : Q_h = μ₀ * V ^ 2 / (2 * n * K) * T_h * (M_1 ^ 2 - M_4 ^ 2) := by
    rw [hQh, hhot]
    ring
  -- The Carnot (Clausius) relation cancels the prefactor and the
  -- temperatures, leaving the squared-magnetization balance (bridge 3).
  exact magnetization_balance_of_heats hA (ne_of_gt hTh) (ne_of_gt hTc) hQhf hQcf hCarnot

/-- **T3-C2 main target, "in terms of" form.**  Under the Carnot-cycle model
of `magnetization_vertex_one_sq`, the vertex-1 magnetization magnitude is

    `M_1 = √(M_2² − M_3² + M_4²)`

(the positive root, since `M_1` is a magnitude, `0 ≤ M_1`).
Proof route: rewrite the radicand by `magnetization_vertex_one_sq` and use
`Real.sqrt_sq` with `hM1`. -/
theorem magnetization_vertex_one
    {μ₀ V n K T_h T_c : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K)
    (hTh : 0 < T_h) (hTc : 0 < T_c) (hTcth : T_c < T_h)
    {T_1 T_2 T_3 T_4 H_1 H_2 H_3 H_4 M_1 M_2 M_3 M_4 : ℝ}
    (hT1 : T_1 = T_h) (hT2 : T_2 = T_c) (hT3 : T_3 = T_c) (hT4 : T_4 = T_h)
    (hEOS1 : EquationOfState T_1 M_1 V n K H_1)
    (hEOS2 : EquationOfState T_2 M_2 V n K H_2)
    (hEOS3 : EquationOfState T_3 M_3 V n K H_3)
    (hEOS4 : EquationOfState T_4 M_4 V n K H_4)
    {Q_12 Q_23 Q_34 Q_41 Q_h Q_c : ℝ}
    (hAd12 : AdiabaticLeg Q_12) (hAd34 : AdiabaticLeg Q_34)
    (hQ23 : IsothermalHeatIntoTorus Q_23 μ₀ n K T_2 H_2 H_3)
    (hQ41 : IsothermalHeatIntoTorus Q_41 μ₀ n K T_4 H_4 H_1)
    (hQc : Q_c = Q_23) (hQh : Q_h = -Q_41)
    (hCarnot : CarnotReservoirHeatRelation Q_h T_h Q_c T_c)
    (hH23 : H_3 < H_2) (hH41 : H_4 < H_1) (hM1 : 0 ≤ M_1) :
    M_1 = vertexOneMagnetizationExpr M_2 M_3 M_4 := by
  have hsq : M_1 ^ 2 = M_2 ^ 2 - M_3 ^ 2 + M_4 ^ 2 :=
    magnetization_vertex_one_sq hμ₀ hV hn hK hTh hTc hTcth hT1 hT2 hT3 hT4
      hEOS1 hEOS2 hEOS3 hEOS4 hAd12 hAd34 hQ23 hQ41 hQc hQh hCarnot hH23 hH41
  change M_1 = Real.sqrt (M_2 ^ 2 - M_3 ^ 2 + M_4 ^ 2)
  rw [← hsq, Real.sqrt_sq hM1]

end IPhO2026.T3C2
