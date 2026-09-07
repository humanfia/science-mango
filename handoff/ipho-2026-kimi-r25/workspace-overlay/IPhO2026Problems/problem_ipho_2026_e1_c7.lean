import Mathlib

/-!
# IPhO 2026 · Experiment E1-C7 — Thermal conductivity of acrylic from the wall
  resistance and the radial Fourier law

Autoformalization of IPhO 2026 E1-C7
(source: `reports/ipho_2026/problem_ipho_2026_e1_c7.source.json`,
problem pages `ipho_2026_source/image/E1_page-13.png` and
`ipho_2026_source/image/E1_page-14.png`, with equation (4) read from
`ipho_2026_source/image/E1_page-12.png`;
"Part C [8.0 pt]. Heat Conduction").

## Physical scenario (pages 12–14)

Part C studies the radial heat exchange between the water in the **outer
cylinder (OC)** and the water in the **inner cylinder (IC)** through the
acrylic cylindrical wall that separates them.  The Part-C preamble (page 12)
states the heat-flow model, equation (4) of the exam,

```
ΔQ/Δt = (1/R_Th)·(T_OC − T_IC)          (equation (4), page 12)
```

"where ΔQ is the heat received by the water in the IC through the wall during
the time interval Δt", and where "the effective thermal resistance R_Th
depends on the material and geometry of the wall separating IC and OC".  The
procedure (page 13) sets the OC water level to `h = 15 cm`, heats the OC water
to `65 °C`, and sets the IC water level to `h = 10 cm`.

For finitely many measurement times, equation (4) is recast as the
proportionality

```
(T_IC,j − T_IC,j−1)/(t_j − t_{j−1}) ∝ (T̄_OC − T̄_IC)   (equation (5), page 13)
```

graphed in C5; subquestion **C6 (the previous part)** determined the
experimental value of the effective wall thermal resistance `R_Th` from that
graph.  C7 consumes `R_Th` as a previous-part result; its numerical value is
the team's graph readout, not fixed by problem-only evidence, so `R_Th` is an
abstract positive parameter here.

Page 13 then states the radial Fourier law, equation (6) of the exam,

```
dQ/dt = −λ·A·dT/dr                      (equation (6), page 13)
```

"for radial heat conduction through a slim cylindrical wall", continued on
page 14: "where A is the area of the wall, λ is the thermal conductivity of
the wall material, and r denotes the distance from the axis of the cylinder."

**Subquestion E1-C7 (page 14).**  "Using equations (4) and (6), determine the
value λ of the thermal conductivity of acrylic (the material separating IC and
OC), indicating the formula that you used."

## Figure 17 readouts — availability note (answer-blind)

The shared context instructs to "use the dimensions in Figure 17".  Figure 17
belongs to the apparatus-description pages of the E1 exam, which are **not**
part of the answer-blind evidence bundle (only pages 9, 11–14 are available;
none shows Figure 17 — the same availability situation recorded in the E1-A1
sibling formalization).  Per the answer-blind protocol the dimensions must not
be guessed.  The wall geometry is therefore carried by the abstract parameters
of `AcrylicWallGeometry`:

* `innerRadius` — radius `r₁` of the inner surface of the acrylic wall, m;
* `outerRadius` — radius `r₂` of the outer surface of the acrylic wall, m;
* `wallHeight` — effective height `L` of the cylindrical wall across which the
  radial exchange takes place (the wetted wall height; the procedure fixes the
  water levels, the effective conducting height is a Figure-17 readout), m.

The stated procedure values `h = 15 cm` (OC level), `h = 10 cm` (IC level) and
the initial OC temperature `65 °C` are recorded as problem data
(`ocWaterLevel`, `icWaterLevel`, `ocInitialTemperatureCelsius`); the C7
formula itself involves only the Figure-17 wall geometry and `R_Th`.

## Physical model (governing laws and readouts)

The model state (`RadialHeatExchangeState`) carries the two distinct heat
rates of equations (4) and (6), the lumped water temperatures, the
conductivity, and the radial temperature profile in the wall; the governing
laws (`RadialConductionLaws`) are:

1. *Heat-flow model* (`heat_flow_model`), equation (4):
   `ΔQ/Δt = (T_OC − T_IC)/R_Th`, with `ΔQ/Δt` the heat **received by the IC
   water** per unit time.
2. *Radial Fourier law* (`fourier_radial`), equation (6), at every radius `r`
   of the wall: the outward radial heat current is constant through the wall
   (steady state; the instruction "ignore the heat capacity of the apparatus"
   removes wall heat storage) and equals `−λ·A(r)·dT/dr`, with the lateral
   shell area `A(r) = 2π·r·L` (`cylindricalShellArea`).
3. *Boundary conditions* (`boundary_inner`, `boundary_outer`): the lumped
   water temperatures equal the wall surface temperatures, `T(r₁) = T_IC`,
   `T(r₂) = T_OC` (the well-stirred/homogenized-water idealization of the
   procedure, "use the pump to homogenize the water temperature").
4. *Current balance and orientation* (`current_balance`): the heat received
   by the IC per unit time is the inward radial current, i.e. the negative of
   the outward current of equation (6).  In the experimental regime
   `T_OC > T_IC` (the OC is heated to `65 °C`), so the outward current is
   negative and the received heat rate is positive; the regime is imposed as
   the hypothesis `S.innerTemperature < S.outerTemperature` where the
   cancellation needs it.
5. *Regularity side conditions* (`profile_differentiable`,
   `profile_deriv_integrable`): the wall temperature profile is differentiable
   with interval-integrable derivative on `[r₁, r₂]`, licensing the
   fundamental theorem of calculus
   (`intervalIntegral.integral_deriv_eq_sub`).

## Derivation route (the requested formula)

Equation (6) at radius `r` gives `dT/dr = −J/(2π·λ·L·r)` with `J` the
(constant) outward current; integrating from `r₁` to `r₂` (FTC) gives
`T(r₂) − T(r₁) = −J·ln(r₂/r₁)/(2π·λ·L)`.  The boundary conditions and the
current balance turn this into
`T_OC − T_IC = (ΔQ/Δt)·ln(r₂/r₁)/(2π·λ·L)`, and equation (4) substitutes
`ΔQ/Δt = (T_OC − T_IC)/R_Th`.  Cancelling the nonzero temperature difference
(the regime `T_IC < T_OC`) gives the product form `2π·λ·L·R_Th = ln(r₂/r₁)`,
hence the requested formula

```
λ = ln(r₂/r₁) / (2π·L·R_Th).
```

## Current target (conclusion side only)

`conductivity_eq_candidate` (blueprint
`thm:physics:ipho_2026_e1_c7:target`): the conductivity of acrylic is the raw
end-to-end candidate quantity
`candidateConductivity g R_Th = ln(r₂/r₁)/(2π·L·R_Th)`; the closed form
appears only in conclusions and in the candidate definition.  The bridge
lemmas `profile_temperature_drop` (integrated Fourier law),
`water_temperature_difference_eq` (boundary + balance form), and
`conductivity_product_form` (product form after cancelling `ΔT`) isolate the
nontrivial steps; `candidateConductivity_pos` certifies positivity of the
candidate in the physical regime.

*Numeric value and rounding.*  The numerical answer is the team's C6 readout
of `R_Th` combined with the Figure-17 geometry; neither is fixed by the
problem-only evidence bundle, so the raw end-to-end quantity is defined but no
numerical value and no source-derived rounding rule is pinned.  C7 carries no
`±` uncertainty specification (the "no uncertainty" note on page 13 concerns
C4 only), so no uncertainty is propagated.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
lengths and radii in m, areas in m², temperatures (and temperature
differences) in K, heat rates in W, the effective thermal resistance `R_Th`
in K/W, and the thermal conductivity `λ` in W/(m·K).  The recorded initial OC
temperature is kept in °C exactly as stated in the procedure.

## Grounding gaps (LeanExplore, packages Mathlib + Physlib)

* No Fourier heat-conduction / thermal-conductivity declaration exists in
  Mathlib or Physlib: the query "Fourier law heat conduction thermal
  conductivity heat flux" returned only Fourier-*analysis* declarations
  (`TemperedDistribution.fourier_lineDerivOp_eq`, `Real.fourierChar`) and the
  stat-mech `CanonicalEnsemble.heatCapacity` (a near miss: a constant-volume
  heat capacity, not a conduction law).  Equation (6) is stated locally with
  Mathlib's `deriv` as the radial derivative.
* No thermal-resistance / lumped heat-flow declaration exists: the query
  "thermal resistance heat flow temperature difference" returned only
  dimension/unit tags (`Dimension.div_temperature`, `Temperature`,
  `Dimension.L𝓭_temperature`) and the unrelated dynamical-systems `Flow`.
  Equation (4) is stated locally as the equation field `heat_flow_model`.
* Grounded Mathlib names used: `deriv`, `DifferentiableAt`,
  `IntervalIntegrable`, `MeasureTheory.volume`,
  `intervalIntegral.integral_deriv_eq_sub` (FTC, proof route of
  `profile_temperature_drop`), `Real.log`, `Real.log_pos`, `one_lt_div`.
-/

namespace IPhO2026.E1C7

/-! ## Problem data (stated numerical values, page 13 procedure) -/

/-- Water level set in the outer cylinder (OC), `h = 15 cm` (procedure step 1,
page 13: "Set the water level in the OC to h = 15 cm."), in metres.  Context
data for the effective wetted wall height; the C7 formula uses the Figure-17
geometry instead. -/
noncomputable def ocWaterLevel : ℝ := 15 / 100

/-- Water level set in the inner cylinder (IC), `h = 10 cm` (procedure step 3,
page 13: "Set the water level in the IC to h = 10 cm and start the
stopwatch."), in metres. -/
noncomputable def icWaterLevel : ℝ := 10 / 100

/-- Initial temperature to which the OC water is heated, `65 °C` (procedure
step 2, page 13: "Heat the water in the OC to 65 °C. Use the pump to
homogenize the water temperature.").  Recorded in °C exactly as stated; it
fixes the experimental regime `T_OC > T_IC`. -/
noncomputable def ocInitialTemperatureCelsius : ℝ := 65

/-- Data fact: the OC water level is positive. -/
theorem ocWaterLevel_pos : 0 < ocWaterLevel := by
  unfold ocWaterLevel; norm_num

/-- Data fact: the IC water level is positive. -/
theorem icWaterLevel_pos : 0 < icWaterLevel := by
  unfold icWaterLevel; norm_num

/-- Data fact: the IC water level is below the OC water level
(`10 cm < 15 cm`); the effective wetted height of the wall is bounded by the
lower level. -/
theorem icWaterLevel_lt_ocWaterLevel : icWaterLevel < ocWaterLevel := by
  unfold icWaterLevel ocWaterLevel; norm_num

/-- Data fact: the initial OC temperature `65 °C` is positive. -/
theorem ocInitialTemperatureCelsius_pos : 0 < ocInitialTemperatureCelsius := by
  unfold ocInitialTemperatureCelsius; norm_num

/-! ## Figure 17 geometry of the acrylic wall (abstract; see the availability
note in the module docstring) -/

/-- Geometry of the acrylic cylindrical wall separating IC and OC, as read
from Figure 17 of the exam.  Figure 17 is not part of the answer-blind
evidence bundle, so the dimensions are abstract parameters with their
physical roles recorded; no values are assumed.  All components are reals in
metres. -/
structure AcrylicWallGeometry where
  /-- Radius `r₁` of the inner surface of the acrylic wall (the IC-side
  surface; Figure 17 readout).  Units: m. -/
  innerRadius : ℝ
  /-- Radius `r₂` of the outer surface of the acrylic wall (the OC-side
  surface; Figure 17 readout).  Units: m. -/
  outerRadius : ℝ
  /-- Effective height `L` of the cylindrical wall across which the radial
  heat exchange takes place (Figure 17 readout; the wetted conducting
  height).  Units: m. -/
  wallHeight : ℝ

/-- Lateral area of the cylindrical shell of radius `r` and height `L`,
`A(r) = 2π·r·L` — the "area of the wall" of equation (6) (page 14: "where A
is the area of the wall … and r denotes the distance from the axis of the
cylinder") evaluated at the radius `r` through which the heat current passes.
Units: m². -/
noncomputable def cylindricalShellArea (r L : ℝ) : ℝ := 2 * Real.pi * r * L

/-- Naming expansion of the shell area (unfolds the definition). -/
theorem cylindricalShellArea_eq (r L : ℝ) :
    cylindricalShellArea r L = 2 * Real.pi * r * L := rfl

/-- The shell area is positive at positive radius and positive wall height. -/
theorem cylindricalShellArea_pos {r L : ℝ} (hr : 0 < r) (hL : 0 < L) :
    0 < cylindricalShellArea r L := by
  unfold cylindricalShellArea; positivity

/-! ## The radial heat-exchange state and its governing laws -/

/-- State of the radial heat exchange through the acrylic wall at one
observation time.  It keeps the two heat rates of equations (4) and (6)
distinct — `ΔQ/Δt` of equation (4) is the heat **received by the IC water**
per unit time, while `dQ/dt` of equation (6) is the radial heat current in
the direction of increasing `r`; `current_balance` below ties them with the
correct orientation.  All components are reals carrying the SI units recorded
in the module docstring. -/
structure RadialHeatExchangeState where
  /-- Heat received by the IC water through the wall per unit time, `ΔQ/Δt` of
  equation (4).  Units: W. -/
  heatReceivedRateIC : ℝ
  /-- Steady radial heat current in the direction of increasing radius,
  `dQ/dt` of equation (6); constant across the cylindrical shells of the wall
  (steady state, wall heat capacity ignored).  Units: W. -/
  outwardRadialCurrent : ℝ
  /-- Lumped temperature `T_IC` of the IC water.  Units: K. -/
  innerTemperature : ℝ
  /-- Lumped temperature `T_OC` of the OC water.  Units: K. -/
  outerTemperature : ℝ
  /-- Thermal conductivity `λ` of acrylic (the wall material).  Units:
  W/(m·K). -/
  conductivity : ℝ
  /-- Radial temperature profile `T(r)` inside the wall, a function of the
  distance `r` from the cylinder axis.  Units: K. -/
  temperatureProfile : ℝ → ℝ

/-- **Governing laws of the E1-C7 model**, equations (4) and (6) of the exam
plus the modeling relations that connect them, imposed on a heat-exchange
state `S`, a wall geometry `g` (Figure 17), and the effective wall thermal
resistance `R_Th` (the C6 previous-part result, K/W).  Every field is a
physical law, a boundary/steady-state relation, or a regularity side
condition; no field states the requested formula
`λ = ln(r₂/r₁)/(2π·L·R_Th)` itself. -/
structure RadialConductionLaws (S : RadialHeatExchangeState)
    (g : AcrylicWallGeometry) (R_Th : ℝ) : Prop where
  /-- Equation (4) of the exam (page 12): the heat received by the IC water
  per unit time is the temperature difference across the wall divided by the
  effective thermal resistance, `ΔQ/Δt = (T_OC − T_IC)/R_Th`. -/
  heat_flow_model :
    S.heatReceivedRateIC = (S.outerTemperature - S.innerTemperature) / R_Th
  /-- Equation (6) of the exam (page 13): Fourier's law for radial conduction
  through the slim cylindrical wall, `dQ/dt = −λ·A(r)·dT/dr`, at every radius
  `r` of the wall, with `A(r) = 2π·r·L` the lateral shell area
  (`cylindricalShellArea`).  Constancy of the left-hand side across radii is
  the steady-state content (no heat storage in the wall: "ignore the heat
  capacity of the apparatus", page 13). -/
  fourier_radial : ∀ r ∈ Set.Icc g.innerRadius g.outerRadius,
    S.outwardRadialCurrent =
      -S.conductivity * cylindricalShellArea r g.wallHeight *
        deriv S.temperatureProfile r
  /-- Boundary condition at the inner wall surface: the wall temperature at
  `r₁` equals the lumped IC water temperature (homogenized water). -/
  boundary_inner : S.temperatureProfile g.innerRadius = S.innerTemperature
  /-- Boundary condition at the outer wall surface: the wall temperature at
  `r₂` equals the lumped OC water temperature. -/
  boundary_outer : S.temperatureProfile g.outerRadius = S.outerTemperature
  /-- Current balance and orientation: the heat received by the IC water per
  unit time is the inward radial heat current, i.e. the negative of the
  outward current of equation (6).  In the experimental regime `T_OC > T_IC`
  the outward current is negative (heat flows from the OC inward to the IC)
  and the received rate is positive. -/
  current_balance : S.heatReceivedRateIC = -S.outwardRadialCurrent
  /-- Regularity side condition: the wall temperature profile is
  differentiable at every radius of the wall (licenses FTC). -/
  profile_differentiable : ∀ r ∈ Set.Icc g.innerRadius g.outerRadius,
    DifferentiableAt ℝ S.temperatureProfile r
  /-- Regularity side condition: the radial derivative of the profile is
  interval-integrable over the wall thickness (licenses
  `intervalIntegral.integral_deriv_eq_sub`). -/
  profile_deriv_integrable :
    IntervalIntegrable (deriv S.temperatureProfile) MeasureTheory.volume
      g.innerRadius g.outerRadius

/-! ## Raw end-to-end candidate quantity (definition only; correctness is
proved in the target theorems below) -/

/-- Raw end-to-end quantity requested as the thermal conductivity of acrylic:
`ln(r₂/r₁)/(2π·L·R_Th)`, the logarithm of the ratio of the outer to the inner
wall radius divided by `2π` times the wall height times the effective thermal
resistance from C6.  Units: W/(m·K). -/
noncomputable def candidateConductivity (g : AcrylicWallGeometry) (R_Th : ℝ) : ℝ :=
  Real.log (g.outerRadius / g.innerRadius) / (2 * Real.pi * g.wallHeight * R_Th)

/-- Naming expansion of the candidate (unfolds the definition). -/
theorem candidateConductivity_eq (g : AcrylicWallGeometry) (R_Th : ℝ) :
    candidateConductivity g R_Th =
      Real.log (g.outerRadius / g.innerRadius) /
        (2 * Real.pi * g.wallHeight * R_Th) := rfl

/-! ## Target: the conductivity formula `λ = ln(r₂/r₁)/(2π·L·R_Th)` -/

/-- **E1-C7 bridge lemma (integrated Fourier law).**  The temperature drop of
the wall profile across the acrylic thickness is
`T(r₂) − T(r₁) = −J·ln(r₂/r₁)/(2π·λ·L)`, with `J` the constant outward radial
current.  Proof route: equation (6) (`fourier_radial`) at radius `r` with
`0 < λ`, `0 < L` gives
`deriv T r = −J/(2π·λ·L·r) = (−J/(2π·λ·L))·r⁻¹` on `[r₁, r₂]`; integrate from
`r₁` to `r₂` with `intervalIntegral.integral_deriv_eq_sub` (uses
`profile_differentiable`, `profile_deriv_integrable`), and
`∫ r in r₁..r₂, r⁻¹ = Real.log r₂ − Real.log r₁ = Real.log (r₂/r₁)`
(`intervalIntegral.integral_one_div` / `Real.log_div`, needs
`0 < r₁ ≤ r₂`). -/
theorem profile_temperature_drop (S : RadialHeatExchangeState)
    (g : AcrylicWallGeometry) {R_Th : ℝ} (L : RadialConductionLaws S g R_Th)
    (hg1 : 0 < g.innerRadius) (hg2 : g.innerRadius < g.outerRadius)
    (hL : 0 < g.wallHeight) (hlam : 0 < S.conductivity) :
    S.temperatureProfile g.outerRadius - S.temperatureProfile g.innerRadius =
      -S.outwardRadialCurrent * Real.log (g.outerRadius / g.innerRadius) /
        (2 * Real.pi * S.conductivity * g.wallHeight) := by
  have hr1 : g.innerRadius ≤ g.outerRadius := le_of_lt hg2
  have hr2pos : 0 < g.outerRadius := lt_trans hg1 hg2
  have hDpos : (0 : ℝ) < 2 * Real.pi * S.conductivity * g.wallHeight :=
    mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hlam) hL
  have hD : (2 * Real.pi * S.conductivity * g.wallHeight) ≠ 0 := ne_of_gt hDpos
  -- Solve equation (6) (`fourier_radial`) for the radial derivative at each
  -- radius of the wall: `deriv T r = (−J/(2π·λ·L))·r⁻¹`.
  have hderiv : ∀ r ∈ Set.Icc g.innerRadius g.outerRadius,
      deriv S.temperatureProfile r =
        (-S.outwardRadialCurrent / (2 * Real.pi * S.conductivity * g.wallHeight)) *
          r⁻¹ := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hg1 hr.1
    have hrr : r ≠ 0 := ne_of_gt hrpos
    have hJ := L.fourier_radial r hr
    rw [cylindricalShellArea_eq] at hJ
    rw [eq_mul_inv_iff_mul_eq₀ hrr, eq_div_iff hD]
    linear_combination hJ
  -- Integrate the derivative across the wall with the fundamental theorem of
  -- calculus (`intervalIntegral.integral_deriv_eq_sub`).
  have hFTC : ∫ r in g.innerRadius..g.outerRadius, deriv S.temperatureProfile r =
      S.temperatureProfile g.outerRadius - S.temperatureProfile g.innerRadius :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x hx => L.profile_differentiable x (by rwa [Set.uIcc_of_le hr1] at hx))
      L.profile_deriv_integrable
  -- Evaluate the same integral from the explicit pointwise form of the
  -- derivative: `∫ r in r₁..r₂, r⁻¹ = log (r₂/r₁)` (`integral_inv`).
  have h0mem : (0 : ℝ) ∉ Set.uIcc g.innerRadius g.outerRadius := by
    rw [Set.uIcc_of_le hr1]
    exact fun h => absurd (Set.mem_Icc.mp h).1 (not_le_of_gt hg1)
  have hInt : ∫ r in g.innerRadius..g.outerRadius, deriv S.temperatureProfile r =
      (-S.outwardRadialCurrent / (2 * Real.pi * S.conductivity * g.wallHeight)) *
        Real.log (g.outerRadius / g.innerRadius) := by
    have hcong : ∫ r in g.innerRadius..g.outerRadius, deriv S.temperatureProfile r =
        ∫ r in g.innerRadius..g.outerRadius,
          (-S.outwardRadialCurrent / (2 * Real.pi * S.conductivity * g.wallHeight)) *
            r⁻¹ :=
      intervalIntegral.integral_congr
        (fun x hx => hderiv x (by rwa [Set.uIcc_of_le hr1] at hx))
    rw [hcong, intervalIntegral.integral_const_mul,
      integral_inv h0mem]
  rw [hFTC] at hInt
  rw [hInt]
  ring

/-- **E1-C7 bridge lemma (boundary + balance form).**  The water temperature
difference equals the heat rate received by the IC times the geometric
factor: `T_OC − T_IC = (ΔQ/Δt)·ln(r₂/r₁)/(2π·λ·L)`.  Proof route: rewrite the
boundary conditions in `profile_temperature_drop`, then use
`current_balance` (`ΔQ/Δt = −J`). -/
theorem water_temperature_difference_eq (S : RadialHeatExchangeState)
    (g : AcrylicWallGeometry) {R_Th : ℝ} (L : RadialConductionLaws S g R_Th)
    (hg1 : 0 < g.innerRadius) (hg2 : g.innerRadius < g.outerRadius)
    (hL : 0 < g.wallHeight) (hlam : 0 < S.conductivity) :
    S.outerTemperature - S.innerTemperature =
      S.heatReceivedRateIC * Real.log (g.outerRadius / g.innerRadius) /
        (2 * Real.pi * S.conductivity * g.wallHeight) := by
  have h1 := profile_temperature_drop S g L hg1 hg2 hL hlam
  rw [L.boundary_inner, L.boundary_outer, ← L.current_balance] at h1
  exact h1

/-- **E1-C7 bridge lemma (product form).**  Combining equations (4) and (6)
through the wall gives `2π·λ·L·R_Th = ln(r₂/r₁)`.  Proof route: substitute
`heat_flow_model` (equation (4), `ΔQ/Δt = (T_OC − T_IC)/R_Th`) into
`water_temperature_difference_eq`, clear the nonzero denominators
(`0 < R_Th`, `0 < λ`, `0 < L`, `0 < π`), and cancel the nonzero temperature
difference `T_OC − T_IC ≠ 0` coming from the experimental regime
`T_IC < T_OC` (the OC is heated to `65 °C`). -/
theorem conductivity_product_form (S : RadialHeatExchangeState)
    (g : AcrylicWallGeometry) {R_Th : ℝ} (L : RadialConductionLaws S g R_Th)
    (hg1 : 0 < g.innerRadius) (hg2 : g.innerRadius < g.outerRadius)
    (hL : 0 < g.wallHeight) (hlam : 0 < S.conductivity) (hR : 0 < R_Th)
    (hΔT : S.innerTemperature < S.outerTemperature) :
    2 * Real.pi * S.conductivity * g.wallHeight * R_Th =
      Real.log (g.outerRadius / g.innerRadius) := by
  have h2 := water_temperature_difference_eq S g L hg1 hg2 hL hlam
  rw [L.heat_flow_model] at h2
  have hne : S.outerTemperature - S.innerTemperature ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hΔT)
  have hR' : R_Th ≠ 0 := ne_of_gt hR
  have hD : (2 * Real.pi * S.conductivity * g.wallHeight) ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hlam) hL)
  -- Clear the nonzero denominators `2π·λ·L` and `R_Th` in the substituted
  -- relation `T_OC − T_IC = ((T_OC − T_IC)/R_Th)·ln(r₂/r₁)/(2π·λ·L)`.
  rw [eq_div_iff hD] at h2
  rw [div_mul_eq_mul_div₀] at h2
  rw [eq_div_iff hR'] at h2
  -- Factor out the nonzero temperature difference and cancel it.
  have hfact : (S.outerTemperature - S.innerTemperature) *
      ((2 * Real.pi * S.conductivity * g.wallHeight) * R_Th -
        Real.log (g.outerRadius / g.innerRadius)) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp hfact with h | h
  · exact absurd h hne
  · linear_combination (sub_eq_zero.mp h)

/-- **E1-C7 main target** (blueprint `thm:physics:ipho_2026_e1_c7:target`).
The formula requested by the subquestion: the thermal conductivity of acrylic
is
`λ = ln(r₂/r₁)/(2π·L·R_Th)`, with `r₁`, `r₂`, `L` the Figure-17 wall geometry
and `R_Th` the effective thermal resistance determined in C6.  Proof route:
divide `conductivity_product_form` by the nonzero factor `2π·L·R_Th`
(`0 < π`, `0 < L`, `0 < R_Th`). -/
theorem conductivity_eq_candidate (S : RadialHeatExchangeState)
    (g : AcrylicWallGeometry) {R_Th : ℝ} (L : RadialConductionLaws S g R_Th)
    (hg1 : 0 < g.innerRadius) (hg2 : g.innerRadius < g.outerRadius)
    (hL : 0 < g.wallHeight) (hlam : 0 < S.conductivity) (hR : 0 < R_Th)
    (hΔT : S.innerTemperature < S.outerTemperature) :
    S.conductivity = candidateConductivity g R_Th := by
  have h3 := conductivity_product_form S g L hg1 hg2 hL hlam hR hΔT
  have hne : (2 * Real.pi * g.wallHeight * R_Th) ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hL) hR)
  rw [candidateConductivity_eq, eq_div_iff hne]
  linear_combination h3

/-- Physical sanity certificate: in the geometric and thermal regime of the
experiment (positive inner radius, positive wall thickness, positive
conducting height, positive measured resistance) the candidate conductivity
is positive, `0 < ln(r₂/r₁)/(2π·L·R_Th)`, as a thermal conductivity must
be. -/
theorem candidateConductivity_pos (g : AcrylicWallGeometry) {R_Th : ℝ}
    (hg1 : 0 < g.innerRadius) (hg2 : g.innerRadius < g.outerRadius)
    (hL : 0 < g.wallHeight) (hR : 0 < R_Th) :
    0 < candidateConductivity g R_Th := by
  unfold candidateConductivity
  have hlog : 0 < Real.log (g.outerRadius / g.innerRadius) :=
    Real.log_pos ((one_lt_div hg1).mpr hg2)
  positivity

end IPhO2026.E1C7
