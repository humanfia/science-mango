import Mathlib

/-!
# IPhO 2026 · Experiment E1-C6 — Effective wall thermal resistance `R_Th` from the C5 graph

Autoformalization of IPhO 2026 E1-C6
(source: `reports/ipho_2026/problem_ipho_2026_e1_c6.source.json`,
problem pages `ipho_2026_source/image/E1_page-12.png` (Part C introduction,
equation (4)), `ipho_2026_source/image/E1_page-13.png` (procedure, C1–C6,
equations (5) and (6)) and `ipho_2026_source/image/E1_page-14.png`
(symbols of equation (6), C7), "Part C [8.0 pt]. Heat Conduction").

## Physical scenario (pages 12–13)

Water in the **outer cylinder (OC)** and water in the **inner cylinder (IC)**
exchange heat radially through the acrylic cylindrical wall that separates
them.  "Heat conduction through a solid wall follows the relation:

```
ΔQ / Δt = (1 / R_Th) · (T_OC − T_IC)        (equation (4), page 12)
```

where `ΔQ` is the heat received by the water in the IC through the wall during
the time interval `Δt.  The effective thermal resistance `R_Th` depends on the
material and geometry of the wall separating IC and OC."  Procedure (page 13):
(1) set the OC water level to `h = 15 cm`; (2) heat the OC water to `65 °C`,
homogenizing with the pump; (3) set the IC water level to `h = 10 cm` and start
the stopwatch.  C1/C2 record and plot `T_IC(t)` and `T_OC(t)`.  "If the
variables are measured a finite number of times, Equation (4) can be expressed
as

```
(T_IC,j − T_IC,(j−1)) / (t_j − t_{j−1})  ∝  T̄_OC − T̄_IC        (5)
```

where `j` represents the measurement number and `T̄` are the average
temperatures at each cylinder during the interval `t_{j−1}` to `t_j`"
(page 13).  C5 graphs the left-hand side of (5) against the right-hand side.

**Subquestion E1-C6 [1.6 pt] (page 13).**  "Determine the value of `R_Th`
from the graph constructed in C5."

Page 13 also states the shared Part-C governing law used on the later route
(C7): "Fourier's law for radial heat conduction through a slim cylindrical
wall can be written as

```
dQ / dt = −λ · A · dT / dr                  (6)
```

where `A` is the area of the wall, `λ` is the thermal conductivity of the wall
material, and `r` denotes the distance from the axis of the cylinder"
(pages 13–14).  Equation (6) is **not** a hypothesis of the C6 target; it is
recorded here (`RadialFourierConduction`) as the governing law of the C7
route, exactly as the E1-B4 file records Clausius–Clapeyron for the B5 route.

## Figure 17 / reference sheet / C5 graph — availability note (answer-blind)

The problem instructs to "use the dimensions in Figure 17", and the
determination of `R_Th` from the C5-graph slope requires the mass of the IC
water (`m_IC = ρ_w · A_IC · h_IC`) and the specific heat capacity of water.
Figure 17, the reference constants and values sheet (which carries the water
density `ρ_w` and specific heat `c_w`), and the student's C1 table / C5 graph
are **not** part of the answer-blind evidence bundle (only E1 pages 9, 11–14
are available, and none of them shows Figure 17, the reference sheet, or any
recorded data; cf. the E1-A1 availability note).  Per the answer-blind
protocol no values are guessed.  They are formalized as **abstract positive
parameters** with their physical roles recorded:

* `d`   — inner diameter of the cylindrical IC (Fig. 17), in metres;
* `ρ_w` — water density (reference constants sheet), in kg/m³;
* `c_w` — specific heat capacity of water (reference constants sheet),
  in J/(kg·K);
* the C1 measurement rows and the C5-graph slope readout `k`, carried by
  `TemperatureRecord` and `c5GraphSlope`.

Once the figure value, the reference-sheet constants, and the graph readout
are supplied to these parameters, the candidate below evaluates numerically;
no target value is assumed anywhere in this file.  A source-derived *numeric*
rounding rule (two significant figures, matching the two-figure procedure
readouts `h = 10 cm`, `h = 15 cm`, `65 °C`) can only be applied once those
readouts are available; see the task-result record.

## Physical model (governing laws and readouts)

1. *Calorimetry of the IC water* (`IntervalHeatExchange.calorimetry_ic_water`):
   the heat received by the IC water during an interval raises its
   temperature, `ΔQ = m_IC · c_w · ΔT_IC`.  This is the modeling content of
   "ignore the heat capacity of the apparatus where instructed" (page 13):
   only the IC water stores the heat `ΔQ` that equation (4) delivers.
2. *Heat-flow model, equation (4)*
   (`IntervalHeatExchange.heat_flow_model`): over the interval `t_{j−1} → t_j`
   the wall delivers `ΔQ = (T̄_OC − T̄_IC) / R_Th · Δt`, the finite-interval
   form of equation (4) with the interval-averaged temperature difference of
   equation (5).
3. *C5 graph readout* (`c5GraphSlope`): the C5 graph plots the
   finite-difference rate `(T_IC,j − T_IC,j−1)/(t_j − t_{j−1})` against the
   average difference `T̄_OC − T̄_IC`; by equation (5) the points lie on a
   proportionality line through the origin, and its slope `k` is read off any
   plotted interval with nonzero abscissa as ordinate/abscissa.
4. *Figure-17 geometry and IC water mass* (`icCrossSectionalArea`,
   `icWaterVolume`, `icWaterMass`): the IC water fills the cross-section
   `π·(d/2)²` to the procedure level `h = 10 cm`, so
   `m_IC = ρ_w · π·(d/2)² · h_IC`.

## Current target (conclusion side only)

`thermalResistance_eq_candidate` (blueprint
`thm:physics:ipho_2026_e1_c6:target`): for any measurement interval obeying
the heat-exchange laws, on the heating branch (OC warmer than IC, stopwatch
running forward), with positive water constants and IC diameter,

```
R_Th = 1 / (m_IC · c_w · k)  =  candidateThermalResistance ρ_w c_w d k,
```

carried by the raw end-to-end candidate definition
`candidateThermalResistance`; the closed form appears only in conclusions.
Bridges: `ic_water_heating_eq_wall_flow` (the two law fields eliminate to the
combined interval equation), `finiteDifferenceRate_eq_physical_slope` (the C5
proportionality of equation (5) with the physical slope
`1 / (m_IC · c_w · R_Th)` identified — the previous-part C5 content derived
inline from problem-only material), `c5GraphSlope_eq_physical` (the readout
`slope k` equals that physical slope).  Sanity certificates:
`heatReceived_pos`, `finiteDifferenceRate_pos`, `c5GraphSlope_pos` (heating
branch: heat flows into the IC, `T_IC` rises, the C5 slope is positive), and
`determined_resistance_pos` (the determined resistance is positive).

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
lengths in m, areas in m², volumes in m³, density in kg/m³, mass in kg,
specific heat in J/(kg·K), time in s, heat in J, thermal resistance `R_Th` in
K/W, the C5 slope `k` in s⁻¹ (i.e. (°C/s)/°C).  Recorded temperatures are in
°C as read by the sensors; only temperature *differences* enter the laws, and
these coincide with kelvin differences, so `R_Th` is equally K/W or °C/W.
`initialOcWaterTemperatureCelsius` is an initial-condition readout in °C, not
a thermodynamic temperature entering a law.

## Grounding gaps (LeanExplore, packages Mathlib + Physlib)

* No thermal-resistance / heat-flow / wall-conduction declaration exists in
  Mathlib or Physlib (query "thermal resistance heat conduction Fourier's law"
  returned only the unrelated `fourier` basis functions and the stat-mech
  `CanonicalEnsemble.heatCapacity`).  Equation (4) and the C5/calorimetry
  model are stated locally (`IntervalHeatExchange`).
* No Fourier's-law / thermal-conductivity declaration exists (query "heat flow
  rate thermal conductivity material wall" returned only
  `CanonicalEnsemble.heatCapacity` near misses and fluid-dynamics hits).
  Equation (6) is stated locally as the equation-giving predicate
  `RadialFourierConduction`.
* `CanonicalEnsemble.heatCapacity` (declaration id 393896) is a stat-mech
  derivative notion (heat capacity at constant volume of an ensemble), not the
  calorimetric relation `ΔQ = m·c·ΔT` an experiment assumes.  Near miss;
  calorimetry is stated locally (`calorimetry_ic_water`).
* `FluidDynamics.MassDensity` (declaration id 386034) is a continuum field
  notion; the lumped relation `m = ρ·V` is stated directly (`icWaterMass`),
  consistent with the sibling E1-A1 formalization.
* No water density or specific-heat constant exists in Physlib; `ρ_w`, `c_w`
  are abstract positive parameters pending the reference constants sheet.
-/

namespace IPhO2026.E1C6

/-! ## Problem data (stated values, page 13 procedure) -/

/-- OC water level, `h = 15 cm` (procedure step 1, page 13: "Set the water
level in the OC to `h = 15 cm`.").  Setup parameter of the Part-C run; it does
not enter the C6 closed form (only the IC water mass stores the heat `ΔQ`).
Units: metres. -/
noncomputable def ocWaterLevelHeight : ℝ := 15 / 100

/-- IC water level, `h = 10 cm` (procedure step 3, page 13: "Set the water
level in the IC to `h = 10 cm` and start the stopwatch.").  Sets the IC water
volume and hence the mass `m_IC` entering the C6 route.  Units: metres. -/
noncomputable def icWaterLevelHeight : ℝ := 10 / 100

/-- Initial OC water temperature, `65 °C` (procedure step 2, page 13: "Heat
the water in the OC to 65 °C.  Use the pump to homogenize the water
temperature.").  Initial condition placing the run on the heating branch
(OC warmer than IC, heat flowing into the IC); recorded in °C as stated.
Units: °C. -/
noncomputable def initialOcWaterTemperatureCelsius : ℝ := 65

/-- Data fact: the OC water level `h = 15 cm` is positive. -/
theorem ocWaterLevelHeight_pos : 0 < ocWaterLevelHeight := by
  unfold ocWaterLevelHeight; norm_num

/-- Data fact: the IC water level `h = 10 cm` is positive. -/
theorem icWaterLevelHeight_pos : 0 < icWaterLevelHeight := by
  unfold icWaterLevelHeight; norm_num

/-- Data fact: the initial OC water temperature `65 °C` is positive (in °C). -/
theorem initialOcWaterTemperatureCelsius_pos :
    0 < initialOcWaterTemperatureCelsius := by
  unfold initialOcWaterTemperatureCelsius; norm_num

/-! ## Figure 17 geometry and the IC water mass (readouts kept abstract; see
the availability note) -/

/-- Cross-sectional area of the cylindrical inner cylinder (IC) of inner
diameter `d` (Figure 17 readout; circular cross-section).  Units: m². -/
noncomputable def icCrossSectionalArea (d : ℝ) : ℝ := Real.pi * (d / 2) ^ 2

/-- Volume of the water in the IC: the IC cross-section times the procedure
fill level `h = 10 cm` (Figure 17 geometry + procedure step 3).  Units: m³. -/
noncomputable def icWaterVolume (d : ℝ) : ℝ :=
  icCrossSectionalArea d * icWaterLevelHeight

/-- Mass `m_IC` of the water in the IC: water density times IC water volume
(`ρ_w` from the reference constants sheet, kept abstract).  This is the mass
whose heat capacity `m_IC · c_w` stores the heat `ΔQ` of equation (4).
Units: kg. -/
noncomputable def icWaterMass (ρ_w d : ℝ) : ℝ := ρ_w * icWaterVolume d

/-- The IC cross-section is positive for positive inner diameter. -/
theorem icCrossSectionalArea_pos {d : ℝ} (hd : 0 < d) :
    0 < icCrossSectionalArea d := by
  unfold icCrossSectionalArea; positivity

/-- The IC water volume is positive for positive inner diameter. -/
theorem icWaterVolume_pos {d : ℝ} (hd : 0 < d) : 0 < icWaterVolume d :=
  mul_pos (icCrossSectionalArea_pos hd) icWaterLevelHeight_pos

/-- The IC water mass is positive for positive water density and inner
diameter. -/
theorem icWaterMass_pos {ρ_w d : ℝ} (hρ : 0 < ρ_w) (hd : 0 < d) :
    0 < icWaterMass ρ_w d :=
  mul_pos hρ (icWaterVolume_pos hd)

/-! ## The C1 measurement records and the C5 interval readouts -/

/-- One row of the C1 table (page 13, C1: "Record the internal temperature
`T_IC` and external temperature `T_OC` as a function of time `t`"): the
stopwatch time and the two water temperatures.  Temperatures are recorded in
°C as read; only differences enter the laws.  Units: `time` in s,
`innerTemp`/`outerTemp` in °C. -/
structure TemperatureRecord where
  /-- Stopwatch time `t` of the measurement.  Units: s. -/
  time : ℝ
  /-- Water temperature `T_IC` in the inner cylinder.  Units: °C. -/
  innerTemp : ℝ
  /-- Water temperature `T_OC` in the outer cylinder.  Units: °C. -/
  outerTemp : ℝ

/-- Length `Δt = t_j − t_{j−1}` of the measurement interval between the
consecutive records `r₀` (measurement `j−1`) and `r₁` (measurement `j`).
Units: s. -/
noncomputable def timeStep (r₀ r₁ : TemperatureRecord) : ℝ := r₁.time - r₀.time

/-- Rise `ΔT_IC = T_IC,j − T_IC,j−1` of the IC water temperature over the
interval — the numerator of the left-hand side of equation (5).  Units: °C
(a difference, hence equally K). -/
noncomputable def innerTempRise (r₀ r₁ : TemperatureRecord) : ℝ :=
  r₁.innerTemp - r₀.innerTemp

/-- Average `T̄_IC` of the IC water temperature during the interval
` t_{j−1}` to `t_j` (equation (5) text: "`T̄` are the average temperatures at
each cylinder during the interval"), read as the arithmetic mean of the two
endpoint records.  Units: °C. -/
noncomputable def averageInnerTemp (r₀ r₁ : TemperatureRecord) : ℝ :=
  (r₀.innerTemp + r₁.innerTemp) / 2

/-- Average `T̄_OC` of the OC water temperature during the interval.  Units:
°C. -/
noncomputable def averageOuterTemp (r₀ r₁ : TemperatureRecord) : ℝ :=
  (r₀.outerTemp + r₁.outerTemp) / 2

/-- The right-hand side of equation (5): the interval-averaged temperature
difference `T̄_OC − T̄_IC` — the abscissa of the C5 graph.  Units: °C (a
difference, hence equally K). -/
noncomputable def averageTempDifference (r₀ r₁ : TemperatureRecord) : ℝ :=
  averageOuterTemp r₀ r₁ - averageInnerTemp r₀ r₁

/-- The left-hand side of equation (5): the finite-difference heating rate
`(T_IC,j − T_IC,j−1) / (t_j − t_{j−1})` of the IC water — the ordinate of the
C5 graph.  Units: °C/s. -/
noncomputable def finiteDifferenceRate (r₀ r₁ : TemperatureRecord) : ℝ :=
  innerTempRise r₀ r₁ / timeStep r₀ r₁

/-- **C5 graph readout.**  The slope `k` of the C5 proportionality graph
(equation (5): the rate is proportional to the average difference), read off a
plotted interval as ordinate over abscissa,
`k = [(T_IC,j − T_IC,j−1)/(t_j − t_{j−1})] / (T̄_OC − T̄_IC)`.
Units: s⁻¹ (i.e. (°C/s)/°C). -/
noncomputable def c5GraphSlope (r₀ r₁ : TemperatureRecord) : ℝ :=
  finiteDifferenceRate r₀ r₁ / averageTempDifference r₀ r₁

/-! ## Governing laws: equation (4), IC-water calorimetry, and equation (6) -/

/-- Governing laws of the E1-C6 heat-exchange model over one measurement
interval `t_{j−1} → t_j`, as equations constraining the heat `ΔQ` received by
the IC water through the acrylic wall.  `R_Th` is the effective thermal
resistance of the wall (K/W), `m` the mass of the IC water (kg), and `c_w`
the specific heat capacity of water (J/(kg·K)).  Every field is a law stated
in or implied by the problem text; no field mentions the requested value of
`R_Th` beyond the laws that determine it. -/
structure IntervalHeatExchange (R_Th m c_w : ℝ) (r₀ r₁ : TemperatureRecord) where
  /-- The heat `ΔQ` "received by the water in the IC through the wall during
  the time interval `Δt`" (equation (4) text, page 12).  Units: J. -/
  heatReceived : ℝ
  /-- **Equation (4) of the exam (page 12)** in finite-interval form with the
  interval-averaged difference of equation (5): the wall delivers
  `ΔQ = (T̄_OC − T̄_IC) / R_Th · Δt`. -/
  heat_flow_model :
    heatReceived = averageTempDifference r₀ r₁ / R_Th * timeStep r₀ r₁
  /-- **Calorimetry of the IC water** (the modeling content of "ignore the
  heat capacity of the apparatus where instructed", page 13): the received
  heat raises the IC water temperature,
  `ΔQ = m_IC · c_w · (T_IC,j − T_IC,j−1)`. -/
  calorimetry_ic_water : heatReceived = m * c_w * innerTempRise r₀ r₁

/-- **Fourier's law for radial heat conduction through a slim cylindrical
wall, equation (6) of the exam (pages 13–14):** at every distance `r` from the
axis of the cylinder, `dQ/dt = −λ·A·dT/dr`, where `A` is the area of the wall
(at radius `r`), `λ` the thermal conductivity of the wall material, and
`dT/dr` the radial temperature gradient.  This is the shared Part-C governing
law of the *later* route (C7 determines `λ` from equations (4) and (6)); it is
recorded here for completeness of the setup and is **not** a hypothesis of the
C6 target.  The predicate unfolds to the pointwise equation, so any hypothesis
of this form can be eliminated to usable equations.  Units: `lam` in
W/(m·K), `wallArea r` in m², `heatFlowRate` in W, `tempGradient` in K/m. -/
def RadialFourierConduction (lam : ℝ) (wallArea : ℝ → ℝ)
    (heatFlowRate tempGradient : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, heatFlowRate r = -lam * wallArea r * tempGradient r

/-- Lateral area of the cylindrical wall at distance `r` from the axis over
the wetted height `L` (Figure 17 geometry behind the area `A` of equation
(6), page 14: "`A` is the area of the wall … `r` denotes the distance from the
axis of the cylinder").  Recorded for the C7 route; it does not enter the C6
target.  Units: m². -/
noncomputable def cylindricalWallLateralArea (r L : ℝ) : ℝ := 2 * Real.pi * r * L

/-! ## Derived bridges (proved in the prover stage) -/

/-- **Combined interval equation.**  The two law fields eliminate the heat
`ΔQ`: the IC water's calorimetric energy gain equals the wall heat flow of
equation (4),
`m_IC · c_w · ΔT_IC = (T̄_OC − T̄_IC) / R_Th · Δt`.  Proof route:
`← calorimetry_ic_water`, then `heat_flow_model`. -/
theorem ic_water_heating_eq_wall_flow {R_Th m c_w : ℝ} {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th m c_w r₀ r₁) :
    m * c_w * innerTempRise r₀ r₁
      = averageTempDifference r₀ r₁ / R_Th * timeStep r₀ r₁ := by
  rw [← E.calorimetry_ic_water]; exact E.heat_flow_model

/-- **C5 content, derived inline** (previous-part dependency E1-C5, policy
`derive_inline_from_problem_only_material`): equation (5) with the
proportionality constant identified.  On an interval with positive time step,
the finite-difference heating rate of the IC water is the physical slope
`1 / (m_IC · c_w · R_Th)` times the interval-averaged temperature difference —
the C5 graph is the proportionality line through the origin with that slope.
Proof route: `ic_water_heating_eq_wall_flow`, then divide by
`0 < timeStep r₀ r₁` and by `0 < m · c_w · R_Th` and rearrange. -/
theorem finiteDifferenceRate_eq_physical_slope {R_Th m c_w : ℝ}
    {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th m c_w r₀ r₁)
    (hm : 0 < m) (hc : 0 < c_w) (hR : 0 < R_Th)
    (hstep : 0 < timeStep r₀ r₁) :
    finiteDifferenceRate r₀ r₁
      = (1 / (m * c_w * R_Th)) * averageTempDifference r₀ r₁ := by
  have h := ic_water_heating_eq_wall_flow E
  have hstep' : timeStep r₀ r₁ ≠ 0 := ne_of_gt hstep
  have hR' : R_Th ≠ 0 := ne_of_gt hR
  have hmc' : m * c_w ≠ 0 := ne_of_gt (mul_pos hm hc)
  have hmcR' : m * c_w * R_Th ≠ 0 := ne_of_gt (mul_pos (mul_pos hm hc) hR)
  field_simp at h
  unfold finiteDifferenceRate
  field_simp
  linear_combination h

/-- **C5-graph slope identification.**  The slope `k` read off the C5 graph
from a plotted interval with nonzero abscissa equals the physical slope
`1 / (m_IC · c_w · R_Th)`.  Proof route:
`finiteDifferenceRate_eq_physical_slope`, then cancel the nonzero
`averageTempDifference r₀ r₁` in `c5GraphSlope`. -/
theorem c5GraphSlope_eq_physical {R_Th m c_w : ℝ} {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th m c_w r₀ r₁)
    (hm : 0 < m) (hc : 0 < c_w) (hR : 0 < R_Th)
    (hstep : 0 < timeStep r₀ r₁) (hgap : averageTempDifference r₀ r₁ ≠ 0) :
    c5GraphSlope r₀ r₁ = 1 / (m * c_w * R_Th) := by
  unfold c5GraphSlope
  rw [finiteDifferenceRate_eq_physical_slope E hm hc hR hstep,
    mul_div_cancel_right₀ _ hgap]

/-! ## Raw end-to-end candidate quantity (definition only; correctness is
proved in the target theorem below) -/

/-- Raw end-to-end quantity requested as the effective wall thermal
resistance: from the C5-graph slope `k`, the Figure-17 IC inner diameter `d`,
the procedure fill level `h = 10 cm` (via `icWaterMass`), and the water
constants `ρ_w`, `c_w`, `R_Th = 1 / (m_IC · c_w · k)`.  Units: K/W. -/
noncomputable def candidateThermalResistance (ρ_w c_w d k : ℝ) : ℝ :=
  1 / (icWaterMass ρ_w d * c_w * k)

/-- Naming expansion of the candidate (unfolds the geometry/mass chain): the
denominator is `ρ_w · (π·(d/2)² · h_IC) · c_w · k` with `h_IC = 10 cm`. -/
theorem candidateThermalResistance_eq (ρ_w c_w d k : ℝ) :
    candidateThermalResistance ρ_w c_w d k
      = 1 / (ρ_w * (Real.pi * (d / 2) ^ 2 * icWaterLevelHeight) * c_w * k) :=
  rfl

/-! ## Target: the effective wall thermal resistance from the C5 graph -/

/-- **E1-C6 main target** (blueprint `thm:physics:ipho_2026_e1_c6:target`).
For a C1 measurement interval on the heating branch of the Part-C run (the OC
water, initially at `65 °C`, stays warmer than the IC water, so
`0 < T̄_OC − T̄_IC`, and the stopwatch runs forward, `0 < Δt`), obeying
equation (4) and the IC-water calorimetry, with positive water density,
specific heat, IC inner diameter, and wall resistance, the effective thermal
resistance of the wall is determined by the C5-graph slope readout `k` as

```
R_Th = 1 / (m_IC · c_w · k) = candidateThermalResistance ρ_w c_w d k.
```

Proof route: `c5GraphSlope_eq_physical` gives `k = 1 / (m_IC · c_w · R_Th)`
with `m_IC = icWaterMass ρ_w d > 0` (`icWaterMass_pos`); solve for `R_Th`,
using `0 < m_IC · c_w · R_Th` for the inversions. -/
theorem thermalResistance_eq_candidate {R_Th ρ_w c_w d : ℝ}
    {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th (icWaterMass ρ_w d) c_w r₀ r₁)
    (hρ : 0 < ρ_w) (hc : 0 < c_w) (hd : 0 < d) (hR : 0 < R_Th)
    (hstep : 0 < timeStep r₀ r₁) (hgap : 0 < averageTempDifference r₀ r₁) :
    R_Th = candidateThermalResistance ρ_w c_w d (c5GraphSlope r₀ r₁) := by
  have hm : (0:ℝ) < icWaterMass ρ_w d := icWaterMass_pos hρ hd
  have hmc : (0:ℝ) < icWaterMass ρ_w d * c_w := mul_pos hm hc
  have hmcR : (0:ℝ) < icWaterMass ρ_w d * c_w * R_Th := mul_pos hmc hR
  have hmcR' : icWaterMass ρ_w d * c_w * R_Th ≠ 0 := ne_of_gt hmcR
  have hk := c5GraphSlope_eq_physical E hm hc hR hstep (ne_of_gt hgap)
  -- The readout slope times `m_IC · c_w · R_Th` is one.
  have h1 : c5GraphSlope r₀ r₁ * (icWaterMass ρ_w d * c_w * R_Th) = 1 := by
    rw [hk]; field_simp
  -- Equivalently `R_Th · (m_IC · c_w · k) = 1`.
  have h2 : R_Th * (icWaterMass ρ_w d * c_w * c5GraphSlope r₀ r₁) = 1 := by
    linear_combination h1
  have hD : icWaterMass ρ_w d * c_w * c5GraphSlope r₀ r₁ ≠ 0 :=
    ne_of_gt (by rw [hk]; positivity)
  unfold candidateThermalResistance
  rw [eq_div_iff hD]
  exact h2

/-- **Heating-branch certificate (heat direction).**  On the heating branch
(`0 < T̄_OC − T̄_IC`, positive time step, positive constants) the heat
received by the IC water is positive: heat flows from the OC through the wall
*into* the IC.  Proof route: `heat_flow_model`, then positivity of each
factor. -/
theorem heatReceived_pos {R_Th m c_w : ℝ} {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th m c_w r₀ r₁)
    (hR : 0 < R_Th) (hstep : 0 < timeStep r₀ r₁)
    (hgap : 0 < averageTempDifference r₀ r₁) :
    0 < E.heatReceived := by
  rw [E.heat_flow_model]
  positivity

/-- **Heating-branch certificate (IC warms).**  The finite-difference heating
rate of the IC water is positive: `T_IC` rises during the run (equation (5)'s
ordinate is positive on the heating branch).  Proof route:
`finiteDifferenceRate_eq_physical_slope`, then positivity. -/
theorem finiteDifferenceRate_pos {R_Th m c_w : ℝ} {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th m c_w r₀ r₁)
    (hm : 0 < m) (hc : 0 < c_w) (hR : 0 < R_Th)
    (hstep : 0 < timeStep r₀ r₁) (hgap : 0 < averageTempDifference r₀ r₁) :
    0 < finiteDifferenceRate r₀ r₁ := by
  rw [finiteDifferenceRate_eq_physical_slope E hm hc hR hstep]
  positivity

/-- **Heating-branch certificate (C5 slope sign).**  The slope read off the
C5 graph is positive, so the graph readout can be inverted to a positive
resistance.  Proof route: `c5GraphSlope_eq_physical` (with
`hgap.ne'` for the nonzero abscissa), then positivity of
`1 / (m · c_w · R_Th)`. -/
theorem c5GraphSlope_pos {R_Th m c_w : ℝ} {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th m c_w r₀ r₁)
    (hm : 0 < m) (hc : 0 < c_w) (hR : 0 < R_Th)
    (hstep : 0 < timeStep r₀ r₁) (hgap : 0 < averageTempDifference r₀ r₁) :
    0 < c5GraphSlope r₀ r₁ := by
  rw [c5GraphSlope_eq_physical E hm hc hR hstep (ne_of_gt hgap)]
  positivity

/-- **Sanity certificate.**  The determined effective wall thermal resistance
is strictly positive — as a resistance of a physical wall must be.  Proof
route: `thermalResistance_eq_candidate`, then `candidateThermalResistance` is
`1 / (positive)` via `icWaterMass_pos` and `c5GraphSlope_pos`. -/
theorem determined_resistance_pos {R_Th ρ_w c_w d : ℝ}
    {r₀ r₁ : TemperatureRecord}
    (E : IntervalHeatExchange R_Th (icWaterMass ρ_w d) c_w r₀ r₁)
    (hρ : 0 < ρ_w) (hc : 0 < c_w) (hd : 0 < d) (hR : 0 < R_Th)
    (hstep : 0 < timeStep r₀ r₁) (hgap : 0 < averageTempDifference r₀ r₁) :
    0 < candidateThermalResistance ρ_w c_w d (c5GraphSlope r₀ r₁) := by
  rw [← thermalResistance_eq_candidate E hρ hc hd hR hstep hgap]
  exact hR

end IPhO2026.E1C6
