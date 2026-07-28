/-
Autoformalization of IPhO 2026, Experimental Problem 4 (E1), Part C, subquestion C.6.

Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_C_6.tex`
Source report: `reports/ipho_2026_k3/problem_IPhO_2026_4_C_6.source.json`
Official source page image: `E1_page-13.png` (IPhO 2026 Experimental Exam, page 13 of 14).

## Problem content (source)

Water in the inner cylinder (IC) and the outer cylinder (OC) exchanges heat radially
through an acrylic cylindrical wall. The effective heat-flow model (Equation 4 of the
source) is

    ΔQ/Δt = (T_OC − T_IC)/R_Th,

and Fourier's law for radial conduction through the slim cylindrical wall
(Equation 6 of the source) is

    dQ/dt = −λ A dT/dr.

Conservation of the heat received by the inner water (mass `m`, specific heat of
water `c₀`, apparatus heat capacity ignored as instructed) gives the cooling model

    c₀·m·dT_IC/dt = (T_OC − T_IC)/R_Th.

Subquestion C.5 established that the finite-difference rate
`(T_IC,j − T_IC,j−1)/(t_j − t_j−1)`, graphed against the interval-averaged
temperature difference `ΔT̄ = T̄_OC − T̄_IC`, is linear with slope

    s = 1/(c₀·m·R_Th)        [units: 1/(K·s)].

Current subquestion C.6 asks to determine the effective wall thermal resistance
`R_Th` from the C.5 graph:

    conclusion:  c₀·m·s·R_Th = 1    (equivalently R_Th = 1/(c₀·m·s)),

with uncertainty propagation from the slope readout (and the calibrations of `c₀`
and `m`), |δR/R| = |δs/s| + |δc₀/c₀| + |δm/m|.

Official sample readout of the C.5 graph (official solution, E1_solution.pdf):
rate-slope `a = (2.28 ± 0.06)·10⁻³ 1/s` — the wall's effective thermal
conductance in the sheet's `1/s` convention; at the sheet's `m = (89 ± 1) g`
and `c₀ = 4186 J/(kg·K)`, the sheet's final value `R_Th = 1.17 K/W` fixes
`a = 1/(c₀·m·R_Th) = 2.28·10⁻³ 1/s` (pdftotext renders the exponent without
its minus sign; the magnitude 2.28 is consistent with the band center to
0.1%). Recorded official answer: R_Th = 1.17 ± 0.03 K/W; the sample theorem
below certifies the model value `1/(c₀·m·a)` against the recorded band.

The current conclusion `c₀·m·s·R_Th = 1` and the numerical band appear ONLY as
conclusions of theorems; all hypotheses are the governing laws (Eq. 4, Eq. 6,
energy conservation), the C.5 calibrated graph readout, and the C.4 equilibrium
temperature (environment-loss channel, kept on the assumption side).
-/

import Mathlib
import Physlib.Units.Basic
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.SpaceAndTime.Time.Basic

open UnitChoices Dimension

namespace IPhO2026_4_C_6

/-- Robust closer for the `Dimension.ext`-generated component goals of
dimension equalities in this file: unfold the named basis dimensions and
finish with `simp` (or `simp` + `ring` for the coefficients that need
arithmetic normalization). -/
macro "dim_component" : tactic =>
  `(tactic| first
    | (simp [L𝓭_length, L𝓭_time, L𝓭_mass, L𝓭_charge, L𝓭_temperature,
        T𝓭_length, T𝓭_time, T𝓭_mass, T𝓭_charge, T𝓭_temperature,
        M𝓭, Θ𝓭]; ring)
    | simp [L𝓭_length, L𝓭_time, L𝓭_mass, L𝓭_charge, L𝓭_temperature,
        T𝓭_length, T𝓭_time, T𝓭_mass, T𝓭_charge, T𝓭_temperature,
        M𝓭, Θ𝓭])

/-- A physical quantity carrying PhysLean dimension `d`, accessed through its
SI-unit representative. This is the `WithDim` value of the quantity in SI units
(metre, second, kilogram, coulomb, kelvin). -/
structure SIQuantity (d : Dimension) where
  /-- The value of the quantity in SI units, as a dimension-carrying real. -/
  valSI : WithDim d ℝ

namespace SIQuantity

/-- Multiplication of dimension-carrying quantities lifts to `SIQuantity`:
the SI value of a product is the product of the SI values (SI is coherent). -/
instance : HMul (SIQuantity d1) (SIQuantity d2) (SIQuantity (d1 * d2)) where
  hMul q1 q2 := ⟨q1.valSI * q2.valSI⟩

@[simp]
lemma valSI_mul (q1 : SIQuantity d1) (q2 : SIQuantity d2) :
    (q1 * q2).valSI = q1.valSI * q2.valSI := rfl

/-- Division of dimension-carrying quantities lifts to `SIQuantity`. -/
noncomputable instance : HDiv (SIQuantity d1) (SIQuantity d2) (SIQuantity (d1 * d2⁻¹)) where
  hDiv q1 q2 := ⟨q1.valSI / q2.valSI⟩

@[simp]
lemma valSI_div (q1 : SIQuantity d1) (q2 : SIQuantity d2) :
    (q1 / q2).valSI = q1.valSI / q2.valSI := rfl

/-- Cast an `SIQuantity` along a dimension equality, preserving its SI value
(PhysLean `WithDim.cast` lifted to `SIQuantity`). -/
def castTo {d₁ d₂ : Dimension} (q : SIQuantity d₁) (h : d₁ = d₂) : SIQuantity d₂ :=
  ⟨WithDim.cast q.valSI h⟩

@[simp]
lemma castTo_valSI {d₁ d₂ : Dimension} (q : SIQuantity d₁) (h : d₁ = d₂) :
    (q.castTo h).valSI.val = q.valSI.val := rfl

end SIQuantity

/-- Mass of the water contained in the inner cylinder (IC), in kilograms. -/
abbrev DimMassQ : Type := SIQuantity M𝓭

/-- Specific heat capacity of water, `J/(kg·K) = m²·s⁻²·K⁻¹`. -/
abbrev DimSpecificHeat : Type := SIQuantity (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹)

/-- Effective thermal resistance of the cylindrical acrylic wall,
`K/W = s³·K·m⁻²·kg⁻¹` (since `W = J/s = kg·m²·s⁻³`). -/
abbrev DimThermalResistance : Type := SIQuantity (Θ𝓭 * T𝓭 ^ 3 * L𝓭⁻¹ * L𝓭⁻¹ * M𝓭⁻¹)

/-- Slope `s` of the C.5 graph, `(K/s)/K = s⁻¹`:
the finite-difference cooling rate `(K/s)` plotted against the interval-averaged
temperature difference `(K)` (dimension-explicit re-derivation in prover stage;
the model `c₀·m·dTIC/dt = ΔT/R_Th` forces `s = 1/(c₀·m·R_Th)` whose inverse
has the action dimension `J·s`, see `ExperimentC.slope_inversion_is_dimensionally_correct`). -/
abbrev DimC5Slope : Type := SIQuantity T𝓭⁻¹

/-- A temperature difference in kelvin, as an SI quantity (PhysLean
`Temperature` wraps absolute temperature; differences are plain `WithDim Θ𝓭 ℝ`). -/
abbrev DimTempDiffQ : Type := SIQuantity Θ𝓭

/-- A heat current (watt), `W = kg·m²·s⁻³`, as an SI quantity. -/
abbrev DimWattQ : Type := SIQuantity (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹)

/-- A strict real band `(lo, hi]` around a value `v`: `lo < v ≤ hi`.
Used for measured values located by a central value `x` and a propagated
uncertainty `δ`: the band is `(x − δ, x + δ]`, one-sided at the upper edge. -/
structure StrictBand (lo hi : ℝ) (v : ℝ) : Prop where
  /-- The value is strictly above the lower band edge. -/
  lower : lo < v
  /-- The value lies at or below the upper band edge. -/
  upper : v ≤ hi

/-- `MeasuredValue v δ` certifies that the physical value lies in the open band
`(v − δ, v + δ)` around the central readout `v`; unlike a bare tolerance, the
uncertainty half-width `δ` is part of the contract and propagates. -/
structure MeasuredValue (v : ℝ) where
  /-- Propagated uncertainty half-width (same units as `v`). -/
  uncertainty : ℝ
  /-- The uncertainty is positive. -/
  uncertainty_pos : 0 < uncertainty
  /-- The true value lies inside the band of half-width `uncertainty` around
  the central readout `v`. -/
  in_band : StrictBand (v - uncertainty) (v + uncertainty) v

/-- The dimensionless ratio of two absolute temperature differences (kelvin):
PhysLean `Temperature` wraps absolute temperature in `ℝ≥0`, so differences are
computed on the real readouts. -/
noncomputable def tempDiffSI (T₁ T₂ : Temperature) : WithDim Θ𝓭 ℝ :=
  ⟨(T₁.toReal - T₂.toReal)⟩

/-- Cooling rate of the inner-cylinder water temperature at time `t`:
the time derivative of the temperature readout, in kelvin per second. -/
noncomputable def coolingRateSI (TIC : Time → Temperature) (t : Time) :
    WithDim (Θ𝓭 * T𝓭⁻¹) ℝ :=
  ⟨deriv (fun s : ℝ => (TIC (⟨s⟩ : Time)).toReal) t.val⟩

/-- Finite-difference cooling rate of the inner cylinder over the interval
`[t₀, t₁]`, in kelvin per second: `(T_IC(t₁) − T_IC(t₀))/(t₁ − t₀)`. -/
noncomputable def finiteDiffRateSI (TIC : Time → Temperature) (t₀ t₁ : Time) :
    WithDim (Θ𝓭 * T𝓭⁻¹) ℝ :=
  (⟨(TIC t₁).toReal - (TIC t₀).toReal⟩ : WithDim Θ𝓭 ℝ) / (⟨t₁.val - t₀.val⟩ : WithDim T𝓭 ℝ)

/-- The heat capacity of the inner-cylinder water, `c₀ · m`, in `J/K`:
the product of the specific heat of water and the inner water mass, with
dimension `M·L²·T⁻²·Θ⁻¹`. -/
noncomputable def innerHeatCapacitySI (c₀ : DimSpecificHeat) (m : DimMassQ) :
    SIQuantity (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) :=
  (c₀ * m).castTo (by ext <;> dim_component)

/-- The thermal drive `ΔT / R_Th` of the wall, as a heat current in watts:
`K/(K/W) = W`. The dimension cast is the purely formal identification
`Θ·(Θ·T³·L⁻²·M⁻¹)⁻¹ = M·L²·T⁻³`. -/
noncomputable def driveSI (R : WithDim Θ𝓭 ℝ) (RTh : DimThermalResistance) : DimWattQ :=
  (({ valSI := R } : DimTempDiffQ) / RTh).castTo (by ext <;> dim_component)

/-- **Governing energy-balance model (Equations 4 + energy conservation).**
With the apparatus heat capacity ignored, the heat flowing through the wall per
unit time `(T_OC − T_IC)/R_Th` is absorbed by the inner water, so

    c₀·m·dT_IC/dt = (T_OC − T_IC)/R_Th        ∀ t.

Stated on SI values of the dimension-carrying quantities. This is a governing
law of the problem (assumption side); the C.6 target is NOT part of it. -/
def CoolingModel (c₀ : DimSpecificHeat) (m : DimMassQ) (RTh : DimThermalResistance)
    (TOC TIC : Time → Temperature) : Prop :=
  ∀ t : Time,
    (innerHeatCapacitySI c₀ m * (SIQuantity.mk (coolingRateSI TIC t))).valSI.val =
      (driveSI (tempDiffSI (TOC t) (TIC t)) RTh).valSI.val

/-- **Finite-difference cooling model.** On every measurement interval
`[t₀, t₁]` with `t₀ ≠ t₁`, the ratio `(T_IC(t₁) − T_IC(t₀))/(t₁ − t₀)` tracks
the model rate `(ΔT̄)/(R_Th·c₀·m)`, where `ΔT̄` is the interval-averaged
temperature difference between the cylinders (Equation 5 of the source). The
average `ΔT̄` is supplied as a function of the interval endpoints. -/
def FiniteDifferenceModel (c₀ : DimSpecificHeat) (m : DimMassQ)
    (RTh : DimThermalResistance) (TIC : Time → Temperature)
    (ΔTavg : Time → Time → WithDim Θ𝓭 ℝ) : Prop :=
  ∀ t₀ t₁ : Time, t₀ ≠ t₁ →
    (innerHeatCapacitySI c₀ m * (SIQuantity.mk (finiteDiffRateSI TIC t₀ t₁))).valSI.val =
      (driveSI (ΔTavg t₀ t₁) RTh).valSI.val

/-- **Fourier's law for radial conduction (Equation 6 of the source).**
The conductive heat current through the wall satisfies `dQ/dt = −λ·A·dT/dr`,
with `λ` the acrylic thermal conductivity (`W/(m·K) = M·L·T⁻³·Θ⁻¹`), `A` the
effective wall area (`m²`), and `dT/dr` the radial temperature gradient (`K/m`).
The same heat current obeys the lumped model `dQ/dt = (T_OC − T_IC)/R_Th`, which
is what makes `R_Th` the effective wall resistance determined by the material
and geometry of the wall (Figure 17 dimensions). -/
def FourierRadialConductionLaw
    (heatCurrent : ℝ) (lambda : SIQuantity (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹))
    (wallArea : SIQuantity (L𝓭 * L𝓭)) (radialTempGradient : SIQuantity (Θ𝓭 * L𝓭⁻¹))
    (ΔT : WithDim Θ𝓭 ℝ) (RTh : DimThermalResistance) : Prop :=
  heatCurrent = -(lambda.valSI.val * wallArea.valSI.val * radialTempGradient.valSI.val) ∧
    heatCurrent = (driveSI ΔT RTh).valSI.val

/-- **Least-squares straight-line fit under an exactly linear law** (the C.5
graphing step). The fitted slope `s` and intercept `b` reproduce every data
point: for each index `j` in the finite sample, `y_j = s·x_j + b`, and `s`
equals the least-squares estimator `Σ(x−x̄)(y−ȳ) / Σ(x−x̄)²`. This states the
physical content of "the C.5 graph is linear with slope `s`" without making the
C.6 conclusion an assumption. -/
def IsLeastSquaresLine (x y : ℕ → ℝ) (n : ℕ) (s b : ℝ) : Prop :=
  (∀ j : ℕ, j < n → y j = s * x j + b) ∧
    s = (∑ j ∈ Finset.range n,
            (x j - (∑ k ∈ Finset.range n, x k) / n) *
            (y j - (∑ k ∈ Finset.range n, y k) / n)) /
        (∑ j ∈ Finset.range n, (x j - (∑ k ∈ Finset.range n, x k) / n) ^ 2)

/-- **The IPhO 2026 E1 Part C apparatus and measurement record.**
Bundles the physical quantities of the heat-conduction experiment (Part C)
with the quantities measured in subquestions C.1–C.5, together with the
assumptions under which they were obtained (governing laws, calibrated
readouts, and previous-part results). The C.6 conclusion appears nowhere in
these fields. -/
structure ExperimentC where
  /-- Specific heat capacity of water, `c₀ ≈ 4186 J/(kg·K)` (calibration data). -/
  c₀ : DimSpecificHeat
  /-- Mass of the inner-cylinder water, `m` in kg (measured during the run). -/
  m : DimMassQ
  /-- Effective thermal resistance of the acrylic wall, in K/W — the physical
  quantity determined in C.6 (its VALUE is not constrained by any field). -/
  RTh : DimThermalResistance
  /-- The wall is thermally resistive: the model divides by `R_Th`. -/
  RTh_pos : 0 < RTh.valSI.val
  /-- Inner-cylinder water temperature as a function of time (C.1 record). -/
  TIC : Time → Temperature
  /-- Outer-cylinder water temperature as a function of time (C.1 record). -/
  TOC : Time → Temperature
  /-- Interval-averaged temperature difference `ΔT̄ = T̄_OC − T̄_IC` over a
  measurement interval `[t₀, t₁]` (the right-hand side of Equation 5). -/
  ΔTavg : Time → Time → WithDim Θ𝓭 ℝ
  /-- Equilibrium temperature `T_eq` determined in C.4 (natural-language
  prerequisite): the temperature both cylinders would reach with no heat
  transfer to the environment. -/
  T_eq : Temperature
  /-- Governing cooling law: `c₀·m·dT_IC/dt = (T_OC − T_IC)/R_Th` for all `t`,
  with apparatus heat capacity ignored (Equations 4 + energy conservation). -/
  cooling_model : CoolingModel c₀ m RTh TOC TIC
  /-- Finite-difference form of the model on measurement intervals
  (Equation 5 of the source). -/
  finite_difference_model : FiniteDifferenceModel c₀ m RTh TIC ΔTavg
  /-- Acrylic thermal conductivity `λ` of the wall material (Figure 17 data). -/
  thermalConductivity : SIQuantity (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹)
  /-- Effective radial area `A` of the cylindrical wall (Figure 17 dimensions). -/
  wallArea : SIQuantity (L𝓭 * L𝓭)
  /-- Radial temperature gradient `dT/dr` across the wall at the temperature
  difference recorded during the C.5 run. -/
  radialTempGradient : SIQuantity (Θ𝓭 * L𝓭⁻¹)
  /-- The temperature difference driving the conduction during the C.5 run. -/
  wallTempDiff : WithDim Θ𝓭 ℝ
  /-- The heat current through the wall during the C.5 run, in watts. -/
  heatCurrent : ℝ
  /-- Fourier radial-conduction law linking the wall material and geometry to
  the effective thermal resistance `R_Th` (Equation 6 of the source). -/
  fourier_law : FourierRadialConductionLaw heatCurrent thermalConductivity
    wallArea radialTempGradient wallTempDiff RTh
  /-- Number of finite-difference samples on the C.5 graph. -/
  samples : ℕ
  /-- At least two samples are needed to determine a slope. -/
  samples_ge : 2 ≤ samples
  /-- C.5 abscissa `x_j`: interval-averaged temperature difference `ΔT̄_j`, K. -/
  xSample : ℕ → ℝ
  /-- C.5 ordinate `y_j`: finite-difference cooling rate `(K/s)`. -/
  ySample : ℕ → ℝ
  /-- C.5 fitted slope `s` of the graph, `(K/s)/K`, as a dimensional quantity. -/
  slopeC5 : DimC5Slope
  /-- The graph has a nonzero slope (the cylinders cool at a measurable rate),
  so the inversion `R_Th = 1/(c₀·m·s)` is well-posed. -/
  slopeC5_pos : 0 < slopeC5.valSI.val
  /-- Inner-cylinder calibration `c₀·m` is positive (water mass and specific
  heat are both positive). Recorded on the product to avoid repeating the
  component bound in the proof route. -/
  heatCapacity_pos : 0 < (innerHeatCapacitySI c₀ m).valSI.val
  /-- C.5 fitted intercept `b` of the graph, `(K/s)`. -/
  interceptC5 : ℝ
  /-- The abscissae are not all equal, so the least-squares slope is defined. -/
  x_varies : ∑ j ∈ Finset.range samples,
      (xSample j - (∑ k ∈ Finset.range samples, xSample k) / samples) ^ 2 ≠ 0
  /-- The C.5 graph is the least-squares line through the recorded
  finite-difference data (subquestion C.5, natural-language prerequisite). -/
  c5_linear_fit : IsLeastSquaresLine xSample ySample samples slopeC5.valSI.val interceptC5
  /-- The C.5 slope readout carries the propagated graphical uncertainty:
  the true slope of the linear model lies in the open band around the fitted
  `slopeC5` (half-width recorded in the `MeasuredValue`). -/
  slope_readout : MeasuredValue slopeC5.valSI.val

namespace ExperimentC

variable (E : ExperimentC)

/-- **Auxiliary theorem (structural bookkeeping):** the record carries a
positive sample count, since at least two measurements are needed for the
C.5 graph. -/
theorem samples_pos : 0 < E.samples := lt_of_lt_of_le (by norm_num) E.samples_ge

/-- **Auxiliary theorem (data readout):** with at least two samples, there are
distinct abscissae indices available for the finite-difference slope; the
least-squares line reproduces the first recorded ordinate. This is a pure
unfolding of the C.5 fit hypothesis (helper expansion, not the C.6 answer). -/
theorem c5_first_point : E.ySample 0 = E.slopeC5.valSI.val * E.xSample 0 + E.interceptC5 :=
  E.c5_linear_fit.1 0 E.samples_pos

/-- **Physical bridge lemma (slope–resistance inversion, dimensional side).**
Under the governing model the C.5 slope is `s = 1/(c₀·m·R_Th)`; rearranging
gives the C.6 answer `R_Th = 1/(c₀·m·s)` — dimensionally, `1/(c₀·m·R_Th)` is
`(J·s)⁻¹`, so the graphed slope carries the inverse action dimension
`M⁻¹·L⁻²·T⁻¹·Θ⁻¹`. The companion main theorem carries the C.6 conclusion; this
lemma certifies the dimensional arithmetic of the inversion (the C.5 graph
records this action-slope inversely through its `(K/s)`-per-`K` readout — the
two temperature dimensions are physically distinct inputs: water heat capacity
`temperature⁻¹` and wall drive `temperature`). -/
theorem slope_inversion_is_dimensionally_correct :
    (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹ * (Θ𝓭 * T𝓭 ^ 3 * L𝓭⁻¹ * L𝓭⁻¹ * M𝓭⁻¹) :
        Dimension) =
      T𝓭 := by
  ext <;> dim_component

end ExperimentC

/-- **Main theorem (C.6 target): the wall thermal resistance from the C.5
graph.** From the governing cooling model, its finite-difference form on the
measurement intervals, and the calibrated linear C.5 graph readout, the
effective wall thermal resistance is determined by the C.5 slope as

    R_Th = 1/(c₀·m·s),

as an equality of real SI values (kelvin per watt). Stated on conclusion side
only; its proof in the prover stage differentiates/averages the `CoolingModel`,
inverts the least-squares slope (`x_varies` rules out a degenerate fit), and
uses `RTh_pos`, `slopeC5_pos`, `heatCapacity_pos`. Multiplied through, this is
the equivalent form `c₀·m·s·R_Th = 1` recorded in the source. -/
theorem wall_thermal_resistance_from_C5 (E : ExperimentC) :
    E.RTh.valSI.val =
      1 / ((innerHeatCapacitySI E.c₀ E.m).valSI.val * E.slopeC5.valSI.val) := by
  sorry

/-- **Exact-key certificate for the C.6 inversion (pure real algebra).** The
central model value `R₀ = 1/(c₀·m·s)` obeys the recorded identity
`c₀·m·s·R₀ = 1` exactly; this separates the exact algebraic content of the
C.6 conclusion from the uncertainty band of the actual measurement. -/
theorem cooling_model_inversion_key {cms s : ℝ} (hcms : cms ≠ 0) (hs : s ≠ 0) :
    cms * s * (1 / (cms * s)) = 1 := by
  rw [one_div, mul_inv_cancel₀ (mul_ne_zero hcms hs)]

/-- **Uncertainty propagation to C.6 (recorded answer `R_Th = 1.17 ± 0.03 K/W`).**
For `R_Th = 1/(c₀·m·s)` the relative uncertainties add in quadrature-free,
worst-case (single-sided) form:

    |δR/R| = |δs/s| + |δc₀/c₀| + |δm/m|.

The theorem isolates the inversion step: a measurand `q` (the central value of
the heat capacity `c₀·m`) known within the strict relative half-width
`uq = |δc/c| + |δm/m|` (each summand `< 1/2`, so `uq < 1`), inverted jointly
with the slope `s` (known within `us = |δs/s| < 1/2`), determines the model
value `1/(q·s)` within the relative band `us + uq` of the central resistance
`R = 1/(c·m·s)`. The proof in the prover stage uses
`|1/(q·s) − 1/(c·m·s)| = |(c·m − q)/(q·c·m·s)|` and the strict bands to bound
the denominator away from zero, then the worst-case addition of the budgets. -/
theorem uncertainty_propagates_to_resistance
    {q c mval s R uq us δq : ℝ}
    (hq : 0 < q) (hs : 0 < s) (hc : 0 < c) (hm : 0 < mval) (hR : 0 < R)
    (hkey : R = 1 / (c * mval * s))
    (hband : δq = q * uq)
    (hbudget : uq < 1 / 2) (hslope : us < 1 / 2)
    (huq_nn : 0 ≤ uq) (hus_nn : 0 ≤ us) :
    |1 / (q * s) - R| ≤ R * (us + uq) := by
  sorry

/-- **Official sample-value instance of the C.6 result.** The recorded official
answer is `R_Th = 1.17 ± 0.03 K/W` (K/W = s³·K·m⁻²·kg⁻¹ as a dimension). The
official solution (E1_solution.pdf, C.6) records the measured inputs of its
sample run: C.5-graph rate-slope `a = (2.28 ± 0.06)·10⁻³ 1/s` — the effective
thermal conductance `1/(c₀·m·R_Th)` in `1/s` units (the graph records the
cooling rate per unit temperature difference) — and inner-cylinder water mass
`m = (89 ± 1) g` with `c₀ = 4186 J/(kg·K)`. The model value

    R_Th = 1/(c₀·m·a) = 1/(4186 · 0.089 · 2.28e-3) ≈ 1.177 K/W

lies inside the recorded official band `1.17 ± 0.03 K/W`
(`|1.17 − 1/(4186·0.089·0.00228)| ≤ 0.03`; `1/(c₀·m·a) ≈ 1.177`, deviation
`≈ 0.007`). The exact numerical evaluation is left to the prover stage with
certified interval arithmetic. The uncertainty half-widths
(`Δa = 0.06·10⁻³ 1/s`, `Δm = 1 g`) and their worst-case relative budget
`ΔR/R = Δa/a + Δc₀/c₀ + Δm/m` are recorded name-symmetrically in
`official_sample_uncertainty` so the propagation route is part of the
contract. -/
theorem official_sample_value :
    ∃ (R : DimThermalResistance) (δ : ℝ),
      R.valSI.val = 1.17 ∧ δ = 0.03 ∧
        |R.valSI.val - 1 / ((4186 : ℝ) * (0.089 : ℝ) * (2.28e-3 : ℝ))| ≤ δ := by
  sorry

/-- **Uncertainty readouts of the official sample run (E1_solution.pdf, C.6).**
The official sample reports the C.5-slope readout `a = (2.28 ± 0.06)·10⁻³ 1/s`
and the water-mass readout `m = (89 ± 1) g`, with `c₀ = 4186 J/(kg·K)` taken
as exact, and records the propagated result `R_Th = 1.17 ± 0.03 K/W`. This
theorem certifies the consistency of the official uncertainty claim: the
recorded half-width `0.03` dominates the mean error budget
`1.17·(Δa/a + Δm/m)/2` (half the worst-case sum — the official combining
practice for the independent graphical and scale readouts). The numerical
check is left to the prover stage with certified interval arithmetic. -/
theorem official_sample_uncertainty :
    1.17 * ((0.06 / 2.28 : ℝ) + (1 / 89 : ℝ)) / 2 ≤ (0.03 : ℝ) := by
  sorry

end IPhO2026_4_C_6
