import Mathlib

/-!
# IPhO 2026 · Experiment E1-A5 — Constant-volume thermal pressure coefficient `β₀`

Autoformalization of IPhO 2026 E1-A5
(source: `reports/ipho_2026/problem_ipho_2026_e1_a5.source.json`,
problem page `ipho_2026_source/image/E1_page-9.png`,
"Part A [4.0 pt]. Isochoric (isovolumetric) process of an ideal gas").

## Physical scenario (page 9)

The experimental apparatus contains a sealed **air column (CA)** in the **inner
cylinder (IC)**.  Propylene glycol (PG) is introduced into the IC to a level
`h = 4.5 cm` and the valves **D** and **E** are closed; "this ensures that the
volume of **CA** is fixed" (procedure, page 9).  The CA obeys the ideal-gas
equation of state

```
P · V = n · R · T        (equation (1), page 9)
```

with `R` the universal gas constant.  The procedure then heats the
outer-cylinder (OC) water bath and subquestion A2 records "in a table the
pressure `P` of the CA as a function of its temperature `T`"; A3 plots the
behavior of pressure as a function of temperature.  Page 9 defines the thermal
pressure coefficient at constant volume by

```
β₀ = (1 / P₀) · (ΔP / ΔT)        (equation (2), page 9)
```

"where `P₀` is the pressure of the system at the reference temperature `T₀` as
indicated in the reference constants and values."

**Subquestion E1-A5 [0.7 pt].**  Determine the value of the coefficient `β₀`
for air.

## Reference constants and data table — availability note (answer-blind)

The numerical values of the reference pressure `P₀` and the reference
temperature `T₀` live on the "reference constants and values" sheet, and the
A2 pressure–temperature table is recorded by the student; neither is part of
the answer-blind evidence bundle (only E1 pages 9, 11–14 are available, and
none of them carries the reference sheet or a data table).  Per the
answer-blind protocol no values are guessed: `P₀`, `T₀` are abstract positive
parameters and the recorded states are arbitrary states on the isochore.
(Page 12 sets `T₀ = 273.15 K` for the *Part B* vapor reference; that value
belongs to a different setup and is not imported here.)  Once the sheet value
of `T₀` is supplied, the candidate below evaluates numerically; no target
value is assumed anywhere in this file.

## Physical model (governing laws and readouts)

1. *Sealed isochoric sample* (`IsochoricLaw.ideal_gas_law`): the PG fill to
   `h = 4.5 cm` with valves D and E closed fixes the CA volume `V` (procedure,
   page 9) and the sealed amount `n`; every recorded state `(P, T)` of the A2
   table obeys equation (1) at that same fixed `V` and `n`.  (The geometric
   form of the fixed volume, `π·(d/2)²·(H − h)` from Figure 17, is formalized
   in the E1-A1 file; on the A5 route only the fixedness and positivity of
   `V` enter.)
2. *A2/A3 readout* (`pressureSlope`): `ΔP/ΔT` is the finite-difference slope
   between two recorded states — the slope read off the A3 pressure–
   temperature graph and used in equation (2).
3. *Reference state* (`referenceState`): `P₀` is the pressure of *the same
   system* at the reference temperature `T₀`, so the reference state `(P₀, T₀)`
   lies on the same isochore (`IsochoricLaw` at the reference state).
4. *Equation (2)* (`thermalPressureCoeff`): `β₀ = (1/P₀)·(ΔP/ΔT)`.

## Current target (conclusion side only)

`thermal_pressure_coeff_eq_candidate`: for any two recorded states with
distinct temperatures on the isochore, and the reference state on the same
isochore,

```
β₀ = (1 / P₀) · (ΔP / ΔT) = 1 / T₀        (the coefficient β₀ for air),
```

carried by the raw end-to-end candidate `candidateBeta0 T₀ = 1 / T₀`; the
closed form appears only in conclusions.  Intermediate bridges:
`pressure_eq_linear_of_temperature` (the previous-part A3 content derived
inline — the A3 graph is the straight line `P = (nR/V)·T` through the origin
in absolute temperature), `pressureSlope_eq_molar_slope` (`ΔP/ΔT = nR/V` for
any recorded pair with distinct temperatures),
`thermalPressureCoeff_pair_independent` (the coefficient does not depend on
the chosen pair of table rows), and the heating-branch sanity certificates
`pressureSlope_pos`, `determined_coefficient_pos`.  A source-derived *numeric*
rounding rule can only be stated once the reference-sheet value of `T₀` is
available; see the task-result record.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
pressures in Pa, absolute temperatures in K, volume in m³, amount of substance
in mol, `R` in J/(mol·K), the slope `ΔP/ΔT` in Pa/K, and the coefficient `β₀`
in K⁻¹.

## Grounding gaps (LeanExplore, packages Mathlib + Physlib)

* Physlib `IdealGas.ideal_gas_law`
  (`Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas`) is a
  *derived* stat-mech identity in a units-less system with `R = 1`, tied to
  the microcanonical `IdealGas` Hamiltonian — not the phenomenological
  equation-of-state contract an experiment assumes.  Near miss; the law is
  stated locally as the exam does (`IsochoricLaw.ideal_gas_law`).
* No thermal-pressure-coefficient or isochoric-process API exists in
  Physlib/Mathlib (query "thermal pressure coefficient constant volume
  isochoric process" returned only unrelated near misses such as
  `CanonicalEnsemble.heatCapacity` and `NVEHamiltonian.pressure`).  Equation
  (2) is therefore stated locally as `thermalPressureCoeff`.
* No universal gas constant `R` exists in Physlib (only the axiom-backed
  Boltzmann constant `Constants.kB` in arbitrary units).  `R` is an abstract
  positive parameter — fitting, since E1-A4 is precisely the experimental
  determination of `R`.
-/

namespace IPhO2026.E1A5

/-! ## Problem data (stated values, page 9) -/

/-- Propylene-glycol fill height, `h = 4.5 cm` (procedure, page 9: "Introduce
PG into IC to `h = 4.5 cm` and close valves D and E.  This ensures that the
volume of CA is fixed.").  On the A5 route this is the setup step that makes
the process isochoric (constant `V`).  Units: metres. -/
noncomputable def pgFillHeight : ℝ := 4.5 / 100

/-- Time-averaged ambient air density in Bucaramanga, `ρ_a = 1.12 kg/m³`
(problem data, page 9).  Shared Part-A context: it drives the A1 mass
determination and does not enter the A5 route; recorded for context fidelity.
Units: kg/m³. -/
noncomputable def ambientAirDensity : ℝ := 1.12

/-- Data fact: the PG fill height is positive. -/
theorem pgFillHeight_pos : 0 < pgFillHeight := by
  unfold pgFillHeight; norm_num

/-- Data fact: the ambient air density is positive. -/
theorem ambientAirDensity_pos : 0 < ambientAirDensity := by
  unfold ambientAirDensity; norm_num

/-! ## Recorded states and the isochore -/

/-- A recorded state of the confined air column (CA) during the isochoric
heating of Part A: pressure `P` and absolute temperature `T` — one row of the
A2 table ("Record in a table the pressure `P` of the CA as a function of its
temperature `T`") / one point of the A3 graph.  Units: `pressure` in Pa,
`temperature` in K. -/
structure CAState where
  /-- Pressure `P` of the confined air.  Units: Pa. -/
  pressure : ℝ
  /-- Absolute temperature `T` of the confined air.  Units: K. -/
  temperature : ℝ

/-- The reference state `(P₀, T₀)`: `P₀` is "the pressure of the system at the
reference temperature `T₀`" (page 9, text below equation (2); values live on
the reference constants and values sheet, kept abstract — see the module
availability note).  Units: `P₀` in Pa, `T₀` in K. -/
def referenceState (P₀ T₀ : ℝ) : CAState := ⟨P₀, T₀⟩

/-- **Governing law of the E1-A5 model (equation (1) at fixed volume and
amount).**  The state `s` lies on the CA's isochore for the volume `V` (m³)
fixed by the PG fill at `h = 4.5 cm` and the closed valves D and E, and the
sealed amount `n` (mol): `s` obeys the ideal-gas equation of state
`P · V = n · R · T` with the universal gas constant `R` (J/(mol·K)).  The
single equation field is the elimination content usable by later proofs. -/
structure IsochoricLaw (V n R : ℝ) (s : CAState) : Prop where
  /-- Equation (1) of the exam at the fixed volume `V` and sealed amount `n`:
  the CA obeys `P · V = n · R · T`. -/
  ideal_gas_law : s.pressure * V = n * R * s.temperature

/-! ## Equation (2): the slope readout and the thermal pressure coefficient -/

/-- The finite-difference pressure–temperature slope `ΔP/ΔT` between two
recorded states of the A2 table — the slope read off the A3 graph and used in
equation (2).  Units: Pa/K. -/
noncomputable def pressureSlope (s₁ s₂ : CAState) : ℝ :=
  (s₂.pressure - s₁.pressure) / (s₂.temperature - s₁.temperature)

/-- **Equation (2) of the exam.**  The constant-volume thermal pressure
coefficient `β₀ = (1/P₀) · (ΔP/ΔT)`, with `P₀` the pressure of the system at
the reference temperature `T₀` and `ΔP/ΔT` the isochoric pressure–temperature
slope.  Units: K⁻¹. -/
noncomputable def thermalPressureCoeff (P₀ ΔP_ΔT : ℝ) : ℝ := (1 / P₀) * ΔP_ΔT

/-- Naming expansion of the experimental quantity entering equation (2): the
coefficient computed from the reference pressure `P₀` and two recorded states
(unfolds `thermalPressureCoeff` and `pressureSlope`). -/
theorem thermalPressureCoeff_pressureSlope_eq (P₀ : ℝ) (s₁ s₂ : CAState) :
    thermalPressureCoeff P₀ (pressureSlope s₁ s₂)
      = (1 / P₀) * ((s₂.pressure - s₁.pressure)
          / (s₂.temperature - s₁.temperature)) :=
  rfl

/-! ## Derived bridges (proved in the prover stage) -/

/-- **A3 content, derived inline** (previous-part dependency E1-A3, policy
`derive_inline_from_problem_only_material`): on the isochore the pressure is
the linear function `P = (nR/V) · T` of the absolute temperature — the A3
graph of pressure versus temperature is a straight line through the origin
(in absolute temperature) of slope `nR/V`.  Proof route: the
`IsochoricLaw.ideal_gas_law` field gives `P · V = n · R · T`; divide by
`0 < V`. -/
theorem pressure_eq_linear_of_temperature {V n R : ℝ} (hV : 0 < V) {s : CAState}
    (hs : IsochoricLaw V n R s) :
    s.pressure = (n * R / V) * s.temperature := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have h := hs.ideal_gas_law
  field_simp
  linear_combination h

/-- **Isochoric slope constancy.**  The finite-difference slope `ΔP/ΔT`
between any two recorded states with distinct temperatures on the same
isochore equals the molar slope `nR/V`; in particular the `ΔP/ΔT` of
equation (2) is well-defined independently of the chosen pair of rows of the
A2 table.  Proof route: subtract the two instances of
`pressure_eq_linear_of_temperature` and divide by the nonzero temperature
difference. -/
theorem pressureSlope_eq_molar_slope {V n R : ℝ} (hV : 0 < V) {s₁ s₂ : CAState}
    (h₁ : IsochoricLaw V n R s₁) (h₂ : IsochoricLaw V n R s₂)
    (hT : s₁.temperature ≠ s₂.temperature) :
    pressureSlope s₁ s₂ = n * R / V := by
  have hp₁ := pressure_eq_linear_of_temperature hV h₁
  have hp₂ := pressure_eq_linear_of_temperature hV h₂
  have hT' : s₂.temperature - s₁.temperature ≠ 0 := sub_ne_zero.mpr (Ne.symm hT)
  have hVne : V ≠ 0 := ne_of_gt hV
  unfold pressureSlope
  rw [hp₁, hp₂]
  field_simp

/-- **Heating branch (sanity).**  The water bath is heated, so the recorded
process runs to higher temperatures and pressures; for air (positive `n`,
`R`, `V`) the isochoric slope is strictly positive.  Proof route:
`pressureSlope_eq_molar_slope`, then positivity of `n · R / V`. -/
theorem pressureSlope_pos {V n R : ℝ} (hV : 0 < V) (hn : 0 < n) (hR : 0 < R)
    {s₁ s₂ : CAState} (h₁ : IsochoricLaw V n R s₁) (h₂ : IsochoricLaw V n R s₂)
    (hT : s₁.temperature ≠ s₂.temperature) :
    0 < pressureSlope s₁ s₂ := by
  rw [pressureSlope_eq_molar_slope hV h₁ h₂ hT]
  positivity

/-- **Pair independence of the coefficient (uniqueness).**  The coefficient
`β₀` of equation (2) computed from any two recorded pairs of the A2 table
(with the same reference pressure `P₀`) is the same: equation (2) determines
*the* coefficient of the gas, not a property of the chosen rows.  Proof
route: both slopes equal `nR/V` by `pressureSlope_eq_molar_slope`. -/
theorem thermalPressureCoeff_pair_independent {V n R P₀ : ℝ} (hV : 0 < V)
    {s₁ s₂ s₃ s₄ : CAState}
    (h₁ : IsochoricLaw V n R s₁) (h₂ : IsochoricLaw V n R s₂)
    (h₃ : IsochoricLaw V n R s₃) (h₄ : IsochoricLaw V n R s₄)
    (hT₁₂ : s₁.temperature ≠ s₂.temperature)
    (hT₃₄ : s₃.temperature ≠ s₄.temperature) :
    thermalPressureCoeff P₀ (pressureSlope s₁ s₂)
      = thermalPressureCoeff P₀ (pressureSlope s₃ s₄) := by
  rw [pressureSlope_eq_molar_slope hV h₁ h₂ hT₁₂,
    pressureSlope_eq_molar_slope hV h₃ h₄ hT₃₄]

/-! ## Raw end-to-end candidate and the E1-A5 target -/

/-- Raw end-to-end quantity requested as the coefficient `β₀` for air: the
inverse `1/T₀` of the reference absolute temperature (derived from
equations (1) and (2) at fixed `V`, `n`; correctness is asserted only
conclusion-side in `thermal_pressure_coeff_eq_candidate`).  Units: K⁻¹. -/
noncomputable def candidateBeta0 (T₀ : ℝ) : ℝ := 1 / T₀

/-- Data fact: the candidate coefficient is positive at a positive reference
temperature. -/
theorem candidateBeta0_pos {T₀ : ℝ} (hT₀ : 0 < T₀) : 0 < candidateBeta0 T₀ := by
  unfold candidateBeta0; positivity

/-- **E1-A5 main target.**  For the sealed CA — volume `V` fixed by the PG
fill and the closed valves, amount `n` fixed by the seal — obeying the
ideal-gas equation of state, with `P₀` the pressure of the system at the
reference temperature `T₀` (equation (2) text), the constant-volume thermal
pressure coefficient of air, `β₀ = (1/P₀)·(ΔP/ΔT)`, determined from any two
recorded states of the A2 table with distinct temperatures, equals the
inverse of the reference absolute temperature.  Proof route:
`pressureSlope_eq_molar_slope` (`ΔP/ΔT = nR/V`);
`pressure_eq_linear_of_temperature` at the reference state
(`P₀ = (nR/V)·T₀`, nonzero since `n, R, T₀, V > 0`); then
`β₀ = (1/P₀)·(nR/V) = (nR/V) / ((nR/V)·T₀) = 1/T₀`. -/
theorem thermal_pressure_coeff_eq_candidate {V n R P₀ T₀ : ℝ}
    (hV : 0 < V) (hn : 0 < n) (hR : 0 < R) (hT₀ : 0 < T₀)
    (href : IsochoricLaw V n R (referenceState P₀ T₀))
    {s₁ s₂ : CAState} (h₁ : IsochoricLaw V n R s₁) (h₂ : IsochoricLaw V n R s₂)
    (hT : s₁.temperature ≠ s₂.temperature) :
    thermalPressureCoeff P₀ (pressureSlope s₁ s₂) = candidateBeta0 T₀ := by
  have hslope := pressureSlope_eq_molar_slope hV h₁ h₂ hT
  have hP₀ : P₀ = (n * R / V) * T₀ := pressure_eq_linear_of_temperature hV href
  have hVne : V ≠ 0 := ne_of_gt hV
  have hT₀ne : T₀ ≠ 0 := ne_of_gt hT₀
  have hnRne : n * R ≠ 0 := ne_of_gt (mul_pos hn hR)
  have hnrVne : n * R / V ≠ 0 := div_ne_zero hnRne hVne
  unfold thermalPressureCoeff candidateBeta0
  rw [hslope, hP₀]
  field_simp

/-- **Sanity certificate.**  The determined coefficient `β₀` for air is
strictly positive (heating raises the pressure; the reference temperature is
positive).  Proof route: `thermal_pressure_coeff_eq_candidate`, then
`candidateBeta0_pos`. -/
theorem determined_coefficient_pos {V n R P₀ T₀ : ℝ}
    (hV : 0 < V) (hn : 0 < n) (hR : 0 < R) (hT₀ : 0 < T₀)
    (href : IsochoricLaw V n R (referenceState P₀ T₀))
    {s₁ s₂ : CAState} (h₁ : IsochoricLaw V n R s₁) (h₂ : IsochoricLaw V n R s₂)
    (hT : s₁.temperature ≠ s₂.temperature) :
    0 < thermalPressureCoeff P₀ (pressureSlope s₁ s₂) := by
  rw [thermal_pressure_coeff_eq_candidate hV hn hR hT₀ href h₁ h₂ hT]
  exact candidateBeta0_pos hT₀

end IPhO2026.E1A5
