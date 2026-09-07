import Mathlib

/-!
# IPhO 2026 · Experiment E1-B4 — Vapor pressure of the trapped air–vapor mixture from the falling gas column

Autoformalization of IPhO 2026 E1-B4
(source: `reports/ipho_2026/problem_ipho_2026_e1_b4.source.json`,
problem pages `ipho_2026_source/image/E1_page-11.png` and
`ipho_2026_source/image/E1_page-12.png`,
"Part B [8.0 pt]. Vapor Pressure").

## Physical scenario (pages 11–12)

The graduated **inner cylinder (IC)** sits inside the water-filled **outer
cylinder (OC)** jug (Fig. 19, page 11).  The IC traps a gas column of height
`H` above its internal water surface; a water-filled hose with a plunger-less
syringe raised to the level `h = 5.0 cm` (valve **E** then closed) "keeps the
pressure inside the IC approximately equal to the atmospheric pressure"
(procedure, page 11).  The OC bath is heated to `65 °C`; as the temperature
`T` *falls*, the gas-column height `H(T)` is recorded (subquestions B1–B2).
"The vapor pressure is relatively small around room temperature and the `H(T)`
curve may be approximated as linear" (page 12); B3 extrapolates that graph to
the value `H₀` of `H` at `0 °C`.  Page 11 states the Clausius–Clapeyron law

```
P_v = P_v0 · exp( −(Q_v/R)·(1/T − 1/T₀) )     (equation (3), page 11)
```

with `T₀` the reference temperature taken as `0 °C`, `P_v0` the vapor pressure
at `T₀`, `R` the universal gas constant, and `Q_v` the molar latent heat of
vaporization of water.  Page 12 stipulates the reference value
`R = 8.31 J/(mol·K)` ("For the following questions").

**Subquestion E1-B4 (page 12).**  "Assuming that IC contains both dry air plus
water vapor, deduce an algebraic expression for the vapor pressure `P_v` in
terms of `P_atm` (atmospheric pressure), `H₀`, `H`, `T₀` and `T`.  For the
purposes of this problem, you can assume that the vapor pressure at `0 °C` is
zero."

## Physical model (governing laws and readouts)

Two thermodynamic states of the trapped gas column are related
(`VaporPressureApparatusLaws`): the generic measurement state `S` at absolute
temperature `T` with gas-column height `H`, and the reference state `S₀` at
`T₀` with height `H₀`.

1. *Reference-state readouts* (`reference_temperature`, `reference_height`):
   `S₀` sits at `T = T₀` and `H = H₀`; `H₀` is the B3 extrapolated graph
   readout (previous part; its numerical value comes from the B2 graph and is
   not needed here — only its physical meaning `H(T₀) = H₀` enters).
2. *Stipulated vanishing vapor pressure at `0 °C`*
   (`reference_vanishing_vapor`): `P_v(T₀) = 0`, the explicit modeling
   assumption of B4.
3. *Dalton's law at the apparatus-controlled total pressure*
   (`dalton_reference`, `dalton_atmospheric`): in both states the total
   pressure of the dry-air/water-vapor mixture equals the atmospheric
   pressure, `P_air + P_v = P_atm`.  This idealizes as an equality the
   procedure's "approximately equal to the atmospheric pressure" (the
   `h = 5.0 cm` syringe arrangement), which is the modeling frame in which B4
   asks for an algebraic expression; `h` is recorded as
   `syringeWaterLevelHeight`.
4. *Combined gas law for the fixed amount of dry air*
   (`combined_gas_law_dry_air`): the dry air is a fixed amount of ideal gas,
   so `P_air·V/T` is the same in both states; with the constant
   cross-section `A` of the graduated IC the volume is `V = A·H`, giving the
   cross-multiplied form `P_air·(A·H)·T₀ = P_air₀·(A·H₀)·T` (the unknown
   dry-air amount `n_air` and the gas constant `R` cancel, which is why B4's
   answer involves neither).  The IC cross-section is a figure readout (the
   graduated cylinder of Fig. 19; its diameter belongs to the Figure-17
   apparatus sheet, which is not part of the answer-blind evidence bundle —
   cf. the E1-A1 availability note), so `A` is an abstract positive parameter;
   it cancels in the final expression.
5. *Clausius–Clapeyron law* (`VaporPressureClausiusClapeyron`): equation (3)
   of the exam, the shared Part-B governing law of the vapor pressure.  It is
   **not** a hypothesis of the B4 target (B4 is a pure Dalton + ideal-gas
   derivation); it is recorded as the governing law of the later route
   (B5 determines `Q_v` from it together with the B4 expression).

## Current target (conclusion side only)

`vaporPressure_eq_candidate` (blueprint `thm:physics:ipho_2026_e1_b4:target`):
any two states obeying the laws satisfy

```
P_v(T) = P_atm · (1 − H₀·T / (H·T₀)),
```

carried by the raw end-to-end candidate definition `candidateVaporPressure`;
the closed form appears only in conclusions.  The bridge lemma
`dryAirPressure_eq_candidate` isolates the dry-air partial pressure
`P_air = P_atm·H₀·T / (H·T₀)`; `vaporPressure_fraction_form` records the
equivalent single-fraction algebraic form; and
`candidateVaporPressure_vanishes_at_reference` certifies that the derived
expression is consistent with the stipulated `P_v(T₀) = 0` (it vanishes at
`H = H₀`, `T = T₀`).

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
pressures in Pa, absolute temperatures in K, heights/lengths in m, the
cross-section `A` in m², `R` in J/(mol·K), and `Q_v` in J/mol.
`initialBathTemperatureCelsius` is recorded in °C exactly as stated in the
procedure (it is an initial-condition readout, not a thermodynamic
temperature entering a law).

## Grounding gaps (LeanExplore, packages Mathlib + Physlib)

* Physlib `IdealGas.ideal_gas_law` (declaration id 393919,
  "The ideal gas law: PV = nRT. In our unitsless system, R = 1.") is a
  *derived* stat-mech identity of the microcanonical `IdealGas` Hamiltonian in
  a units-less system with `R = 1` — not the phenomenological
  equation-of-state contract an experiment assumes.  Near miss; the
  fixed-amount consequence used here is stated locally
  (`combined_gas_law_dry_air`).
* No Clausius–Clapeyron / saturation-vapor-pressure / latent-heat declaration
  exists in Mathlib or Physlib (query "Clausius Clapeyron equation vapor
  pressure latent heat" returned only unrelated hits such as
  `adiabatic_relation_log` and `DimPressure`); the law is stated locally as
  the equation-giving predicate `VaporPressureClausiusClapeyron`.
* No Dalton's-law / partial-pressure-mixture declaration exists (query
  "Dalton law partial pressure gas mixture" returned no relevant physics);
  Dalton's law at the apparatus-controlled total pressure is stated locally
  (`dalton_reference`, `dalton_atmospheric`).
* Physlib `DimPressure` (declaration id 394474) is a dimension/unit-tag notion,
  not a pressure-quantity API; pressures are carried as reals with documented
  SI units, consistent with the sibling E1-A1 formalization.
-/

namespace IPhO2026.E1B4

/-! ## Problem data (stated numerical values, pages 11–12) -/

/-- Reference temperature `T₀`, "taken as `0 °C`" (page 11), expressed as an
absolute temperature: `T₀ = 273.15 K`.  The B4 target keeps `T₀` symbolic
("in terms of … `T₀` …"); this definition records the stated value.
Units: K. -/
noncomputable def referenceTemperature0C : ℝ := 273.15

/-- Syringe water level `h = 5.0 cm` (procedure, page 11: "raise the syringe
until it reaches the water level at `h = 5.0 cm`.  Close valve E …  This
arrangement keeps the pressure inside the IC approximately equal to the
atmospheric pressure.").  This is the figure/procedure parameter behind the
total-pressure modeling equality; it does not appear in the final closed
form.  Units: metres. -/
noncomputable def syringeWaterLevelHeight : ℝ := 5.0 / 100

/-- Stipulated reference value of the universal gas constant,
`R = 8.31 J/(mol·K)` (page 12: "For the following questions, use the reference
value R = 8.31 J/(mol·K).").  `R` does not occur in the B4 expression (it
cancels with the fixed dry-air amount); it is recorded for the shared Part-B
route (Clausius–Clapeyron, equation (3); B5).  Units: J/(mol·K). -/
noncomputable def gasConstantReference : ℝ := 8.31

/-- Initial OC bath temperature, `65 °C` (procedure, page 11: "Heat the water
in the OC to 65 °C … Wait until the temperature starts to decrease to start
recording H as a function of T.").  Initial condition of the recorded `H(T)`
run, recorded in °C as stated; it does not enter the B4 laws.  Units: °C. -/
noncomputable def initialBathTemperatureCelsius : ℝ := 65

/-- Data fact: the reference temperature `T₀ = 273.15 K` is positive. -/
theorem referenceTemperature0C_pos : 0 < referenceTemperature0C := by
  unfold referenceTemperature0C; norm_num

/-- Data fact: the syringe water level `h = 5.0 cm` is positive. -/
theorem syringeWaterLevelHeight_pos : 0 < syringeWaterLevelHeight := by
  unfold syringeWaterLevelHeight; norm_num

/-- Data fact: the reference gas constant `R = 8.31 J/(mol·K)` is positive. -/
theorem gasConstantReference_pos : 0 < gasConstantReference := by
  unfold gasConstantReference; norm_num

/-- Data fact: the initial bath temperature `65 °C` is positive (in °C). -/
theorem initialBathTemperatureCelsius_pos : 0 < initialBathTemperatureCelsius := by
  unfold initialBathTemperatureCelsius; norm_num

/-! ## The gas-mixture state and the governing laws -/

/-- Thermodynamic state of the trapped gas column in the IC: the dry-air
partial pressure, the water-vapor partial pressure, the absolute temperature,
and the height `H` of the gas column read on the graduated cylinder.  All
components are reals carrying the SI units recorded in the module docstring. -/
structure GasMixtureState where
  /-- Partial pressure `P_air` of the dry air in the mixture.  Units: Pa. -/
  dryAirPressure : ℝ
  /-- Partial pressure `P_v` of the water vapor in the mixture.  Units: Pa. -/
  vaporPressure : ℝ
  /-- Absolute temperature `T` of the trapped gas.  Units: K. -/
  temperature : ℝ
  /-- Height `H` of the trapped gas column, read on the graduated IC
  (Fig. 19).  Units: m. -/
  gasColumnHeight : ℝ

/-- **Clausius–Clapeyron law, equation (3) of the exam (page 11):** a vapor
pressure function `Pv` obeys
`Pv(T) = P_v0 · exp( −(Q_v/R)·(1/T − 1/T₀) )` at every absolute temperature
`T`, with `P_v0` the vapor pressure at the reference temperature `T₀`, `R` the
universal gas constant, and `Q_v` the molar latent heat of vaporization of
water.  This is the shared Part-B governing law; it drives the later route
(B5/B6 determine `Q_v`, `L_v`) and is recorded here for completeness of the
setup — it is *not* a hypothesis of the B4 target.  The predicate unfolds to
the pointwise equation, so any hypothesis of this form can be eliminated to
usable equations. -/
def VaporPressureClausiusClapeyron (P_v0 Q_v R T_0 : ℝ) (Pv : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, Pv T = P_v0 * Real.exp (-(Q_v / R) * (1 / T - 1 / T_0))

/-- Governing laws of the E1-B4 model, as equations constraining the generic
measurement state `S` (at temperature `T`, column height `H`) and the
reference state `S₀` (at `T₀`, extrapolated height `H₀`) of the trapped gas
column.  `P_atm` is the atmospheric pressure, `A` the constant cross-sectional
area of the graduated IC, `H₀` the B3 extrapolated height at `0 °C`, and `T₀`
the reference temperature.  Every field is a law, stipulation, or readout
stated in or implied by the problem text; no field mentions the requested
expression for `P_v` beyond the laws that determine it. -/
structure VaporPressureApparatusLaws (S S₀ : GasMixtureState)
    (P_atm A H_0 T_0 : ℝ) : Prop where
  /-- Reference-state readout: the reference state sits at the reference
  temperature, `T = T₀` (taken as `0 °C`, page 11). -/
  reference_temperature : S₀.temperature = T_0
  /-- Definition of the B3 readout: `H₀` is the (extrapolated) gas-column
  height at `T₀`, i.e. `H(T₀) = H₀` (page 12, B3: "find the value of `H₀`
  (`H` at `0 °C`)"). -/
  reference_height : S₀.gasColumnHeight = H_0
  /-- Stipulated modeling assumption of B4 (page 12): "you can assume that the
  vapor pressure at `0 °C` is zero", `P_v(T₀) = 0`. -/
  reference_vanishing_vapor : S₀.vaporPressure = 0
  /-- Dalton's law at the reference state: the total pressure of the
  dry-air/water-vapor mixture equals the atmospheric pressure,
  `P_air(T₀) + P_v(T₀) = P_atm` (same syringe arrangement as in the
  measurement state). -/
  dalton_reference : S₀.dryAirPressure + S₀.vaporPressure = P_atm
  /-- Dalton's law at the apparatus-controlled total pressure (measurement
  state): `P_air(T) + P_v(T) = P_atm`.  This states as an equality the
  procedure's "keeps the pressure inside the IC approximately equal to the
  atmospheric pressure" (the `h = 5.0 cm` syringe arrangement of Fig. 19) —
  the modeling frame in which B4 requests an algebraic expression. -/
  dalton_atmospheric : S.dryAirPressure + S.vaporPressure = P_atm
  /-- Combined gas law for the fixed amount of dry air between the two states:
  the dry air is a fixed amount of ideal gas, so `P_air·V/T` agrees in both
  states; with the constant IC cross-section `A` the gas volume is `V = A·H`,
  giving the cross-multiplied form
  `P_air(T)·(A·H(T))·T₀ = P_air(T₀)·(A·H₀)·T`.
  The unknown dry-air amount `n_air` and the gas constant `R` cancel between
  the two states — which is why neither occurs in the B4 expression. -/
  combined_gas_law_dry_air :
    S.dryAirPressure * (A * S.gasColumnHeight) * S₀.temperature
      = S₀.dryAirPressure * (A * S₀.gasColumnHeight) * S.temperature

/-! ## Raw end-to-end candidate quantity (definition only; correctness is
proved in the target theorems below) -/

/-- Raw end-to-end quantity requested as the algebraic expression for the
vapor pressure: `P_atm · (1 − H₀·T / (H·T₀))`, in terms of exactly the
quantities named by B4 (`P_atm`, `H₀`, `H`, `T₀`, `T`).  Units: Pa. -/
noncomputable def candidateVaporPressure (P_atm H_0 H T_0 T : ℝ) : ℝ :=
  P_atm * (1 - H_0 * T / (H * T_0))

/-! ## Target: the algebraic expression for the vapor pressure -/

/-- **E1-B4 bridge lemma.**  The dry-air partial pressure in the measurement
state is `P_air(T) = P_atm·H₀·T / (H·T₀)`.  Proof route: at the reference
state, `dalton_reference` with `reference_vanishing_vapor` gives
`P_air(T₀) = P_atm`; substitute the reference readouts
(`reference_temperature`, `reference_height`) into `combined_gas_law_dry_air`
and solve for `S.dryAirPressure`, cancelling the cross-section `A`
(needs `0 < A`, `0 < H`, `0 < T₀` for the cancellations/division). -/
theorem dryAirPressure_eq_candidate (S S₀ : GasMixtureState)
    {P_atm A H_0 T_0 : ℝ}
    (L : VaporPressureApparatusLaws S S₀ P_atm A H_0 T_0)
    (hA : 0 < A) (hH : 0 < S.gasColumnHeight) (hT0 : 0 < T_0) :
    S.dryAirPressure
      = P_atm * (H_0 * S.temperature) / (S.gasColumnHeight * T_0) := by
  -- At the reference state, Dalton's law with vanishing vapor pressure
  -- pins the dry-air partial pressure to the atmospheric pressure.
  have hPair0 : S₀.dryAirPressure = P_atm := by
    have hDal0 := L.dalton_reference
    have hPv0 := L.reference_vanishing_vapor
    linarith
  -- Substitute the reference readouts into the combined gas law:
  -- `P_air·(A·H)·T₀ = P_atm·(A·H₀)·T`.
  have hComb := L.combined_gas_law_dry_air
  rw [L.reference_temperature, L.reference_height, hPair0] at hComb
  have hdenom : S.gasColumnHeight * T_0 ≠ 0 :=
    mul_ne_zero (ne_of_gt hH) (ne_of_gt hT0)
  rw [eq_div_iff hdenom]
  -- Cancel the cross-section `A` (it is nonzero) and match ring terms.
  apply mul_left_cancel₀ (ne_of_gt hA)
  linear_combination hComb

/-- **E1-B4 main target** (blueprint `thm:physics:ipho_2026_e1_b4:target`).
Assuming the IC contains dry air plus water vapor with zero vapor pressure at
`T₀`, the vapor pressure at the measurement state is the candidate closed form
`P_v(T) = P_atm · (1 − H₀·T / (H·T₀))` — an expression in exactly the
quantities `P_atm`, `H₀`, `H`, `T₀`, `T` named by the subquestion.  Proof
route: `dalton_atmospheric` gives `P_v = P_atm − P_air`; rewrite
`P_air` by `dryAirPressure_eq_candidate`. -/
theorem vaporPressure_eq_candidate (S S₀ : GasMixtureState)
    {P_atm A H_0 T_0 : ℝ}
    (L : VaporPressureApparatusLaws S S₀ P_atm A H_0 T_0)
    (hA : 0 < A) (hH : 0 < S.gasColumnHeight) (hT0 : 0 < T_0) :
    S.vaporPressure
      = candidateVaporPressure P_atm H_0 S.gasColumnHeight T_0 S.temperature := by
  -- Dalton's law in the measurement state: `P_v = P_atm − P_air`.
  have hPair := dryAirPressure_eq_candidate S S₀ L hA hH hT0
  have hDal := L.dalton_atmospheric
  have h2 : S.vaporPressure = P_atm - S.dryAirPressure := by linarith
  -- Substitute the bridge lemma and rearrange `P_atm − P_atm·x` into
  -- `P_atm·(1 − x)`; the division appears as the same atom on both sides.
  rw [h2, hPair, mul_div_assoc]
  unfold candidateVaporPressure
  ring

/-- **E1-B4 equivalent algebraic form.**  The same expression as a single
fraction, `P_v(T) = P_atm · (H·T₀ − H₀·T) / (H·T₀)`.  Proof route:
`vaporPressure_eq_candidate`, then clear the denominator `H·T₀` using the
positivity hypotheses. -/
theorem vaporPressure_fraction_form (S S₀ : GasMixtureState)
    {P_atm A H_0 T_0 : ℝ}
    (L : VaporPressureApparatusLaws S S₀ P_atm A H_0 T_0)
    (hA : 0 < A) (hH : 0 < S.gasColumnHeight) (hT0 : 0 < T_0) :
    S.vaporPressure
      = P_atm * (S.gasColumnHeight * T_0 - H_0 * S.temperature)
          / (S.gasColumnHeight * T_0) := by
  -- Clear the common denominator `H·T₀ ≠ 0` in both the bridge lemma and the
  -- goal, then combine with Dalton's law multiplied through by `H·T₀`.
  have hPair := dryAirPressure_eq_candidate S S₀ L hA hH hT0
  have hDal := L.dalton_atmospheric
  have hdenom : S.gasColumnHeight * T_0 ≠ 0 :=
    mul_ne_zero (ne_of_gt hH) (ne_of_gt hT0)
  rw [eq_div_iff hdenom] at hPair ⊢
  linear_combination hDal * (S.gasColumnHeight * T_0) - hPair

/-- Consistency certificate: the derived candidate expression is compatible
with the stipulated modeling assumption of B4 — at the reference readouts
`H = H₀`, `T = T₀` it evaluates to zero, matching `P_v(T₀) = 0`.  Proof route:
unfold `candidateVaporPressure` and use `H₀·T₀ ≠ 0` from the hypotheses. -/
theorem candidateVaporPressure_vanishes_at_reference {P_atm H_0 T_0 : ℝ}
    (hH0 : 0 < H_0) (hT0 : 0 < T_0) :
    candidateVaporPressure P_atm H_0 H_0 T_0 T_0 = 0 := by
  -- At `H = H₀`, `T = T₀` the subtracted term is `H₀·T₀ / (H₀·T₀) = 1`.
  unfold candidateVaporPressure
  have h : H_0 * T_0 ≠ 0 := mul_ne_zero (ne_of_gt hH0) (ne_of_gt hT0)
  rw [div_self h]
  ring

/-- Physical sanity certificate: since the mixture pressure is the sum of the
two partial pressures and the dry-air partial pressure is nonnegative, the
vapor pressure never exceeds the atmospheric pressure, `P_v ≤ P_atm`.
Proof route: linear arithmetic on `dalton_atmospheric` with the regime
hypothesis `0 ≤ P_air`. -/
theorem vaporPressure_le_atm (S S₀ : GasMixtureState)
    {P_atm A H_0 T_0 : ℝ}
    (L : VaporPressureApparatusLaws S S₀ P_atm A H_0 T_0)
    (hPair : 0 ≤ S.dryAirPressure) :
    S.vaporPressure ≤ P_atm := by
  -- `P_v = P_atm − P_air ≤ P_atm` since `0 ≤ P_air` (Dalton's law).
  have hDal := L.dalton_atmospheric
  linarith

end IPhO2026.E1B4
