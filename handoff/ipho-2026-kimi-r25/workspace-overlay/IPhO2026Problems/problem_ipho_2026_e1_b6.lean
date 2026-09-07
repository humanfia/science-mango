import Mathlib

/-!
# IPhO 2026 · Experiment E1-B6 — Latent heat per unit mass from the molar latent heat

Autoformalization of IPhO 2026 E1-B6
(source: `reports/ipho_2026/problem_ipho_2026_e1_b6.source.json`,
problem pages `ipho_2026_source/image/E1_page-11.png` and
`ipho_2026_source/image/E1_page-12.png`,
"Part B [8.0 pt]. Vapor Pressure").

## Physical scenario (pages 11–12)

Part B studies the water vapor pressure inside the graduated **inner cylinder
(IC)** (Fig. 19, page 11), which contains dry air plus water vapor at total
pressure approximately `P_atm`.  Page 11 states the Clausius–Clapeyron law

```
P_v = P_v0 · exp( −(Q_v/R)·(1/T − 1/T₀) )     (equation (3), page 11)
```

with `T₀` the reference temperature "taken as `0 °C`", `P_v0` the vapor
pressure at `T₀`, `R` the universal gas constant, and "`Q_v` … the molar
latent heat of vaporization of water" (page 11).  Page 12 stipulates the
reference value `R = 8.31 J/(mol·K)` ("For the following questions, use the
reference value R = 8.31 J/(mol·K).").  Subquestion B5 (previous part) used
equation (3) together with the B4 expression for `P_v` to construct a
Clausius–Clapeyron graph and determine the experimental value of the molar
latent heat `Q_v` (units J/mol).

**Subquestion E1-B6 (page 12).**  "From the value of `Q_V`, determine `L_v`
(the latent heat of vaporization per unit mass) indicating the formula that
you used."

## Physical model (governing laws and readouts)

The conversion rests on the defining relations of the three latent-heat
quantities, imposed on **one and the same vaporization sample** (a fixed
portion of water that is vaporized), recorded by `VaporizationSample` and
`LatentHeatConversionLaws`:

1. *Molar latent heat* (`molar_latent_heat`): the heat required to vaporize
   `n` moles of water is `Q = n·Q_v`.  This is the physical role page 11
   assigns to `Q_v` ("the molar latent heat of vaporization of water",
   J/mol), whose experimental value B5 determined.
2. *Specific latent heat* (`specific_latent_heat`): the heat required to
   vaporize a mass `m` of water is `Q = m·L_v`.  This is the physical role B6
   assigns to `L_v` ("the latent heat of vaporization per unit mass", J/kg) —
   it gives `L_v` its independent physical meaning; the conversion formula
   itself appears only in conclusions.
3. *Molar mass of water* (`molar_mass`): a sample of `n` moles has mass
   `m = n·M_w`.  The molar mass `M_w` (kg/mol) is carried as an abstract
   positive parameter: its numerical value belongs to the exam's "reference
   constants and values" sheet cited on page 9, which is **not** part of the
   answer-blind evidence bundle (pages 9–14) — the same availability
   situation as the Fig-17 geometry readouts in the E1-A1/E1-B4 sibling
   formalizations.  No value is assumed here.

The same-sample coherence (one `Q`, one `n`, one `m` for all three laws) is
what makes the conversion well-defined: `n·Q_v = Q = m·L_v = n·M_w·L_v`, and
cancelling the positive vaporized amount `n` gives `Q_v = M_w·L_v`, i.e.
`L_v = Q_v / M_w`.

*Provenance record (not a hypothesis of the target).*  The shared Part-B
governing law, equation (3), is recorded as `VaporPressureClausiusClapeyron`;
the stipulated data `referenceTemperature0C` (`T₀ = 273.15 K`) and
`gasConstantReference` (`R = 8.31 J/(mol·K)`) are recorded for the shared
route by which B5 obtained `Q_v`.  The B6 conversion itself uses neither the
law nor these constants.  The remaining Part-B readouts (`P_atm`, `H₀`, `H`,
`T`, the `h = 5.0 cm` syringe arrangement) belong to the B1–B4 measurement
pipeline and are formalized in the E1-B4 sibling file; B6's route touches only
the B5 result `Q_v` and the reference-sheet molar mass `M_w`.

## Current target (conclusion side only)

`latentHeatPerMass_eq_candidate` (blueprint
`thm:physics:ipho_2026_e1_b6:target`): the requested formula,

```
L_v = Q_v / M_w,
```

carried by the raw end-to-end candidate definition
`candidateLatentHeatPerMass Q_v M_w = Q_v / M_w`; the closed form appears only
in conclusions.  The bridge lemma `molarLatentHeat_eq_molarMass_mul_specific`
isolates the product form `Q_v = M_w·L_v` (molar heat = molar mass × specific
heat), and `latentHeatPerMass_pos` certifies that a positive measured `Q_v`
yields a positive `L_v`.

*Numeric value and rounding.*  B6's numerical answer is the team's
experimental `Q_v` (B5) divided by the reference-sheet molar mass of water;
neither number is fixed by the problem-only evidence available here, so the
raw end-to-end quantity is defined but no numerical value and no
source-derived rounding rule is pinned (B6 carries no `±` uncertainty
specification; the "no uncertainty needed" note on page 13 concerns C4 only).

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
heats in J, the molar latent heat `Q_v` in J/mol, the specific latent heat
`L_v` in J/kg, the molar mass `M_w` in kg/mol, the vaporized amount `n` in
mol, the vaporized mass `m` in kg, pressures in Pa, absolute temperatures in
K, and `R` in J/(mol·K).

## Grounding gaps (LeanExplore, packages Mathlib + Physlib)

* No latent-heat (molar or specific) declaration exists in Mathlib or Physlib:
  the query "latent heat of vaporization per unit mass specific latent heat"
  returned only unit tags (`MassUnit.*`) and the stat-mech
  `CanonicalEnsemble.heatCapacity` (constant-volume heat capacity, a near
  miss — it is a derivative of mean energy, not a phase-change latent heat).
  The two latent-heat roles are stated locally as the equation fields
  `molar_latent_heat` and `specific_latent_heat`.
* No molar-mass / amount-of-substance API exists (query "molar mass amount of
  substance moles" returned only `MassUnit`, `Dimension.div_mass` and
  unrelated hits); the molar-mass relation `m = n·M_w` is stated locally
  (`molar_mass`).
* No Clausius–Clapeyron / saturation-vapor-pressure declaration exists
  (query "Clausius Clapeyron equation vapor pressure temperature exponential"
  returned only unrelated hits such as `adiabatic_relation_log` and
  `DimPressure`); equation (3) is stated locally as the equation-giving
  predicate `VaporPressureClausiusClapeyron`, as in the E1-B4 sibling file.
-/

namespace IPhO2026.E1B6

/-! ## Problem data (stated numerical values, pages 11–12) -/

/-- Reference temperature `T₀`, "taken as `0 °C`" (page 11), expressed as an
absolute temperature: `T₀ = 273.15 K`.  The B6 conversion formula does not
involve `T₀`; this definition records the stated value for the shared Part-B
route (the Clausius–Clapeyron graph of B5 that produced `Q_v`).  Units: K. -/
noncomputable def referenceTemperature0C : ℝ := 273.15

/-- Stipulated reference value of the universal gas constant,
`R = 8.31 J/(mol·K)` (page 12: "For the following questions, use the reference
value R = 8.31 J/(mol·K)." — the stipulation directly precedes subquestions
B5–B6 on page 12).  `R` does not occur in the B6 conversion formula; it is
recorded for the shared Part-B route.  Units: J/(mol·K). -/
noncomputable def gasConstantReference : ℝ := 8.31

/-- Data fact: the reference temperature `T₀ = 273.15 K` is positive. -/
theorem referenceTemperature0C_pos : 0 < referenceTemperature0C := by
  unfold referenceTemperature0C; norm_num

/-- Data fact: the reference gas constant `R = 8.31 J/(mol·K)` is positive. -/
theorem gasConstantReference_pos : 0 < gasConstantReference := by
  unfold gasConstantReference; norm_num

/-! ## Shared Part-B governing law (provenance of `Q_v`) -/

/-- **Clausius–Clapeyron law, equation (3) of the exam (page 11):** a vapor
pressure function `Pv` obeys
`Pv(T) = P_v0 · exp( −(Q_v/R)·(1/T − 1/T₀) )` at every absolute temperature
`T`, with `P_v0` the vapor pressure at the reference temperature `T₀`, `R` the
universal gas constant, and `Q_v` the molar latent heat of vaporization of
water.  This is the shared Part-B governing law: B5 determined the
experimental `Q_v` from its Clausius–Clapeyron graph, and B6 converts that
`Q_v`.  It is recorded for provenance and is **not** a hypothesis of the B6
target.  The predicate unfolds to the pointwise equation, so any hypothesis of
this form can be eliminated to usable equations. -/
def VaporPressureClausiusClapeyron (P_v0 Q_v R T_0 : ℝ) (Pv : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, Pv T = P_v0 * Real.exp (-(Q_v / R) * (1 / T - 1 / T_0))

/-! ## The vaporization sample and the latent-heat laws -/

/-- Bookkeeping state of one vaporization sample: a fixed portion of water
that is vaporized, characterized by the heat `Q` required to vaporize it, the
amount of substance `n` vaporized, and the mass `m` vaporized.  All components
are reals carrying the SI units recorded in the module docstring. -/
structure VaporizationSample where
  /-- Heat `Q` required to vaporize the sample.  Units: J. -/
  heatOfVaporization : ℝ
  /-- Amount of substance `n` of water vaporized.  Units: mol. -/
  amountVaporized : ℝ
  /-- Mass `m` of water vaporized.  Units: kg. -/
  massVaporized : ℝ

/-- **Latent-heat conversion laws.**  The defining relations of the molar
latent heat `Q_v` (J/mol), the latent heat per unit mass `L_v` (J/kg), and the
molar mass `M_w` of water (kg/mol), imposed on a single vaporization sample
`S`.  Every field is a defining physical law stated in or implied by the
problem text (page 11 names `Q_v` "the molar latent heat of vaporization of
water"; B6 names `L_v` "the latent heat of vaporization per unit mass"); no
field states the requested conversion relation `L_v = Q_v / M_w` itself. -/
structure LatentHeatConversionLaws (S : VaporizationSample) (Q_v L_v M_w : ℝ) :
    Prop where
  /-- Definition of the molar latent heat: vaporizing `n` moles of water
  requires the heat `Q = n·Q_v`. -/
  molar_latent_heat : S.heatOfVaporization = S.amountVaporized * Q_v
  /-- Definition of the latent heat per unit mass: vaporizing a mass `m` of
  water requires the heat `Q = m·L_v`. -/
  specific_latent_heat : S.heatOfVaporization = S.massVaporized * L_v
  /-- Definition of the molar mass: a sample of `n` moles has mass
  `m = n·M_w`. -/
  molar_mass : S.massVaporized = S.amountVaporized * M_w

/-! ## Raw end-to-end candidate quantity (definition only; correctness is
proved in the target theorems below) -/

/-- Raw end-to-end quantity requested as the latent heat of vaporization per
unit mass: `Q_v / M_w`, the molar latent heat divided by the molar mass of
water.  Units: J/kg. -/
noncomputable def candidateLatentHeatPerMass (Q_v M_w : ℝ) : ℝ := Q_v / M_w

/-- Naming expansion of the candidate (unfolds the definition). -/
theorem candidateLatentHeatPerMass_eq (Q_v M_w : ℝ) :
    candidateLatentHeatPerMass Q_v M_w = Q_v / M_w := rfl

/-! ## Target: the conversion formula `L_v = Q_v / M_w` -/

/-- **E1-B6 bridge lemma (product form).**  The molar latent heat is the molar
mass of water times the latent heat per unit mass, `Q_v = M_w·L_v`.  Proof
route: the three laws give
`n·Q_v = Q = m·L_v = (n·M_w)·L_v = n·(M_w·L_v)`; cancel the positive
vaporized amount `n` (needs `0 < n`). -/
theorem molarLatentHeat_eq_molarMass_mul_specific (S : VaporizationSample)
    {Q_v L_v M_w : ℝ} (L : LatentHeatConversionLaws S Q_v L_v M_w)
    (hn : 0 < S.amountVaporized) :
    Q_v = M_w * L_v := by
  -- Chain the three laws: `n·Q_v = Q = m·L_v = (n·M_w)·L_v = n·(M_w·L_v)`.
  have h1 : S.amountVaporized * Q_v = S.amountVaporized * (M_w * L_v) := by
    rw [← L.molar_latent_heat, L.specific_latent_heat, L.molar_mass]
    ring
  -- Cancel the positive vaporized amount `n`.
  exact mul_left_cancel₀ (ne_of_gt hn) h1

/-- **E1-B6 main target** (blueprint `thm:physics:ipho_2026_e1_b6:target`).
The conversion formula requested by the subquestion: the latent heat of
vaporization per unit mass is the molar latent heat divided by the molar mass
of water, `L_v = Q_v / M_w`.  Proof route:
`molarLatentHeat_eq_molarMass_mul_specific` gives `Q_v = M_w·L_v`; divide by
the positive molar mass (needs `0 < M_w`). -/
theorem latentHeatPerMass_eq_candidate (S : VaporizationSample)
    {Q_v L_v M_w : ℝ} (L : LatentHeatConversionLaws S Q_v L_v M_w)
    (hn : 0 < S.amountVaporized) (hM : 0 < M_w) :
    L_v = candidateLatentHeatPerMass Q_v M_w := by
  -- Product form from the bridge lemma, then divide by the positive `M_w`.
  have hprod : Q_v = M_w * L_v := molarLatentHeat_eq_molarMass_mul_specific S L hn
  have hMne : M_w ≠ 0 := ne_of_gt hM
  unfold candidateLatentHeatPerMass
  rw [eq_div_iff hMne, hprod]
  ring

/-- Physical sanity certificate: a positive measured molar latent heat `Q_v`
(B5) and a positive molar mass `M_w` yield a positive latent heat per unit
mass, `0 < L_v`.  Proof route: the laws give `Q = n·Q_v > 0` and
`m = n·M_w > 0`, so `L_v = Q/m > 0` (or rewrite
`molarLatentHeat_eq_molarMass_mul_specific` and use `0 < M_w`, `0 < Q_v`). -/
theorem latentHeatPerMass_pos (S : VaporizationSample)
    {Q_v L_v M_w : ℝ} (L : LatentHeatConversionLaws S Q_v L_v M_w)
    (hn : 0 < S.amountVaporized) (hM : 0 < M_w) (hQ : 0 < Q_v) :
    0 < L_v := by
  -- From `Q_v = M_w·L_v` with `0 < Q_v` and `0 < M_w`, the factor `L_v` is
  -- positive (a positive product with a positive left factor).
  have hprod : Q_v = M_w * L_v := molarLatentHeat_eq_molarMass_mul_specific S L hn
  rw [hprod] at hQ
  exact pos_of_mul_pos_right hQ hM.le

end IPhO2026.E1B6
