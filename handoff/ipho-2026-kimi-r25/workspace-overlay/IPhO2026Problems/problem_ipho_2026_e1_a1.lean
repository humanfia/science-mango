import Mathlib

/-!
# IPhO 2026 · Experiment E1-A1 — Confined air column: mass, amount, molecule count

Autoformalization of IPhO 2026 E1-A1
(source: `reports/ipho_2026/problem_ipho_2026_e1_a1.source.json`,
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

with `R` the universal gas constant.  "The density of ambient air in Bucaramanga
varies with local temperature and pressure.  For the following question, use the
time-averaged value `ρ = 1.12 kg/m³`."  The outer-cylinder (OC) water bath is
then heated while `P` and `T` are recorded (that is the isochoric process of
subquestions A2–A5; for A1 only the sealing state matters).  Page 9 also refers
to a "reference constants and values" sheet carrying the reference pressure `P₀`
and reference temperature `T₀` of the system.

**Subquestion E1-A1.**  Determine the mass `m`, the number of moles `n`, and the
total number of air molecules `N` of the CA.

## Figure 17 readout — availability note (answer-blind)

The problem instructs to "use the cylinder dimensions in Figure 17".  Figure 17
belongs to the apparatus-description pages of the E1 exam, which are **not**
part of the answer-blind evidence bundle (only pages 9, 11–14 are available,
and none of them shows Figure 17; the figure dimensions occur nowhere in the
extracted question text either).  Per the answer-blind protocol the dimensions
must not be guessed.  They are therefore formalized as **abstract positive
parameters** with their physical roles recorded:

* `d` — inner diameter of the cylindrical inner cylinder (Fig. 17), in metres;
* `H` — effective inner height of the IC air space up to the closed-valve seal
  (Fig. 17), in metres, with `h < H` so that the air column above the PG
  surface has positive height `H − h`.

Once the figure values are supplied to these parameters, the candidate
quantities below evaluate to the requested numbers; no target value is assumed
anywhere in this file.

## Physical model (governing laws and readouts)

1. *Fixed geometry* (`airColumnVolume`): the CA occupies the cylinder
   cross-section `π·(d/2)²` over the height `H − h` above the PG surface; the
   PG fill and the closed valves fix this volume (`volume_fixed`).
2. *Sealing at ambient conditions* (`sealed_at_ambient_pressure`,
   `sealed_at_ambient_temperature`): the valves are closed while the trapped
   air is in equilibrium with the ambient air, so the sealing state has
   pressure `P_amb` and absolute temperature `T_amb` (the reference constants
   `P₀`, `T₀` alluded to on page 9).  This is also what licenses using the
   ambient density for the trapped air.
3. *Ideal-gas law* (`ideal_gas_law`): `P·V = n·R·T`, equation (1) of the exam.
4. *Density route to the mass* (`mass_from_density`): `m = ρ_a·V` with the
   stipulated time-averaged `ρ_a = 1.12 kg/m³`.
5. *Avogadro relation* (`molecules_from_amount`): `N = n·N_A`, the definition
   of the mole.

## Current target (conclusion side only)

`confined_air_column_values`: any CA state obeying the laws has

* `m = ρ_a · π·(d/2)²·(H − h)`                      (mass, density route),
* `n = P_amb · π·(d/2)²·(H − h) / (R · T_amb)`      (amount, ideal-gas route),
* `N = N_A · P_amb · π·(d/2)²·(H − h) / (R · T_amb)` (molecule count),

carried by the raw end-to-end candidate definitions `candidateMass`,
`candidateAmount`, `candidateMoleculeCount`; the closed forms appear only in
conclusions.  `confined_air_column_positive` certifies that the determined
values are physically positive.  A source-derived *numeric* rounding rule
(e.g. two significant figures, from `h = 4.5 cm`) can only be stated once the
Figure-17 dimensions are available; see the task-result record.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
lengths in m, areas in m², volumes in m³, density in kg/m³, pressure in Pa,
temperature in K, amount in mol, mass in kg, `R` in J/(mol·K), `N_A` in
mol⁻¹, and the molecule count `N` dimensionless (carried as a real, as is
customary for large counts).

## Grounding gaps (LeanExplore, packages Mathlib + Physlib)

* Physlib `IdealGas.ideal_gas_law`
  (`Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas`) is a
  *derived* stat-mech identity in a units-less system with `R = 1`, tied to the
  microcanonical `IdealGas` Hamiltonian — not the phenomenological
  equation-of-state contract an experiment assumes.  Near miss; the law is
  stated locally as the exam does (`ideal_gas_law` field).
* No universal gas constant `R` and no Avogadro constant `N_A` exist in
  Physlib (only the axiom-backed Boltzmann constant `Constants.kB` in arbitrary
  units).  `R` and `N_A` are abstract positive parameters — fitting, since
  Part A4 of the exam is precisely the experimental determination of `R`.
* `FluidDynamics.MassDensity` is a continuum field notion; the lumped relation
  `m = ρ·V` is stated directly (`mass_from_density`).
-/

namespace IPhO2026.E1A1

/-! ## Problem data (stated numerical values, page 9) -/

/-- Propylene-glycol fill height, `h = 4.5 cm` (procedure, page 9: "Introduce PG
into IC to `h = 4.5 cm` and close valves D and E.  This ensures that the volume
of CA is fixed.").  Units: metres. -/
noncomputable def pgFillHeight : ℝ := 4.5 / 100

/-- Time-averaged ambient air density in Bucaramanga, `ρ_a = 1.12 kg/m³`
(problem data, page 9; the density "varies with local temperature and
pressure" and the exam stipulates this time-averaged value for A1).
Units: kg/m³. -/
noncomputable def ambientAirDensity : ℝ := 1.12

/-- Data fact: the PG fill height is positive. -/
theorem pgFillHeight_pos : 0 < pgFillHeight := by
  unfold pgFillHeight; norm_num

/-- Data fact: the ambient air density is positive. -/
theorem ambientAirDensity_pos : 0 < ambientAirDensity := by
  unfold ambientAirDensity; norm_num

/-! ## Figure 17 geometry (readouts kept abstract; see the availability note) -/

/-- Cross-sectional area of the cylindrical inner cylinder (IC) of inner
diameter `d` (Figure 17 readout; circular cross-section).  Units: m². -/
noncomputable def icCrossSectionalArea (d : ℝ) : ℝ := Real.pi * (d / 2) ^ 2

/-- Height of the confined air column: the CA fills the IC from the PG surface
at height `h = pgFillHeight` up to the effective inner height `H` at the
closed-valve seal (Figure 17 readout).  Units: metres. -/
noncomputable def airColumnHeight (H : ℝ) : ℝ := H - pgFillHeight

/-- Volume of the confined air column, fixed by the PG fill and the closed
valves D and E: cross-section times air-column height.  Units: m³. -/
noncomputable def airColumnVolume (d H : ℝ) : ℝ :=
  icCrossSectionalArea d * airColumnHeight H

/-- The air column has positive height whenever the effective inner height
exceeds the PG fill level (physical regime of the experiment). -/
theorem airColumnHeight_pos {H : ℝ} (hH : pgFillHeight < H) :
    0 < airColumnHeight H :=
  sub_pos.mpr hH

/-- The confined air volume is positive for positive inner diameter and an air
column of positive height. -/
theorem airColumnVolume_pos {d H : ℝ} (hd : 0 < d) (hH : pgFillHeight < H) :
    0 < airColumnVolume d H := by
  have hH' : 0 < airColumnHeight H := airColumnHeight_pos hH
  unfold airColumnVolume icCrossSectionalArea
  positivity

/-! ## The confined air column state and its governing laws -/

/-- Thermodynamic state of the confined air column (CA) at sealing: pressure
`P`, volume `V`, absolute temperature `T`, amount of substance `n`, mass `m`,
and total molecule count `N`.  All components are reals carrying the SI units
recorded in the module docstring; the molecule count is dimensionless. -/
structure ConfinedAirColumn where
  /-- Pressure `P` of the confined air.  Units: Pa. -/
  pressure : ℝ
  /-- Volume `V` of the confined air.  Units: m³. -/
  volume : ℝ
  /-- Absolute temperature `T` of the confined air.  Units: K. -/
  temperature : ℝ
  /-- Amount of substance `n` of the confined air.  Units: mol. -/
  amount : ℝ
  /-- Mass `m` of the confined air.  Units: kg. -/
  mass : ℝ
  /-- Total number `N` of air molecules in the column (dimensionless count,
  carried as a real). -/
  molecules : ℝ

/-- Governing laws of the E1-A1 model, as equations constraining the sealing
state `S` of the CA.  The ambient (reference) pressure `P_amb` and absolute
temperature `T_amb` are the reference-constants readouts (`P₀`, `T₀` on
page 9), `R` is the universal gas constant, `N_A` the Avogadro constant, and
`d`, `H` the Figure-17 cylinder dimensions.  Every field is an equation or a
modeling relation stated in the problem; no field mentions the requested
values of `m`, `n`, `N` beyond the law that determines them. -/
structure ConfinedAirColumnLaws (S : ConfinedAirColumn)
    (P_amb T_amb R N_A d H : ℝ) : Prop where
  /-- Fixed-volume readout (procedure + Figure 17 geometry): introducing PG to
  height `h` and closing valves D and E fixes the CA volume to the cylinder
  cross-section times the air-column height. -/
  volume_fixed : S.volume = airColumnVolume d H
  /-- Sealing at ambient pressure: the valves are closed while the trapped air
  is in equilibrium with the ambient air, so `P = P_amb`. -/
  sealed_at_ambient_pressure : S.pressure = P_amb
  /-- Sealing at ambient temperature: the trapped air is in thermal equilibrium
  with the room when the valves are closed, so `T = T_amb`. -/
  sealed_at_ambient_temperature : S.temperature = T_amb
  /-- Governing law, equation (1) of the exam: the CA obeys the ideal-gas
  equation of state `P · V = n · R · T`. -/
  ideal_gas_law : S.pressure * S.volume = S.amount * R * S.temperature
  /-- Problem-instructed density route to the mass: the CA mass is the
  time-averaged ambient air density `ρ_a = 1.12 kg/m³` times the CA volume
  (legitimized by the sealing at ambient conditions). -/
  mass_from_density : S.mass = ambientAirDensity * S.volume
  /-- Avogadro relation (definition of the mole): the molecule count is the
  amount of substance times the Avogadro constant, `N = n · N_A`. -/
  molecules_from_amount : S.molecules = S.amount * N_A

/-! ## Raw end-to-end candidate quantities (definitions only; correctness is
proved in the target theorems below) -/

/-- Raw end-to-end quantity requested as the mass of the CA: the ambient
density times the confined volume, `ρ_a · π·(d/2)²·(H − h)`.  Units: kg. -/
noncomputable def candidateMass (d H : ℝ) : ℝ :=
  ambientAirDensity * airColumnVolume d H

/-- Raw end-to-end quantity requested as the amount of substance of the CA:
from the ideal-gas law at the ambient sealing state,
`P_amb · π·(d/2)²·(H − h) / (R · T_amb)`.  Units: mol. -/
noncomputable def candidateAmount (P_amb T_amb R d H : ℝ) : ℝ :=
  P_amb * airColumnVolume d H / (R * T_amb)

/-- Raw end-to-end quantity requested as the total number of air molecules:
the Avogadro constant times the candidate amount,
`N_A · P_amb · π·(d/2)²·(H − h) / (R · T_amb)`.  Dimensionless count. -/
noncomputable def candidateMoleculeCount (P_amb T_amb R N_A d H : ℝ) : ℝ :=
  N_A * P_amb * airColumnVolume d H / (R * T_amb)

/-- Naming expansion of the mass candidate (unfolds the geometry chain). -/
theorem candidateMass_eq (d H : ℝ) :
    candidateMass d H
      = ambientAirDensity * (Real.pi * (d / 2) ^ 2 * (H - pgFillHeight)) :=
  rfl

/-- Naming expansion of the amount candidate (unfolds the geometry chain). -/
theorem candidateAmount_eq (P_amb T_amb R d H : ℝ) :
    candidateAmount P_amb T_amb R d H
      = P_amb * (Real.pi * (d / 2) ^ 2 * (H - pgFillHeight)) / (R * T_amb) :=
  rfl

/-- Naming expansion of the molecule-count candidate (unfolds the geometry
chain). -/
theorem candidateMoleculeCount_eq (P_amb T_amb R N_A d H : ℝ) :
    candidateMoleculeCount P_amb T_amb R N_A d H
      = N_A * P_amb * (Real.pi * (d / 2) ^ 2 * (H - pgFillHeight)) / (R * T_amb) :=
  rfl

/-! ## Target: the determined mass, amount, and molecule count -/

/-- **E1-A1 target, mass component.**  The mass of the confined air column is
the ambient density times the fixed confined volume.  Proof route:
`mass_from_density` then `volume_fixed`. -/
theorem mass_eq_candidate (S : ConfinedAirColumn) {P_amb T_amb R N_A d H : ℝ}
    (L : ConfinedAirColumnLaws S P_amb T_amb R N_A d H) :
    S.mass = candidateMass d H := by
  -- `mass_from_density` gives `S.mass = ρ_a * S.volume`; substituting the fixed
  -- volume `volume_fixed` yields the candidate mass (defeq to `candidateMass`).
  rw [L.mass_from_density, L.volume_fixed]
  -- `candidateMass d H` is definitionally `ambientAirDensity * airColumnVolume d H`.
  rfl

/-- **E1-A1 target, amount component.**  The amount of substance of the
confined air column follows from the ideal-gas law at the ambient sealing
state.  Proof route: rewrite `ideal_gas_law` by `sealed_at_ambient_pressure`,
`sealed_at_ambient_temperature`, `volume_fixed`, then solve for `S.amount`
(needs `0 < R` and `0 < T_amb` for the division). -/
theorem amount_eq_candidate (S : ConfinedAirColumn) {P_amb T_amb R N_A d H : ℝ}
    (L : ConfinedAirColumnLaws S P_amb T_amb R N_A d H)
    (hR : 0 < R) (hT : 0 < T_amb) :
    S.amount = candidateAmount P_amb T_amb R d H := by
  -- Rewrite the ideal-gas law `P·V = n·R·T` at the ambient sealing state:
  -- `P_amb · V = n · R · T_amb`, then solve for `n` (the divisor `R·T_amb` is
  -- nonzero since `0 < R` and `0 < T_amb`).
  have higl := L.ideal_gas_law
  rw [L.sealed_at_ambient_pressure, L.volume_fixed,
    L.sealed_at_ambient_temperature] at higl
  -- higl : P_amb * airColumnVolume d H = S.amount * R * T_amb
  have hRT : R * T_amb ≠ 0 := mul_ne_zero (ne_of_gt hR) (ne_of_gt hT)
  unfold candidateAmount
  rw [eq_div_iff_mul_eq hRT]
  -- goal : S.amount * (R * T_amb) = P_amb * airColumnVolume d H
  linear_combination higl.symm

/-- **E1-A1 target, molecule-count component.**  The total number of air
molecules is the Avogadro constant times the amount of substance.  Proof
route: `molecules_from_amount` then `amount_eq_candidate`. -/
theorem molecules_eq_candidate (S : ConfinedAirColumn) {P_amb T_amb R N_A d H : ℝ}
    (L : ConfinedAirColumnLaws S P_amb T_amb R N_A d H)
    (hR : 0 < R) (hT : 0 < T_amb) :
    S.molecules = candidateMoleculeCount P_amb T_amb R N_A d H := by
  -- `molecules_from_amount` gives `S.molecules = S.amount * N_A`; substituting
  -- the amount from `amount_eq_candidate` yields the candidate molecule count
  -- (the two closed forms differ only by commutativity/associativity).
  have hAmt := amount_eq_candidate S L hR hT
  rw [L.molecules_from_amount, hAmt]
  unfold candidateAmount candidateMoleculeCount
  ring

/-- **E1-A1 main target.**  The laws of the model determine the requested mass
`m`, amount of substance `n`, and total molecule count `N` of the confined air
column as the candidate closed forms.  Proof route: conjunction of
`mass_eq_candidate`, `amount_eq_candidate`, `molecules_eq_candidate`. -/
theorem confined_air_column_values (S : ConfinedAirColumn)
    {P_amb T_amb R N_A d H : ℝ}
    (L : ConfinedAirColumnLaws S P_amb T_amb R N_A d H)
    (hR : 0 < R) (hT : 0 < T_amb) :
    S.mass = candidateMass d H ∧
      S.amount = candidateAmount P_amb T_amb R d H ∧
        S.molecules = candidateMoleculeCount P_amb T_amb R N_A d H := by
  exact ⟨mass_eq_candidate S L, amount_eq_candidate S L hR hT,
    molecules_eq_candidate S L hR hT⟩

/-- Physical sanity certificate: in the regime of the experiment (positive
cylinder diameter, air column of positive height, positive ambient pressure
and temperature, positive constants) the determined mass, amount, and
molecule count are all positive — the CA really contains air.  Proof route:
the three component theorems, then positivity of each candidate via
`airColumnVolume_pos`, `ambientAirDensity_pos`, and the hypotheses. -/
theorem confined_air_column_positive (S : ConfinedAirColumn)
    {P_amb T_amb R N_A d H : ℝ}
    (L : ConfinedAirColumnLaws S P_amb T_amb R N_A d H)
    (hd : 0 < d) (hH : pgFillHeight < H) (hP : 0 < P_amb) (hT : 0 < T_amb)
    (hR : 0 < R) (hNA : 0 < N_A) :
    0 < S.mass ∧ 0 < S.amount ∧ 0 < S.molecules := by
  -- Transport the three component equalities into the goal, then each
  -- candidate is a product/quotient of strictly positive quantities.
  have hV_pos : 0 < airColumnVolume d H := airColumnVolume_pos hd hH
  have hρ : 0 < ambientAirDensity := ambientAirDensity_pos
  rw [mass_eq_candidate S L, amount_eq_candidate S L hR hT,
    molecules_eq_candidate S L hR hT]
  refine ⟨?_, ?_, ?_⟩
  · unfold candidateMass
    positivity
  · unfold candidateAmount
    positivity
  · unfold candidateMoleculeCount
    positivity

end IPhO2026.E1A1
