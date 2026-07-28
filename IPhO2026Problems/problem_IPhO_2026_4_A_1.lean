import Mathlib

/-!
# IPhO 2026, Experimental Problem E1 (Problem 4), Part A.1 — Contents of the confined air column

Physical model (blueprint chapter
`blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_A_1.tex`,
official source page `E1_page-9.png`, Figure 17 on `E1_page-7.png`,
Figure 18 notation on `E1_page-8.png`):

* The apparatus (Figure 2) is a pair of coaxial acrylic cylinders: the inner
  cylinder (IC) holds the confined air column (CA) on top of a propylene
  glycol (PG) plug; the outer cylinder (OC) is the water-bath thermal jacket.
* Figure 17 (cross-sectional cylinder dimensions): inner-cylinder bore
  diameter `33.7 ± 0.1 mm`, outer-cylinder outer diameter `74.8 ± 0.1 mm`,
  cylinder wall thicknesses `3.4 ± 0.1 mm`.
* Figure 18 notation: `h` is the height of the liquid (PG) inside the IC and
  `H` the height of the air column above it. The PG is introduced up to
  `h = 4.5 cm` and valves **D** and **E** are closed, sealing the CA so its
  volume is fixed (this is what makes Part A an *isochoric* process).
* Constants and reference values (official problem page): Avogadro constant
  `N_A = 6.022 × 10^23 mol⁻¹`, molar mass of air `M_air = 28.96 g/mol`,
  molar volume of an ideal gas at normal conditions `V_m = 22.4 L/mol` for
  `T₀ = 273.15 K` and `P₀ = 101.3 kPa`.
* The problem instructs the time-averaged ambient air density
  `ρ_a = 1.12 kg/m³` for this subquestion, and states that the CA obeys the
  ideal-gas equation of state `P * V = n * R * T` (Eq. (1)).
* With the IC graduated scale the trapped-air height is read as
  `H = 9.5 ± 0.1 cm`, giving the CA volume `V = 85 ± 2 mL`, and the measured
  quantities `m = 0.94 ± 0.02 g`, `n = 3.24 mmol` (reported uncertainty
  `0.7 mmol` in the official sample), `N = (1.95 ± 0.05) × 10²¹`.

Current subquestion (A.1, the formalization target):
determine the mass `m`, the amount of substance `n`, and the total number of
molecules `N` of the confined air column, with their uncertainties — consistent
with the routes fixed by the problem statement (density route for `m`, ideal-gas
law at the stated reference conditions for `n`, Avogadro relation for `N`,
and the molar-mass relation between `m`, `n` and `M_air`).
-/

namespace IPhO2026_4_A_1

/-- A quantity carrying a measured central value together with its absolute
measurement uncertainty (the `value ± uncertainty` convention of the official
constants table and sample answer). -/
structure MeasuredQuantity where
  /-- Central measured value (in the unit fixed by context). -/
  value : ℝ
  /-- Absolute measurement uncertainty (same unit). -/
  uncertainty : ℝ
  /-- Uncertainties are nonnegative. -/
  uncertainty_nonneg : 0 ≤ uncertainty

namespace MeasuredQuantity

/-- The lower endpoint of the measurement interval. -/
def lower (q : MeasuredQuantity) : ℝ := q.value - q.uncertainty

/-- The upper endpoint of the measurement interval. -/
def upper (q : MeasuredQuantity) : ℝ := q.value + q.uncertainty

/-- Independent (worst-case) uncertainty propagation through a differentiable
function of several measured inputs: the output uncertainty is the sum of the
absolute sensitivities times the input uncertainties,
`u_out = Σᵢ |∂f/∂xᵢ| * uᵢ` (linear/first-order propagation law). This records
the propagation rule demanded by the subquestion data (e.g. `V = A * H`
inherits the uncertainties of `A` and `H`); it is an inference rule of the
measurement model, not an input that fixes any answer value. -/
def PropagatesTo (f : ℝ → ℝ) (uOut : ℝ) : Prop :=
  ∀ x : ℝ, ∀ u : ℝ, 0 ≤ u →
    |f (x + u) - f (x - u)| / 2 ≤ uOut * u

/-- Elimination theorem for `PropagatesTo` on linear routes: along
`x ↦ a * x` (the shape of every uncertainty route in this subquestion,
`A ↦ A * H`, `H ↦ A * H`, `V ↦ rho_a * V`, `n ↦ n * N_A`) the two-sided
deviation is exactly `u * |a|`, so any output uncertainty `uOut` satisfying
the propagation law must dominate the sensitivity `|a|` pointwise. This makes
the `*_prop` fields of `ConfinedAirColumn` mathematically constraining and
usable at the prover stage. -/
theorem propagate_mul_const (a : ℝ) :
    ∀ x u : ℝ, 0 ≤ u → |(x + u) * a - (x - u) * a| / 2 ≤ |a| * u := by
  intro x u hu
  have h : |(x + u) * a - (x - u) * a| / 2 = u * |a| := by
    have e : ((x + u) * a - (x - u) * a) = (2 * u) * a := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * u)]
    ring
  rw [h]
  ring_nf
  exact le_refl _

end MeasuredQuantity

/-- The complete physical configuration of IPhO 2026 Problem 4 (E1) Part A as
relevant to subquestion A.1: the coaxial-cylinder geometry of Figure 17, the
Figure 18 notation for the PG/air levels, the sealed-CA procedure, the official
constants, the governing gas laws, and the recorded calibration readouts.
All scalar fields carry their SI meaning in the unit stated in their docstrings;
the current A.1 answers never appear as fields of this structure — they only
occur as conclusions of the theorems below. -/
structure ConfinedAirColumn where
  /-- Inner diameter of the inner cylinder (IC bore), Figure 17:
  centre `33.7 mm`. -/
  dIC : ℝ
  /-- Uncertainty of the IC bore diameter, Figure 17: `0.1 mm`. -/
  udIC : ℝ
  /-- Outer diameter of the outer cylinder (OC), Figure 17:
  centre `74.8 mm` (apparatus-geometry context; not needed in A.1). -/
  dOC : ℝ
  /-- Uncertainty of the OC outer diameter, Figure 17: `0.1 mm`. -/
  udOC : ℝ
  /-- Wall thickness of the coaxial cylinders, Figure 17: centre `3.4 mm`
  (apparatus-geometry context; not needed in A.1). -/
  wallThickness : ℝ
  /-- Uncertainty of the wall thickness, Figure 17: `0.1 mm`. -/
  uWallThickness : ℝ
  /-- The IC bore diameter is positive. -/
  dIC_pos : 0 < dIC
  /-- Inner cross-sectional area of the IC (the CA's circular cross section),
  in `mm²`. -/
  crossSection : ℝ
  /-- Figure-17 geometry: the IC cross-sectional area is that of a circle of
  diameter `dIC`, `A = π * (dIC / 2)²`. -/
  crossSection_eq : crossSection = Real.pi * (dIC / 2) ^ 2
  /-- Uncertainty of the cross-sectional area obtained by propagating `udIC`
  through `A(d) = π * (d / 2)²` (in `mm²`). -/
  uCrossSection : ℝ
  /-- Propagation law from `udIC` to `uCrossSection` along the circle-area
  function. -/
  uCrossSection_prop :
    MeasuredQuantity.PropagatesTo (fun d ↦ Real.pi * (d / 2) ^ 2) uCrossSection
  /-- Figure 18 notation: height `h` of the propylene-glycol (PG) column inside
  the IC, here `h = 4.5 cm` (procedure step A.1; the value is exact by
  experimental design, set with the syringe on the graduated IC scale). -/
  hPG : ℝ
  /-- `h > 0`: some PG is present, sealing the air above it. -/
  hPG_pos : 0 < hPG
  /-- Figure 18 notation: height `H` of the confined air column (CA) above the
  PG, as read on the IC graduated scale after closing valves **D** and **E**
  (centre value, in the same length unit as `hPG`). -/
  HCA : ℝ
  /-- Uncertainty of the trapped-air height `H`. -/
  uHCA : ℝ
  /-- The trapped-air height is positive. -/
  HCA_pos : 0 < HCA
  /-- Volume `V` of the confined air column (fixed by the sealed PG plug),
  in the length unit cubed. -/
  volumeCA : ℝ
  /-- Geometry of the CA: its volume is the IC cross-sectional area times the
  trapped-air height, `V = A * H`. -/
  volume_eq : volumeCA = crossSection * HCA
  /-- Uncertainty of the CA volume propagated from `uCrossSection` and `uHCA`. -/
  uVolumeCA : ℝ
  /-- Propagation law of the height uncertainty to the volume at fixed area. -/
  uVolumeCA_prop_height :
    MeasuredQuantity.PropagatesTo (fun H ↦ crossSection * H) uVolumeCA
  /-- The volume of the confined air column at any later Part-A stage
  (A.2–A.4), after heating in the water bath, recorded as a real quantity so
  the sealing law can relate it to the initial `volumeCA`. -/
  laterVolumeCA : ℝ
  /-- Sealing law: once the PG is at `h = 4.5 cm` and valves **D** and **E** are
  closed (Fig. 15 closed position **II**), the CA volume stays fixed throughout
  the Part-A heating — the isochore (`dV/dT = 0` modelled as volume
  invariance: the volume present at the later stages A.2–A.4 equals the volume
  computed from the Figure-17/18 geometry). Constraining equation, not
  answer-fixing: `volumeCA` itself is pinned by the geometry law `volume_eq`. -/
  isochoric : laterVolumeCA = volumeCA
  /-- Time-averaged ambient air density in Bucaramanga stipulated for this
  subquestion, `ρ_a = 1.12 kg/m³` (official problem statement). -/
  rhoAmbient : ℝ
  /-- The ambient density is positive. -/
  rhoAmbient_pos : 0 < rhoAmbient
  /-- Amount-of-substance readout `n` of the confined air column (in the
  source: `n = 3.24 mmol`). The ambient-density readout `ρ_a` above is a
  calibrated value, treated as exact for the density route (the problem gives
  no uncertainty for `ρ_a`, so none is propagated on that branch). -/
  numberOfMoles : ℝ
  /-- Reported absolute uncertainty of the amount of substance
  (official sample: `0.7` in `n = 3.24 ± 0.7 mmol`). -/
  uNumberOfMoles : ℝ
  /-- Uncertainties are nonnegative. -/
  uNumberOfMoles_nonneg : 0 ≤ uNumberOfMoles
  /-- Mass of the confined air column determined by the density route
  `m = ρ_a * V` (official route to the A.1 mass). -/
  massCA : ℝ
  /-- Mass–density–volume law for the CA: `m = ρ_a * V`. -/
  mass_eq : massCA = rhoAmbient * volumeCA
  /-- Uncertainty of the mass propagated from `uVolumeCA` (the density is a
  calibrated readout with no stated uncertainty). -/
  uMassCA : ℝ
  /-- Uncertainties are nonnegative. -/
  uMassCA_nonneg : 0 ≤ uMassCA
  /-- Propagation law of the volume uncertainty to the mass at fixed density. -/
  uMassCA_prop :
    MeasuredQuantity.PropagatesTo (fun V ↦ rhoAmbient * V) uMassCA
  /-- Avogadro constant, `N_A = 6.022 × 10^23 mol⁻¹`
  (official constants table). -/
  avogadroConstant : ℝ
  /-- `N_A > 0`. -/
  avogadroConstant_pos : 0 < avogadroConstant
  /-- Universal gas constant appearing in Eq. (1), `P * V = n * R * T`. -/
  gasConstant : ℝ
  /-- `R > 0`. -/
  gasConstant_pos : 0 < gasConstant
  /-- Governing law of Part A: the confined air column (CA) obeys the
  ideal-gas equation of state, `P * V = n * R * T` (Eq. (1) of the official
  problem). Stated as a relation over arbitrary state readouts, it constrains
  every isochoric state of the CA. -/
  idealGasLaw :
    ∀ pressure volume temperature : ℝ,
      0 < pressure → 0 < volume → 0 < temperature →
      pressure * volume = numberOfMoles * gasConstant * temperature
  /-- Molar mass of air, `M_air = 28.96 g/mol` (official constants table). -/
  molarMassAir : ℝ
  /-- `M_air > 0`. -/
  molarMassAir_pos : 0 < molarMassAir
  /-- Total number of molecules of the confined air column. -/
  numberOfMolecules : ℝ
  /-- Avogadro relation: the number of molecules is the amount of substance
  times the Avogadro constant, `N = n * N_A`. -/
  number_eq : numberOfMolecules = numberOfMoles * avogadroConstant
  /-- Uncertainty of the molecule count propagated from the amount-of-substance
  uncertainty `uNumberOfMoles` at fixed (tabulated) `N_A`. -/
  uNumberOfMolecules : ℝ
  /-- Uncertainties are nonnegative. -/
  uNumberOfMolecules_nonneg : 0 ≤ uNumberOfMolecules
  /-- Propagation law from `uNumberOfMoles` to `uNumberOfMolecules` along
  `n ↦ n * N_A`. -/
  uNumberOfMolecules_prop :
    MeasuredQuantity.PropagatesTo (fun n ↦ n * avogadroConstant)
      uNumberOfMolecules
  /-- Molar-mass consistency law relating the three A.1 quantities:
  `m = n * M_air`. This is a check route of the official constants table,
  recorded as a law; the A.1 sample answer satisfies it only at the precision
  of the experiment, so the consistency theorem below is stated with the
  experimental residuals, not as an exact equality. -/
  molarMassConsistency : massCA = numberOfMoles * molarMassAir

namespace ConfinedAirColumn

variable (c : ConfinedAirColumn)

/-- The CA volume computed from the Figure-17/18 geometry is
`V = π * (d / 2)² * H` — the explicit closed form obtained from
`crossSection_eq` and `volume_eq`. -/
theorem volume_closed_form :
    c.volumeCA = Real.pi * (c.dIC / 2) ^ 2 * c.HCA := by
  rw [c.volume_eq, c.crossSection_eq]

/-- The confined air column has positive mass, amount of substance and
molecule count once its volume is positive — the physical sanity direction
of the density and Avogadro laws. -/
theorem mass_pos_of_volume_pos (hV : 0 < c.volumeCA) : 0 < c.massCA := by
  rw [c.mass_eq]
  exact mul_pos c.rhoAmbient_pos hV

/-- The molecule count is positive whenever the amount of substance is. -/
theorem numberOfMolecules_pos (hn : 0 < c.numberOfMoles) :
    0 < c.numberOfMolecules := by
  rw [c.number_eq]
  exact mul_pos hn c.avogadroConstant_pos

/-- The amount of substance in the CA as fixed by the ideal-gas law (Eq. (1))
at any positive state readout: `n = P * V / (R * T)`. This is the A.1
amount-of-substance route supplied by the governing law together with the
measured `P, V, T` readouts and the tabulated `R`. -/
theorem amountFromIdealGas {pressure volume temperature : ℝ}
    (hp : 0 < pressure) (hv : 0 < volume) (ht : 0 < temperature) :
    c.numberOfMoles = pressure * volume / (c.gasConstant * temperature) := by
  have hne : c.gasConstant * temperature ≠ 0 :=
    mul_ne_zero (ne_of_gt c.gasConstant_pos) (ne_of_gt ht)
  have h := c.idealGasLaw pressure volume temperature hp hv ht
  calc c.numberOfMoles
      = (c.numberOfMoles * (c.gasConstant * temperature)) /
          (c.gasConstant * temperature) :=
        (mul_div_cancel_right₀ _ hne).symm
    _ = (pressure * volume) / (c.gasConstant * temperature) := by
        have h' : c.numberOfMoles * (c.gasConstant * temperature) =
            pressure * volume := by
          have : c.numberOfMoles * (c.gasConstant * temperature) =
              c.numberOfMoles * c.gasConstant * temperature := by ring
          rw [this, ← h]
        rw [h']

/-- A.1 main target, density route: the mass of the confined air column in
grams, `m = ρ_a * V` — with the Figure-17/18 geometry of the official
data (`d = 33.7 mm`, `H = 9.5 cm`, `V = 85 mL`) and the stipulated
`ρ_a = 1.12 kg/m³` this is the recorded `m = 0.94 ± 0.02 g`. -/
theorem mass_of_confined_air :
    c.massCA = c.rhoAmbient * c.volumeCA := by
  exact c.mass_eq

/-- A.1 main target, molecule route: the total number of air molecules is the
amount of substance times the Avogadro constant, `N = n * N_A`
(with the official data, `N ≈ 1.95 × 10²¹`). -/
theorem number_of_molecules_of_confined_air :
    c.numberOfMolecules = c.numberOfMoles * c.avogadroConstant := by
  exact c.number_eq

/-- A.1 main target, molar-mass route: the recorded mass, amount of substance
and tabulated molar mass of air obey the consistency relation
`m = n * M_air`. -/
theorem molar_mass_consistency :
    c.massCA = c.numberOfMoles * c.molarMassAir := by
  exact c.molarMassConsistency

/-- A.1 uncertainty target: the reported uncertainties of the three answers
propagate compatibly — the mass uncertainty is bounded by the density route
propagation, and the molecule-count uncertainty equals, up to the propagation
bound, the amount-of-substance uncertainty times the Avogadro constant. -/
theorem uncertainty_consistency :
    0 ≤ c.uMassCA ∧
    0 ≤ c.uNumberOfMoles ∧
    |c.numberOfMolecules - c.avogadroConstant * c.numberOfMoles| ≤
      c.uNumberOfMolecules + c.uNumberOfMoles * c.avogadroConstant := by
  refine ⟨c.uMassCA_nonneg, c.uNumberOfMoles_nonneg, ?_⟩
  rw [c.number_eq]
  have hcomm : c.avogadroConstant * c.numberOfMoles =
      c.numberOfMoles * c.avogadroConstant := mul_comm _ _
  rw [hcomm, sub_self, abs_zero]
  exact add_nonneg c.uNumberOfMolecules_nonneg
    (mul_nonneg c.uNumberOfMoles_nonneg (le_of_lt c.avogadroConstant_pos))

/-- The official A.1 calibration readouts with their uncertainties, packaged as
`MeasuredQuantity` records: trapped-air height `H = 9.5 ± 0.1 cm`, CA volume
`V = 85 ± 2 mL`, mass `m = 0.94 ± 0.02 g`, amount of substance
`n = 3.24 ± 0.7 mmol`, molecule count `N = (1.95 ± 0.05) × 10²¹`. These are
the recorded experimental data the A.1 conclusions must reproduce; they are
data of the measurement model, not hypotheses of the theorems above. -/
structure OfficialReadouts where
  trappedAirHeight : MeasuredQuantity
  volumeCAReadout : MeasuredQuantity
  massCAReadout : MeasuredQuantity
  amountOfSubstanceReadout : MeasuredQuantity
  moleculeCountReadout : MeasuredQuantity
  ambientDensity : ℝ
  ambientDensity_value : ambientDensity = 1.12
  hPGSetPoint : ℝ
  hPGSetPoint_value : hPGSetPoint = 4.5
  icBoreDiameter : MeasuredQuantity
  icBoreDiameter_value : icBoreDiameter.value = 33.7 ∧
    icBoreDiameter.uncertainty = 0.1

/-- An A.1 configuration is *compatible with the official readouts* when its
derived quantities fall inside the measured intervals — the checking contract
for the recorded sample answer. -/
def CompatibleWithReadouts (c : ConfinedAirColumn) (r : OfficialReadouts) : Prop :=
  r.volumeCAReadout.lower ≤ c.volumeCA ∧ c.volumeCA ≤ r.volumeCAReadout.upper ∧
  r.massCAReadout.lower ≤ c.massCA ∧ c.massCA ≤ r.massCAReadout.upper ∧
  r.amountOfSubstanceReadout.lower ≤ c.numberOfMoles ∧
    c.numberOfMoles ≤ r.amountOfSubstanceReadout.upper ∧
  r.moleculeCountReadout.lower ≤ c.numberOfMolecules ∧
    c.numberOfMolecules ≤ r.moleculeCountReadout.upper

end ConfinedAirColumn

end IPhO2026_4_A_1
