import Mathlib

/-!
# IChO 2026, Theory Problem 3, subquestion 3.7 — uranyl adsorption by COF-9

Source: 58th International Chemistry Olympiad, Tashkent 2026, Theory Q3-7
(problem PDF page 31; marking scheme page 31).  Primary visual evidence:
`T3_page-7.png` (experiment data and COF-8 → COF-9 scheme) and
`T3_page-6.png` (COF-8 synthesis from E1 + D2).

## Source contract

COF-9, obtained from COF-8 by hydroxylamine treatment (three nitrile groups of
the E1-derived linker converted to amidoxime groups), adsorbs UO₂²⁺ ions and
loses its fluorescence.

Experiment (all readouts are the source's numerical values):

* adsorbent: `m = 5.000 mg = 5.000 × 10⁻³ g` of COF-9, suspended in
* `V = 200.0 mL = 200.0 × 10⁻³ dm³` of uranyl solution with
* initial concentration `C₀ = 19.90 mg dm⁻³`; after equilibration and
  filtration the final concentration is `Cₑ = 9.225 mg dm⁻³`.

Assumption stated by the problem: all uranium exists as UO₂²⁺ ions, so the
measured uranium concentrations *are* the uranyl concentrations and the
adsorbate molar mass is `M(UO₂²⁺) = 270.03 g mol⁻¹` (marking scheme; standard
atomic masses).  The marking scheme further uses that one repeat unit of
COF-9, formula C₃₆H₂₇N₉O₃ with `M = 633.67 g mol⁻¹`, constitutes one pore.

Governing relations:

* mass balance / definition of the equilibrium adsorption capacity
  `qₑ = (C₀ − Cₑ) · V / m`   (in mg g⁻¹ when `C` is in mg dm⁻³, `V` in dm³,
  `m` in g);
* ions per pore = molar ratio
  `n(UO₂²⁺) / n(pore) = (qₑ · 10⁻³ g g⁻¹ / M(UO₂²⁺)) / (1 g / M(repeat unit))`.

## Assumption / target split

Hypotheses (source data): the four experimental readouts, the two molar
masses, the speciation assumption (all uranium is UO₂²⁺, carried by using the
uranyl molar mass for the adsorbate), and the structural fact that one
C₃₆H₂₇N₉O₃ repeat unit is one pore.  Positivity of masses/volume/molar masses
and `Cₑ ≤ C₀` are preserved as structure side conditions.

Requested outputs (targets, *not* premises):

1. `qₑ = 427.0 mg g⁻¹` — `qe_cof9UranylExperiment`;
2. the number of UO₂²⁺ ions adsorbed per pore is `1` (molar ratio 1 : 1) —
   `uranylIonsPerPore_cof9UranylExperiment` (nearest-integer form) and
   `uranylIonsPerPore_cof9UranylExperiment_approx` (quantitative closeness).

No previous-part conclusions are reused (`previous_parts` is empty).
-/

namespace IChO2026.T3A7

/-- A mass concentration readout in the source's `mg dm⁻³` scale. -/
abbrev MassConcentrationMgDm3 := ℝ

/-- A volume readout in the source's `dm³` scale. -/
abbrev VolumeDm3 := ℝ

/-- A mass readout in the source's `g` scale. -/
abbrev MassG := ℝ

/-- A molar mass readout in the source's `g mol⁻¹` scale. -/
abbrev MolarMassGMol := ℝ

/-- An equilibrium adsorption capacity readout in the source's `mg g⁻¹` scale. -/
abbrev AdsorptionCapacityMgG := ℝ

/-- The data of the COF-9 / UO₂²⁺ adsorption experiment.

The adsorbent is COF-9 and the adsorbate is the uranyl ion UO₂²⁺; the
problem's assumption that all uranium exists as UO₂²⁺ is carried by
`uranylMolarMass`, the molar mass used for the adsorbate.  The side-condition
fields preserve the physical positivity constraints and the fact that
adsorption lowers the dissolved concentration. -/
structure UranylAdsorptionExperiment where
  /-- Initial UO₂²⁺ concentration `C₀`, in `mg dm⁻³`. -/
  initialConcentration : MassConcentrationMgDm3
  /-- Equilibrium (final) UO₂²⁺ concentration `Cₑ`, in `mg dm⁻³`. -/
  equilibriumConcentration : MassConcentrationMgDm3
  /-- Solution volume `V`, in `dm³`. -/
  volume : VolumeDm3
  /-- Mass `m` of the COF-9 adsorbent, in `g`. -/
  adsorbentMass : MassG
  /-- Molar mass of the adsorbate UO₂²⁺, in `g mol⁻¹`. -/
  uranylMolarMass : MolarMassGMol
  /-- Molar mass of the COF-9 repeat unit C₃₆H₂₇N₉O₃, in `g mol⁻¹`. -/
  repeatUnitMolarMass : MolarMassGMol
  /-- Adsorption removes solute: `Cₑ ≤ C₀`. -/
  equilibriumConcentration_le_initial : equilibriumConcentration ≤ initialConcentration
  /-- The solution volume is positive. -/
  volume_pos : 0 < volume
  /-- The adsorbent mass is positive. -/
  adsorbentMass_pos : 0 < adsorbentMass
  /-- The adsorbate molar mass is positive. -/
  uranylMolarMass_pos : 0 < uranylMolarMass
  /-- The repeat-unit molar mass is positive. -/
  repeatUnitMolarMass_pos : 0 < repeatUnitMolarMass

/-- The equilibrium adsorption capacity
`qₑ = (C₀ − Cₑ) · V / m`, in `mg g⁻¹`: the mass of uranyl removed from the
solution per unit mass of COF-9 (solution-side mass balance). -/
noncomputable def qe (e : UranylAdsorptionExperiment) : AdsorptionCapacityMgG :=
  (e.initialConcentration - e.equilibriumConcentration) * e.volume / e.adsorbentMass

/-- The mass of uranyl adsorbed per gram of COF-9, in `g g⁻¹`
(`qₑ` converted from `mg g⁻¹`). -/
noncomputable def adsorbedUranylMassPerGram (e : UranylAdsorptionExperiment) : ℝ :=
  qe e / 1000

/-- The molar amount of uranyl adsorbed per gram of COF-9, in `mol g⁻¹`. -/
noncomputable def adsorbedUranylMolesPerGram (e : UranylAdsorptionExperiment) : ℝ :=
  adsorbedUranylMassPerGram e / e.uranylMolarMass

/-- The molar amount of pores per gram of COF-9, in `mol g⁻¹`: exactly one
pore per C₃₆H₂₇N₉O₃ repeat unit, so one gram contains `1 / M` moles of pores. -/
noncomputable def poreMolesPerGram (e : UranylAdsorptionExperiment) : ℝ :=
  1 / e.repeatUnitMolarMass

/-- The number of UO₂²⁺ ions adsorbed per pore: the molar ratio
`n(UO₂²⁺) / n(pore)` evaluated per gram of COF-9. -/
noncomputable def uranylIonsPerPore (e : UranylAdsorptionExperiment) : ℝ :=
  adsorbedUranylMolesPerGram e / poreMolesPerGram e

/-- The IChO 2026 T3 experiment: `5.000 mg` of COF-9 suspended in `200.0 mL`
of `19.90 mg dm⁻³` UO₂²⁺ solution; equilibrium concentration `9.225 mg dm⁻³`.

The molar masses are sourced data (marking scheme, consistent with standard
atomic masses): `M(UO₂²⁺) = 270.03 g mol⁻¹` and
`M(C₃₆H₂₇N₉O₃) = 633.67 g mol⁻¹`. -/
def cof9UranylExperiment : UranylAdsorptionExperiment where
  initialConcentration := 19.90
  equilibriumConcentration := 9.225
  volume := 0.2000
  adsorbentMass := 0.005000
  uranylMolarMass := 270.03
  repeatUnitMolarMass := 633.67
  equilibriumConcentration_le_initial := by norm_num
  volume_pos := by norm_num
  adsorbentMass_pos := by norm_num
  uranylMolarMass_pos := by norm_num
  repeatUnitMolarMass_pos := by norm_num

/-- Mass-balance (elimination) form of the `qₑ` relation: the mass of uranyl
taken up by the adsorbent equals the mass removed from the solution,
`qₑ · m = (C₀ − Cₑ) · V`. -/
theorem qe_mul_adsorbentMass (e : UranylAdsorptionExperiment) :
    qe e * e.adsorbentMass =
      (e.initialConcentration - e.equilibriumConcentration) * e.volume := by
  exact div_mul_cancel₀ _ (ne_of_gt e.adsorbentMass_pos)

/-- The equilibrium adsorption capacity is nonnegative: adsorption cannot
remove a negative mass of solute. -/
theorem qe_nonneg (e : UranylAdsorptionExperiment) : 0 ≤ qe e := by
  exact div_nonneg
    (mul_nonneg (sub_nonneg.mpr e.equilibriumConcentration_le_initial) e.volume_pos.le)
    e.adsorbentMass_pos.le

/-- Requested output (1): the equilibrium adsorption capacity of COF-9 in
this experiment is `qₑ = 427.0 mg g⁻¹`. -/
theorem qe_cof9UranylExperiment : qe cof9UranylExperiment = 427.0 := by
  norm_num [qe, cof9UranylExperiment]

/-- Requested output (2): the number of UO₂²⁺ ions adsorbed per pore of
COF-9 is `1` — the per-pore molar ratio rounds to the nearest integer `1`
(the marking scheme's `COF-9 pore : UO₂²⁺ = 1 : 1`). -/
theorem uranylIonsPerPore_cof9UranylExperiment :
    round (uranylIonsPerPore cof9UranylExperiment) = 1 := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;>
    norm_num [uranylIonsPerPore, adsorbedUranylMolesPerGram, adsorbedUranylMassPerGram, qe,
      poreMolesPerGram, cof9UranylExperiment]

/-- Quantitative content of the `1 : 1` ratio: the per-pore count computed
from the experiment, `(1.000 g / 633.67 g mol⁻¹) : (0.4270 g / 270.03 g mol⁻¹)`,
lies within `0.01` of exactly `1`. -/
theorem uranylIonsPerPore_cof9UranylExperiment_approx :
    |uranylIonsPerPore cof9UranylExperiment - 1| < 0.01 := by
  rw [abs_lt]
  constructor <;>
    norm_num [uranylIonsPerPore, adsorbedUranylMolesPerGram, adsorbedUranylMassPerGram, qe,
      poreMolesPerGram, cof9UranylExperiment]

end IChO2026.T3A7
