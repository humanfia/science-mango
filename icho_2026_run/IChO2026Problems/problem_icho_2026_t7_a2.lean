import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T7 (Nitrogen Fixation), Subquestion 7.2

Source: 58th International Chemistry Olympiad, Tashkent 2026, theory problem T7,
page PNG `T7_page-1.png` (problem PDF page 63).

## Problem statement

The Haber–Bosch synthesis plant of Fig. 1 consists of

* **R1, steam reforming:** `CH4 + H2O → CO + 3H2` (fed by `x CH4 + y H2O`);
* **R2, partial oxidation:** `2 CH4 + O2 → 2 CO + 4 H2` (fed by the `CH4, CO, H2`
  stream leaving R1 and by air in the ratio `4 N2 + 1 O2`);
* **R3, water–gas shift:** `CO + H2O → CO2 + H2` (extra `H2O` fed in);
* **Z**, a `CO2` scrubber (the stream `N2, CO2, H2` enters, `N2, H2` leaves);
* **R4, ammonia synthesis:** `N2 + 3H2 ⇌ 2NH3`, with a cooler (CLR) separating
  `NH3` and recycling unreacted `N2, H2`.

All reactions except `NH3` formation are quantitative.  The Navoiazot plant
produces `660 000` tons of ammonia per year with a `97.0 %` overall yield.

**Question 7.2.** Calculate the mass of `CH4` (tons) required annually.

## Assumption / target split

Assumptions (carrier: `FlowSheetBalance` and the hypotheses of
`icho_2026_t7_a2`):

* given data: annual output `660 000` tons `NH3`, overall yield `0.97`,
  molar masses `M(NH3) = 17 g/mol`, `M(CH4) = 16 g/mol` (the values used by
  the official marking scheme), air feed ratio `n(N2) = 4 · n(O2)`;
* stoichiometry of R1–R3 imposed quantitatively, with `O2` the limiting
  reagent of R2 and all `CO` converted by R3;
* fresh synthesis gas fed stoichiometrically, `n(H2) = 3 · n(N2)`;
* the overall-yield relation `n(NH3) = 2 · 0.97 · n(N2)` for
  `N2 + 3H2 → 2NH3` (the marking scheme's definition of the 97 % yield);
* total `CH4` feed = `CH4` reformed (R1) + `CH4` oxidised (R2);
* positivity/nonnegativity side conditions.

Target (not assumed anywhere): the methane demand satisfies the mole-ratio
bridge `n(CH4) = 7/8 · n(N2)` and its annual mass is the recorded answer
`280 000` tons to the stated precision (`|m(CH4) − 280 000| ≤ 500` tons,
i.e. rounding to the nearest `1000` tons / three significant figures).
-/

namespace IChO2026.T7.A2

/-- Annual mole/mass bookkeeping for the Navoiazot ammonia plant of
IChO 2026 T7, following the flow sheet of Fig. 1.

All `n_…` fields are amounts of substance in mol per year, `M_…` are molar
masses in g/mol, and `m_…_tons` are masses in metric tons per year. -/
structure AmmoniaPlantBalance where
  /-- Annual ammonia output, tons. -/
  m_NH3_tons : ℝ
  /-- Overall yield of the ammonia synthesis step (dimensionless, in `(0, 1]`). -/
  yield : ℝ
  /-- Molar mass of ammonia, g/mol. -/
  M_NH3 : ℝ
  /-- Molar mass of methane, g/mol. -/
  M_CH4 : ℝ
  /-- Ammonia produced, mol/yr. -/
  n_NH3 : ℝ
  /-- Fresh nitrogen feed (from air), mol/yr. -/
  n_N2 : ℝ
  /-- Fresh hydrogen feed to the synthesis loop, mol/yr. -/
  n_H2 : ℝ
  /-- Oxygen feed (from air), mol/yr. -/
  n_O2 : ℝ
  /-- Methane consumed by steam reforming (R1), mol/yr. -/
  n_CH4_ref : ℝ
  /-- Methane consumed by partial oxidation (R2), mol/yr. -/
  n_CH4_ox : ℝ
  /-- Carbon monoxide produced by steam reforming (R1), mol/yr. -/
  n_CO_ref : ℝ
  /-- Carbon monoxide produced by partial oxidation (R2), mol/yr. -/
  n_CO_ox : ℝ
  /-- Hydrogen produced by steam reforming (R1), mol/yr. -/
  n_H2_ref : ℝ
  /-- Hydrogen produced by partial oxidation (R2), mol/yr. -/
  n_H2_ox : ℝ
  /-- Hydrogen produced by the water–gas shift (R3), mol/yr. -/
  n_H2_shift : ℝ
  /-- Total methane feed, mol/yr. -/
  n_CH4 : ℝ
  /-- Total methane feed, tons/yr. -/
  m_CH4_tons : ℝ

/-- The governing relations of the Fig. 1 flow sheet: unit conversions,
quantitative stoichiometry of R1–R3, the stoichiometric fresh synthesis-gas
feed, the `4 : 1` `N2 : O2` air feed, the overall-yield relation of R4, and
the hydrogen and methane balances, together with the physical side
conditions.  `10 ^ 6` converts grams to metric tons (`1 ton = 10^6 g`). -/
def FlowSheetBalance (b : AmmoniaPlantBalance) : Prop :=
  -- Amount of ammonia produced from its mass (`n = m/M`, grams per year).
  b.n_NH3 = b.m_NH3_tons * 10 ^ 6 / b.M_NH3 ∧
  -- Overall yield of R4 (`N2 + 3H2 → 2NH3`): `n(NH3) = 2 · yield · n(N2, init)`.
  b.n_NH3 = 2 * b.yield * b.n_N2 ∧
  -- Stoichiometric fresh synthesis gas: `n(H2) = 3 · n(N2)`.
  b.n_H2 = 3 * b.n_N2 ∧
  -- Air feed of Fig. 1: `4 N2 + 1 O2`.
  b.n_N2 = 4 * b.n_O2 ∧
  -- R2 quantitative (`2 CH4 + O2 → 2 CO + 4 H2`), O2 fully consumed.
  b.n_CH4_ox = 2 * b.n_O2 ∧
  b.n_CO_ox = 2 * b.n_O2 ∧
  b.n_H2_ox = 4 * b.n_O2 ∧
  -- R1 quantitative (`CH4 + H2O → CO + 3H2`).
  b.n_CO_ref = b.n_CH4_ref ∧
  b.n_H2_ref = 3 * b.n_CH4_ref ∧
  -- R3 quantitative (`CO + H2O → CO2 + H2`): every mole of CO from R1 and R2
  -- is shifted to one mole of H2.
  b.n_H2_shift = b.n_CO_ref + b.n_CO_ox ∧
  -- Hydrogen balance over the front end of the plant.
  b.n_H2 = b.n_H2_ref + b.n_H2_ox + b.n_H2_shift ∧
  -- Methane balance: all fed CH4 reacts in R1 or R2 (no CH4 leaves the plant).
  b.n_CH4 = b.n_CH4_ref + b.n_CH4_ox ∧
  -- Mass of the methane feed (`m = n · M`, grams to tons).
  b.m_CH4_tons = b.n_CH4 * b.M_CH4 / 10 ^ 6 ∧
  -- Physical side conditions.
  0 < b.m_NH3_tons ∧ 0 < b.yield ∧ b.yield ≤ 1 ∧
  0 < b.M_NH3 ∧ 0 < b.M_CH4 ∧
  0 < b.n_N2 ∧ 0 < b.n_O2 ∧ 0 < b.n_H2 ∧
  0 ≤ b.n_CH4_ref ∧ 0 ≤ b.n_CH4_ox

/-- **IChO 2026 T7, question 7.2.**

For a plant satisfying the Fig. 1 flow-sheet balances, producing
`660 000` tons of `NH3` per year at `97.0 %` overall yield, with
`M(NH3) = 17 g/mol` and `M(CH4) = 16 g/mol`:

1. the annual methane demand is `n(CH4) = 7/8 · n(N2, init)` moles
   (the marking-scheme bridge: with `x = n(CH4, ref)` the hydrogen balance
   reads `6·10^10 = 2·10^10 + 3x + x + 1·10^10`, giving `x = 7.5·10^9` and
   `n(CH4) = x + 1·10^10 = 1.75·10^10 mol`);
2. its mass is the recorded answer `280 000` tons, to the nearest
   `1000` tons (three significant figures). -/
theorem icho_2026_t7_a2 (b : AmmoniaPlantBalance)
    (hM_NH3 : b.M_NH3 = 17) (hM_CH4 : b.M_CH4 = 16)
    (hcapacity : b.m_NH3_tons = 660000) (hyield : b.yield = 0.97)
    (hbalance : FlowSheetBalance b) :
    b.n_CH4 = 7 / 8 * b.n_N2 ∧ |b.m_CH4_tons - 280000| ≤ 500 := by
  obtain ⟨h_nNH3, h_yield, h_syngas, h_air, h_ch4ox, h_coox, h_h2ox, h_coref,
    h_h2ref, h_shift, h_h2bal, h_ch4tot, h_mass, _, _, _, _, _, _, _, _, _, _⟩ :=
    hbalance
  rw [hcapacity, hM_NH3] at h_nNH3
  rw [hyield] at h_yield
  rw [hM_CH4] at h_mass
  -- The hydrogen balance reads `3·n(N2) = 4·n(CH4,ref) + 6·n(O2)`; with
  -- `n(O2) = n(N2)/4` this gives `n(CH4,ref) = 3/8·n(N2)`, and adding
  -- `n(CH4,ox) = 2·n(O2) = n(N2)/2` yields the `7/8` bridge.
  have hbridge : b.n_CH4 = 7 / 8 * b.n_N2 := by linarith
  refine ⟨hbridge, ?_⟩
  -- `m(CH4) = 14·n(N2)/10^6` with `1.94·n(N2) = 660000·10^6/17`, giving
  -- `m(CH4) = 9240000/32.98 ≈ 280170` tons, within `500` of `280 000`.
  rw [abs_le]
  constructor <;> linarith

end IChO2026.T7.A2
