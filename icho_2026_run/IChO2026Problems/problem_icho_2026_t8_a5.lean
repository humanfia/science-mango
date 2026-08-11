import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, Theory Problem 8 (Recycling of CO₂), Subquestion 8.5

Catalyst **1** (the Fe–N₄ molecular catalyst synthesised from ligand **8**
and FeCl₂) is dispersed on crystalline carbon nitride (C₃N₄).  The
subquestion asks for the number `N_cat` of catalytic molecules per nm² of
loaded C₃N₄.

## Source data (Problem PDF page 73, printed page Q8-2)

* mass fraction of catalyst in the loaded support: `ω_cat = 3.8 %`;
* specific surface area of C₃N₄: `S = 17.8 m² g⁻¹`;
* catalyst molar mass: `M_cat = 557.21 g mol⁻¹`;
* the marking scheme converts amount to molecule count with
  `N_A = 6.02 × 10²³ mol⁻¹`.

## Governing relations

1. A 1 nm² patch of support carries
   `m_sup = 1 / (S · 10¹⁸)` g of C₃N₄ (since 1 m² = 10¹⁸ nm²).
2. The mass fraction of catalyst in the loaded support obeys
   `ω_cat = m_cat / (m_cat + m_sup)`.
3. The molecule count per nm² is `N_cat = (m_cat / M_cat) · N_A`.

## Assumption / target split

Assumptions: the four source readouts above, their positivity (and
`ω_cat < 1`), and the three governing relations, which are encoded as
*definitions* plus the consistency lemma `massFraction_law`.
Target: `N_cat` for these data rounds to `2.4` molecules per nm²
(`moleculesPerNm2_problem_rounds`), via the marking-scheme intermediates
`m_sup = 5.618 × 10⁻²⁰ g` and `m_cat = 2.219 × 10⁻²¹ g`.

Note on the rubric: full credit requires solving relation 2 for `m_cat`
(giving `N_cat ≈ 2.4`); treating `17.8 m² g⁻¹` as the area of the loaded
mixture, i.e. dropping the `1 - ω_cat` correction, gives `N_cat ≈ 2.3`
(partial credit).  The formalization below encodes the correct relation.

All quantities are real numerical readouts in the source units stated
above; the identities of the two samples (catalyst **1**, crystalline
C₃N₄) do not enter the arithmetic beyond the quoted constants.
-/

namespace IChO2026T8A5

/-- Numerical parameters of a molecular catalyst dispersed on a porous
support, each represented by its real readout in the source units:

* `massFraction` — `ω_cat`, catalyst mass fraction of the loaded support
  (dimensionless);
* `specificArea` — specific surface area of the support, in `m² g⁻¹`;
* `molarMassCat` — `M_cat`, catalyst molar mass, in `g mol⁻¹`;
* `avogadro` — `N_A`, Avogadro constant, in `mol⁻¹`.

The side conditions keep the mass fraction in the open interval `(0, 1)`
and the remaining readouts positive, so the mass-fraction law has a unique
positive solution for the catalyst mass. -/
structure LoadingParameters where
  massFraction : ℝ
  specificArea : ℝ
  molarMassCat : ℝ
  avogadro : ℝ
  massFraction_pos : 0 < massFraction
  massFraction_lt_one : massFraction < 1
  specificArea_pos : 0 < specificArea
  molarMassCat_pos : 0 < molarMassCat
  avogadro_pos : 0 < avogadro

/-- One square metre expressed in square nanometres: `1 m² = 10¹⁸ nm²`. -/
def nm2PerM2 : ℝ := 1e18

/-- Mass of support (g) beneath a 1 nm² patch: the reciprocal of the
specific surface area after converting `m²` to `nm²`,
`m_sup = 1 / (S · 10¹⁸)`. -/
noncomputable def supportMassPerNm2 (p : LoadingParameters) : ℝ :=
  1 / (p.specificArea * nm2PerM2)

/-- Catalyst mass (g) per nm², the unique positive solution `m_cat` of the
mass-fraction law `ω_cat = m_cat / (m_cat + m_sup)` at fixed support mass
`m_sup = supportMassPerNm2 p`, namely
`m_cat = ω_cat / (1 - ω_cat) · m_sup`. -/
noncomputable def catMassPerNm2 (p : LoadingParameters) : ℝ :=
  p.massFraction / (1 - p.massFraction) * supportMassPerNm2 p

/-- Number of catalytic molecules per nm² of loaded support:
`N_cat = (m_cat / M_cat) · N_A`. -/
noncomputable def moleculesPerNm2 (p : LoadingParameters) : ℝ :=
  catMassPerNm2 p / p.molarMassCat * p.avogadro

/-- Bridge to the governing law: the solved catalyst mass
`catMassPerNm2 p` is exactly the mass for which the catalyst fraction of
the loaded support equals `p.massFraction`. -/
theorem massFraction_law (p : LoadingParameters) :
    p.massFraction =
      catMassPerNm2 p / (catMassPerNm2 p + supportMassPerNm2 p) := by
  have hw : (1 : ℝ) - p.massFraction ≠ 0 :=
    ne_of_gt (sub_pos.mpr p.massFraction_lt_one)
  have hn : (0 : ℝ) < nm2PerM2 := by norm_num [nm2PerM2]
  have hspos : (0 : ℝ) < supportMassPerNm2 p := by
    unfold supportMassPerNm2
    exact one_div_pos.mpr (mul_pos p.specificArea_pos hn)
  have hs : supportMassPerNm2 p ≠ 0 := ne_of_gt hspos
  have hcat : catMassPerNm2 p =
      p.massFraction / (1 - p.massFraction) * supportMassPerNm2 p := rfl
  have hsum : p.massFraction / (1 - p.massFraction) * supportMassPerNm2 p
        + supportMassPerNm2 p
      = supportMassPerNm2 p / (1 - p.massFraction) := by
    field_simp
    ring
  rw [hcat, hsum]
  field_simp

/-- The numerical data of subquestion 8.5: `ω_cat = 3.8 %`,
`S = 17.8 m² g⁻¹`, `M_cat = 557.21 g mol⁻¹`, and
`N_A = 6.02 × 10²³ mol⁻¹` (the value the marking scheme computes with). -/
def problemParameters : LoadingParameters where
  massFraction := 0.038
  specificArea := 17.8
  molarMassCat := 557.21
  avogadro := 6.02e23
  massFraction_pos := by norm_num
  massFraction_lt_one := by norm_num
  specificArea_pos := by norm_num
  molarMassCat_pos := by norm_num
  avogadro_pos := by norm_num

/-- Support mass under 1 nm² for the problem data; the marking-scheme
readout is `1 / (17.8 × 10¹⁸) g ≈ 5.618 × 10⁻²⁰ g`. -/
theorem supportMassPerNm2_problem :
    supportMassPerNm2 problemParameters = 1 / (17.8 * 1e18) := by
  rfl

/-- The support mass under 1 nm² matches the marking-scheme intermediate
`5.618 × 10⁻²⁰ g`. -/
theorem supportMassPerNm2_problem_bounds :
    5.61e-20 ≤ supportMassPerNm2 problemParameters ∧
      supportMassPerNm2 problemParameters ≤ 5.62e-20 := by
  rw [supportMassPerNm2_problem]
  constructor <;> norm_num

/-- Catalyst mass per nm² for the problem data matches the marking-scheme
intermediate `m_cat = 2.219 × 10⁻²¹ g`. -/
theorem catMassPerNm2_problem_bounds :
    2.21e-21 ≤ catMassPerNm2 problemParameters ∧
      catMassPerNm2 problemParameters ≤ 2.22e-21 := by
  have h : catMassPerNm2 problemParameters
      = 0.038 / (1 - 0.038) * (1 / (17.8 * 1e18)) := rfl
  rw [h]
  constructor <;> norm_num

/-- Closed form of the requested molecule count for the problem data. -/
theorem moleculesPerNm2_problem_eq :
    moleculesPerNm2 problemParameters =
      0.038 / (1 - 0.038) * (1 / (17.8 * 1e18)) / 557.21 * 6.02e23 := by
  rfl

/-- **Main target (8.5).** The number of catalytic molecules of **1** per
nm² of C₃N₄ lies in `[2.35, 2.45)`, i.e. `N_cat` rounds to the recorded
answer `N_cat ≈ 2.4` molecules per nm². -/
theorem moleculesPerNm2_problem_rounds :
    2.35 ≤ moleculesPerNm2 problemParameters ∧
      moleculesPerNm2 problemParameters < 2.45 := by
  rw [moleculesPerNm2_problem_eq]
  constructor <;> norm_num

end IChO2026T8A5
