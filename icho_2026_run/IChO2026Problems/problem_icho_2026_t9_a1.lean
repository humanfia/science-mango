import Mathlib

/-!
# IChO 2026, Theory Problem T9 (Cyclodextrin Chemistry), subquestion 9.1

Blueprint chapter:
`blueprint/src/chapters/IChO2026Problems_problem_icho_2026_t9_a1.tex`
(`thm:physics:icho_2026_t9_a1:target`).
Source report: `reports/icho_2026/problem_icho_2026_t9_a1.source.json`.
Visual evidence: `../icho_2026_source/image/T9_page-1.png`.

## Source contract

**Shared context (T9 stem, problem page Q9-1).** Cyclodextrins (CD) are cyclic
oligosaccharides of glucose subunits joined by α-1,4-glycosidic bonds.  The three
most common cyclodextrins (α-, β-, γ-cyclodextrin) contain 6, 7, and 8
α-D-glucopyranoside units, respectively.  The page figure labels the cyclic
structure "n = 7, β-CD" and counts its substituents as `(CH₂OH)₇` and `(OH)₁₄`.

**Question 9.1 (2.0 pt).** Calculate the molar mass of β-CD.
Assume `M_w(glucose) = 180.16 g mol⁻¹`.

**Marking scheme (official solution).**
`M_w(β-cyclodextrin) = 180.16 · 7 − 18.016 · 7 = 1135.01 g mol⁻¹`.

## Assumption / target split

Assumptions (all sourced, none is the requested answer):

* `glucoseMolarMass = 180.16 g mol⁻¹` — explicit datum of subquestion 9.1.
* `waterMolarMass = 18.016 g mol⁻¹` — the water molar mass the official marking
  scheme subtracts seven times (standard table value, `H = 1.008`, `O = 16.00`).
* `Cyclodextrin.glucoseUnits` — 6/7/8 units for α/β/γ-CD, stated in the T9 stem.
* `cyclicGlycosidicBonds n = n` — a *cyclic* chain of `n` glucopyranose units has
  exactly `n` α-1,4-glycosidic bonds (each unit's anomeric C1 is linked to the next
  unit's O4, and cyclization links the last unit back to the first; a linear chain
  would have `n − 1`).
* Condensation mass balance — every glycosidic bond is formed with elimination of
  one water molecule, hence `M = n · M(glucose) − n · M(H₂O)` for the ring.

Targets (the requested conclusion of 9.1, worth 2 points):

* `betaCD_molarMass_exact`: the stoichiometric value is exactly
  `1135.008 g mol⁻¹` (`7 · 180.16 − 7 · 18.016`).
* `betaCD_molarMass_reported`: rounded to two decimal places it is
  `1135.01 g mol⁻¹`, the value printed by the marking scheme.  Rounding is
  stated explicitly because `1135.008 ≠ 1135.01` in `ℝ`; the printed answer is
  the two-decimal rounding of the exact stoichiometric value.

The recorded answer (`1135.01`) appears only in theorem conclusions, never in a
definition, structure field, or hypothesis.

## Conventions

Following the shared-module convention of `IChO2026Chem.Kinetics`, quantities are
represented by their real numerical readouts in the source's units
(here `g mol⁻¹`); species identity is carried by the declaration names and
docstrings.  No configured package (Mathlib, Physlib, CRNT/"Chemistry") exposes
molar masses, cyclodextrins, or glycosidic-bond stoichiometry, so the smallest
faithful local interface is declared here.
-/

namespace IChO2026.T9.A1

/-- A molar mass, represented by its numerical readout in `g mol⁻¹`
(the unit used throughout the source). -/
abbrev MolarMass := ℝ

/-- **Problem datum (9.1).** The molar mass of glucose,
`M_w(glucose) = 180.16 g mol⁻¹`, given explicitly in the question. -/
def glucoseMolarMass : MolarMass := 180.16

/-- **Marking-scheme datum.** The molar mass of water,
`M_w(H₂O) = 18.016 g mol⁻¹`, as subtracted seven times in the official solution
`180.16 · 7 − 18.016 · 7` (the standard table value from `H = 1.008`,
`O = 16.00`). -/
def waterMolarMass : MolarMass := 18.016

/-- The three most common cyclodextrins named in the T9 stem.  The branches are
kept distinct so that no unit count is pre-selected for the requested species. -/
inductive Cyclodextrin where
  | alpha
  | beta
  | gamma
  deriving DecidableEq, Repr

/-- **Problem datum (T9 stem).** The number of α-D-glucopyranoside units in each
common cyclodextrin: 6 for α-CD, 7 for β-CD, 8 for γ-CD. -/
def Cyclodextrin.glucoseUnits : Cyclodextrin → ℕ
  | .alpha => 6
  | .beta => 7
  | .gamma => 8

/-- **Cyclicity fact (T9 stem + marking scheme).** A cyclic α-1,4-glucan of `n`
glucopyranose units contains exactly `n` glycosidic bonds: each unit's anomeric
C1 is linked to the next unit's O4, and ring closure links the last unit back to
the first (a linear chain would have `n − 1` bonds).  This is also the number of
water molecules eliminated in the condensation forming the ring. -/
def cyclicGlycosidicBonds (n : ℕ) : ℕ := n

/-- **Condensation mass balance.** Each glycosidic bond is formed by condensation
of two hydroxyl groups with elimination of one water molecule, so the molar mass
of a cyclic α-1,4-glucan of `n` glucose units is
`n · M_w(glucose) − n · M_w(H₂O)`. -/
def cyclicGlucanMolarMass (n : ℕ) : MolarMass :=
  (n : ℝ) * glucoseMolarMass - (cyclicGlycosidicBonds n : ℝ) * waterMolarMass

/-- The molar mass of a cyclodextrin, from its glucose-unit count and the
condensation mass balance of the glycosidic ring. -/
def Cyclodextrin.molarMass (cd : Cyclodextrin) : MolarMass :=
  cyclicGlucanMolarMass cd.glucoseUnits

/-- **T9-A1 target (exact).** The molar mass of β-cyclodextrin computed from the
condensation stoichiometry is exactly `1135.008 g mol⁻¹`:
`7 · 180.16 − 7 · 18.016 = 1135.008`. -/
theorem betaCD_molarMass_exact :
    Cyclodextrin.beta.molarMass = 1135.008 := by
  norm_num [Cyclodextrin.molarMass, cyclicGlucanMolarMass, cyclicGlycosidicBonds,
    glucoseMolarMass, waterMolarMass, Cyclodextrin.glucoseUnits]

/-- **T9-A1 target (as reported).** Rounded to two decimal places, the molar mass
of β-cyclodextrin is `1135.01 g mol⁻¹`, the value printed by the official
marking scheme. -/
theorem betaCD_molarMass_reported :
    (round (Cyclodextrin.beta.molarMass * 100) : ℝ) / 100 = 1135.01 := by
  have hr : round ((1135.008 : ℝ) * 100) = 113501 := by
    rw [round_eq, Int.floor_eq_iff]
    norm_num
  rw [betaCD_molarMass_exact, hr]
  norm_num

end IChO2026.T9.A1
