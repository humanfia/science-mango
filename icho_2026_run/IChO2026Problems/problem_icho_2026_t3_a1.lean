import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem 3, subquestion 3.1 — empirical formula of COF-1
and mass percentage of carbon

## Source

58th International Chemistry Olympiad, Tashkent, Uzbekistan, 2026, Theory
Problem T3 ("Into Reticular Chemistry"), subquestion 3.1 (2.0 pt).  Problem
PDF page 25 (printed page Q3-1); page image `T3_page-1.png`.

The source figure shows the honeycomb 2D-COF "COF-1" assembled from two
building blocks (black and red bold lines denote different building blocks):

* **B3** — 2,3,6,7,10,11-hexahydroxytriphenylene (HHTP), a 3-connected
  triphenylene core bearing six phenolic –OH groups: formula `C₁₈H₁₂O₆`;
* **A2** — benzene-1,4-diboronic acid (BDBA), a 2-connected linker bearing
  two boronic acid –B(OH)₂ groups: formula `C₆H₈B₂O₄`.

Each boronic acid group condenses with a catechol pair of HHTP to form a
boronate ester ring, releasing two water molecules per boron atom (the
scheme marks the COF-1 arrow with `−H₂O`).  The dashed-line repeat unit of
the honeycomb net therefore contains 2 HHTP and 3 BDBA building blocks and
is formed with the loss of 12 H₂O.

## Assumption / target split

*Assumptions (source data).*
* Monomer formulas `C₁₈H₁₂O₆` (B3) and `C₆H₈B₂O₄` (A2) read off the
  structures drawn in the source figure (`hhtp`, `bdba`), and `H₂O`
  (`water`) as the only by-product.
* The repeat-unit atom balance
  `repeat unit + 12 H₂O = 2 B3 + 3 A2`
  taken as hypothesis `hBalance` (dashed repeat unit and `−H₂O` arrows of
  the source figure).  Atom counts are natural numbers, so conservation,
  nonnegativity and the 2:3 honeycomb stoichiometry are preserved.
* Atomic-mass readouts `C 12.01, H 1.008, B 10.81, O 16.00` g/mol
  (`standardAtomicMass`) — exactly the values the official marking scheme
  uses in `12.01·9 / (12.01·9 + 4·1.008 + 10.81 + 32) · 100%`.

*Targets (requested conclusions, 2.0 pt).*
1. The empirical formula of COF-1 is `C₉H₄BO₂` (obtained by reducing the
   repeat-unit counts by their greatest common divisor, 6);
2. the carbon mass percentage of COF-1, rounded to two decimal places, is
   `69.77 %`.

The recorded answer appears only in theorem conclusions, never in a
premise, structure field, or definition.
-/

namespace IChO2026Problems.Icho2026T3A1

/-- The elements occurring in the COF-1 building blocks of the source figure. -/
inductive Element where
  | C
  | H
  | B
  | O
  deriving DecidableEq, Repr

deriving instance Fintype for Element

/-- A molecular/empirical formula over `Element`: the atom count of each element.

Pointwise `+` and `n • ·` model combining and multiplying building blocks;
natural-number subtraction is never needed because the atom balance is stated
with the by-product water on the repeat-unit side. -/
abbrev Formula := Element → ℕ

/-- Building block **B3** of the source figure: hexahydroxytriphenylene (HHTP),
`C₁₈H₁₂O₆` — a triphenylene core (`C₁₈`) with six ring hydrogens and six
phenolic –OH groups. -/
def hhtp : Formula
  | .C => 18
  | .H => 12
  | .B => 0
  | .O => 6

/-- Building block **A2** of the source figure: benzene-1,4-diboronic acid
(BDBA), `C₆H₈B₂O₄` — a para-disubstituted benzene (`C₆H₄`) carrying two
–B(OH)₂ groups. -/
def bdba : Formula
  | .C => 6
  | .H => 8
  | .B => 2
  | .O => 4

/-- Water, the sole condensation by-product of the source scheme (`−H₂O`), `H₂O`. -/
def water : Formula
  | .C => 0
  | .H => 2
  | .B => 0
  | .O => 1

/-- Atomic-mass readouts (g/mol) supplied with the exam and used verbatim by the
official marking scheme: C 12.01, H 1.008, B 10.81, O 16.00. -/
def standardAtomicMass : Element → ℝ
  | .C => 12.01
  | .H => 1.008
  | .B => 10.81
  | .O => 16.00

/-- The molar-mass readout (g/mol) of a formula under an atomic-mass assignment:
`M(f) = Σ_e amu(e) · f(e)`. -/
noncomputable def formulaMass (amu : Element → ℝ) (f : Formula) : ℝ :=
  ∑ e, amu e * (f e : ℝ)

/-- The empirical formula of a compound: atom counts reduced by their greatest
common divisor, i.e. the simplest whole-number element ratio. -/
def empiricalFormula (f : Formula) : Formula :=
  fun e => f e / Finset.univ.gcd f

/-- The mass percentage of element `e` in a compound of formula `f`:
`100 · amu(e) · f(e) / M(f)` (a percent readout, so `69.77…` for carbon here). -/
noncomputable def elementMassPercentage
    (amu : Element → ℝ) (e : Element) (f : Formula) : ℝ :=
  100 * (amu e * (f e : ℝ)) / formulaMass amu f

/-- Intermediate composition of one COF-1 repeat unit: the atom balance of the
condensation `repeat unit + 12 H₂O = 2 B3 + 3 A2` forces the repeat-unit formula
`C₅₄H₂₄B₆O₁₂`. -/
theorem cof1_repeatUnit_formula (repeatUnit : Formula)
    (hBalance : repeatUnit + 12 • water = 2 • hhtp + 3 • bdba) :
    repeatUnit = fun
      | .C => 54
      | .H => 24
      | .B => 6
      | .O => 12 := by
  funext e
  have h := congrFun hBalance e
  cases e <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhtp, bdba, water] at h <;>
    dsimp only <;>
    omega

/-- **T3.1 target.**  Any COF-1 repeat unit satisfying the condensation atom
balance of the source figure has empirical formula `C₉H₄BO₂`, and its carbon
mass percentage rounded to two decimal places is `69.77 %`
(`round (percentage · 100) = 6977`, i.e. the percentage lies in
`[69.765, 69.775)`). -/
theorem cof1_empirical_formula_and_carbon_mass_percentage (repeatUnit : Formula)
    (hBalance : repeatUnit + 12 • water = 2 • hhtp + 3 • bdba) :
    (empiricalFormula repeatUnit = fun
        | .C => 9
        | .H => 4
        | .B => 1
        | .O => 2) ∧
      round (elementMassPercentage standardAtomicMass .C repeatUnit * 100) = 6977 := by
  have hR : repeatUnit = (fun
      | .C => 54
      | .H => 24
      | .B => 6
      | .O => 12) := cof1_repeatUnit_formula repeatUnit hBalance
  have huniv : (Finset.univ : Finset Element)
      = {Element.C, Element.H, Element.B, Element.O} := by
    ext e
    fin_cases e <;> simp
  have hgcd : Finset.univ.gcd (fun (e : Element) => match e with
        | .C => 54
        | .H => 24
        | .B => 6
        | .O => 12) = 6 := by
    decide
  constructor
  · rw [hR]
    funext e
    cases e <;> simp only [empiricalFormula] <;> rw [hgcd]
  · rw [hR, round_eq, Int.floor_eq_iff]
    simp [elementMassPercentage, formulaMass, huniv, Finset.sum_insert,
      Finset.sum_singleton, standardAtomicMass]
    norm_num

end IChO2026Problems.Icho2026T3A1
