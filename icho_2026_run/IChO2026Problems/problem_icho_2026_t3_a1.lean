import Mathlib
import CRNT.Basic.Complex
import IChO2026Chem

/-!
# IChO 2026 T3-A1: elemental composition of COF-1

The diagram in the question is the source of the atom inventory below.  We
represent a chosen dashed supercell, containing two primitive formula units,
rather than storing the requested empirical formula as a datum.  The empirical
formula is then the primitive formula associated to that atom inventory.

Atomic masses are numerical values in `g mol⁻¹`, and the reported carbon
composition is a percentage (so it includes the factor `100`).
-/

namespace IChO2026Problems.T3A1

/-- The four element labels occurring in the COF-1 formula requested in T3-A1.
The polymeric framework identity is kept separate from these scalar counts. -/
private inductive COF1Element where
  | carbon
  | hydrogen
  | boron
  | oxygen
  deriving DecidableEq, Repr

/-- A chemical formula is a nonnegative stoichiometric vector over the element
labels.  This reuses the generic reaction-network representation of a complex. -/
private abbrev Formula := CRNT.Complex COF1Element

namespace Formula

/-- Construct a formula from counts in the conventional order C, H, B, O. -/
private def ofCounts (carbon hydrogen boron oxygen : ℕ) : Formula
  | .carbon => carbon
  | .hydrogen => hydrogen
  | .boron => boron
  | .oxygen => oxygen

/-- `n` copies of a formula, with stoichiometric coefficients multiplied
pointwise. -/
private def scale (n : ℕ) (formula : Formula) : Formula :=
  fun element => n * formula element

/-- A formula is primitive when no integer greater than one divides every
element count. -/
private def IsPrimitive (formula : Formula) : Prop :=
  ∀ n : ℕ, 1 < n → ¬ ∀ element : COF1Element, n ∣ formula element

/-- `candidate` is an empirical formula for `formula` precisely when the latter
is a positive whole-number multiple of the former and the candidate is
primitive. -/
private def IsEmpiricalFormulaOf (formula candidate : Formula) : Prop :=
  ∃ multiplicity : ℕ, 0 < multiplicity ∧
    formula = scale multiplicity candidate ∧ IsPrimitive candidate

/-- Standard atomic masses, expressed numerically in `g mol⁻¹`. -/
private structure AtomicMasses where
  carbon : ℝ
  hydrogen : ℝ
  boron : ℝ
  oxygen : ℝ

/-- The molar mass of a formula calculated from a supplied atomic-mass table. -/
private def molarMass (masses : AtomicMasses) (formula : Formula) : ℝ :=
  masses.carbon * formula .carbon +
    masses.hydrogen * formula .hydrogen +
      masses.boron * formula .boron +
        masses.oxygen * formula .oxygen

/-- Carbon's percentage by mass in a formula. -/
noncomputable def carbonMassPercentage (masses : AtomicMasses) (formula : Formula) : ℝ :=
  100 * (masses.carbon * formula .carbon) / molarMass masses formula

/-- A numerical percentage agrees with a value printed to two decimal places.
The strict half-hundredth bound records ordinary nearest-hundredth rounding. -/
private def AgreesToTwoDecimalPlaces (value reported : ℝ) : Prop :=
  |value - reported| < 1 / 200

end Formula

/-- The C₁₈H₈B₂O₄ inventory obtained by counting the atoms in a dashed COF-1
supercell in the structural diagram.  It contains two primitive units; this is
structural evidence, not the requested empirical-formula conclusion. -/
private def COF1DashedCellAtomInventory (cell : Formula) : Prop :=
  cell .carbon = 18 ∧
    cell .hydrogen = 8 ∧
      cell .boron = 2 ∧
        cell .oxygen = 4

/-- The atomic masses used in the official calculation.  These are empirical
inputs, so they are supplied as hypotheses rather than axioms of chemistry. -/
private def AtomicMasses.matchesOfficialCalculation (masses : Formula.AtomicMasses) : Prop :=
  masses.carbon = 12.01 ∧
    masses.hydrogen = 1.008 ∧
      masses.boron = 10.81 ∧
        masses.oxygen = 16.00

/-- The formula requested in T3-A1, represented by its element-count vector
`C₉H₄BO₂`. -/
private def cof1EmpiricalFormula : Formula := Formula.ofCounts 9 4 1 2

/--
Counting the dashed COF-1 supercell gives a positive two-fold multiple of the
primitive formula `C₉H₄BO₂`.  With the atomic masses used by the official
solution, carbon's mass percentage is defined (the molar mass is positive) and
rounds to `69.77%` to two decimal places.
-/
theorem cof1_empirical_formula_and_carbon_mass_percentage
    (cell : Formula)
    (masses : Formula.AtomicMasses)
    (hstructure : COF1DashedCellAtomInventory cell)
    (hmasses : AtomicMasses.matchesOfficialCalculation masses) :
    Formula.IsEmpiricalFormulaOf cell cof1EmpiricalFormula ∧
      0 < Formula.molarMass masses cof1EmpiricalFormula ∧
        Formula.AgreesToTwoDecimalPlaces
          (Formula.carbonMassPercentage masses cof1EmpiricalFormula) 69.77 := by
  rcases hstructure with ⟨hcarbon, hhydrogen, hboron, hoxygen⟩
  rcases hmasses with ⟨hmcarbon, hmhydrogen, hmboron, hmoxygen⟩
  constructor
  · refine ⟨2, by norm_num, ?_, ?_⟩
    · funext element
      cases element <;>
        simp [Formula.scale, cof1EmpiricalFormula, Formula.ofCounts, hcarbon,
          hhydrogen, hboron, hoxygen]
    · intro n hn hdiv
      have hn_dvd_one : n ∣ 1 := by
        simpa [cof1EmpiricalFormula, Formula.ofCounts] using hdiv .boron
      have hn_one : n = 1 := Nat.dvd_one.mp hn_dvd_one
      omega
  constructor
  · norm_num [Formula.molarMass, cof1EmpiricalFormula, Formula.ofCounts,
      hmcarbon, hmhydrogen, hmboron, hmoxygen]
  · norm_num [Formula.AgreesToTwoDecimalPlaces, Formula.carbonMassPercentage,
      Formula.molarMass, cof1EmpiricalFormula, Formula.ofCounts, hmcarbon,
      hmhydrogen, hmboron, hmoxygen]

end IChO2026Problems.T3A1
