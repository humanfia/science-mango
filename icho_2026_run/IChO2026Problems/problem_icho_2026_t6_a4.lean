import IChO2026Chem
import Mathlib

/-!
# IChO 2026 T6-A4: suggested assignments of four mass-spectrum peaks

The question asks to *suggest* identities.  Positive-ion mode and the absence
of fragmentation do not bound either the number of interlocked macrocycles or
the positive charge, so they do not support a global uniqueness claim.

Accordingly, this file gives an unbounded composition model for an intact
`C₄₈Eₖ` catenane with an arbitrary number of added protons and arbitrary
positive charge.  A peak assignment means that these generic composition,
nominal-mass, protonation, and charge equations reproduce the observed `m/z`.
The theorem verifies the four suggested assignments directly; it contains no
finite candidate universe and no precomputed peak-to-answer map.
-/

namespace IChO2026Problems.T6A4

/-- Atom counts for the elements occurring in macrocycle `E` and its adducts. -/
private structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- Integer nominal atomic masses, as explicitly requested in the question. -/
private structure IntegerAtomicMasses where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ

/-- The conventional integer masses used by the official calculation. -/
private def IntegerAtomicMasses.matchesSuppliedConvention
    (masses : IntegerAtomicMasses) : Prop :=
  masses.carbon = 12 ∧
    masses.hydrogen = 1 ∧
      masses.nitrogen = 14 ∧
        masses.oxygen = 16

/-- Nominal mass of a formula under the supplied integer-mass convention. -/
private def MolecularFormula.nominalMass
    (masses : IntegerAtomicMasses) (formula : MolecularFormula) : ℕ :=
  formula.carbon * masses.carbon +
    formula.hydrogen * masses.hydrogen +
      formula.nitrogen * masses.nitrogen +
        formula.oxygen * masses.oxygen

/-- Componentwise formula addition. -/
private def MolecularFormula.add (left right : MolecularFormula) : MolecularFormula where
  carbon := left.carbon + right.carbon
  hydrogen := left.hydrogen + right.hydrogen
  nitrogen := left.nitrogen + right.nitrogen
  oxygen := left.oxygen + right.oxygen

/-- `n` intact copies of a molecular formula. -/
private def MolecularFormula.scale (n : ℕ) (formula : MolecularFormula) : MolecularFormula where
  carbon := n * formula.carbon
  hydrogen := n * formula.hydrogen
  nitrogen := n * formula.nitrogen
  oxygen := n * formula.oxygen

/-- Macrocycle `E`; the formula `C₄₀H₃₄N₂O₃` is printed under its structure. -/
private def macrocycleEFormula : MolecularFormula := ⟨40, 34, 2, 3⟩

/-- The all-carbon cyclo[48]carbon component. -/
private def cyclo48CarbonFormula : MolecularFormula := ⟨48, 0, 0, 0⟩

/-- A proton adduct at nominal-mass precision. -/
private def protonFormula : MolecularFormula := ⟨0, 1, 0, 0⟩

/-- Exact nominal mass-to-charge ratios are rational numbers. -/
private abbrev MassToCharge := ℚ

/-- Formula of intact `[E + pH]`, used for the supplied 591 example. -/
private def protonatedMacrocycleEFormula (protonCount : ℕ) : MolecularFormula :=
  MolecularFormula.add macrocycleEFormula
    (MolecularFormula.scale protonCount protonFormula)

/--
Formula of an intact `C₄₈Eₖ` catenane carrying `p` added protons.
Both `k` and `p` are unbounded: no rubric-shaped finite carrier is imposed.
-/
private def intactCatenaneFormula
    (macrocycleECount protonCount : ℕ) : MolecularFormula :=
  MolecularFormula.add
    (MolecularFormula.add cyclo48CarbonFormula
      (MolecularFormula.scale macrocycleECount macrocycleEFormula))
    (MolecularFormula.scale protonCount protonFormula)

/-- Generic formula-derived nominal `m/z`, with charge kept independent. -/
private def nominalMassToCharge
    (masses : IntegerAtomicMasses) (formula : MolecularFormula)
    (positiveCharge : ℕ) : MassToCharge :=
  (formula.nominalMass masses : MassToCharge) / (positiveCharge : MassToCharge)

/--
The supplied free-`E` example is explained by a positive protonated intact ion
when its proton count supplies its charge and the nominal `m/z` is observed.
-/
private def ProtonatedMacrocycleEExplainsPeak
    (masses : IntegerAtomicMasses) (observed : MassToCharge)
    (protonCount positiveCharge : ℕ) : Prop :=
  0 < positiveCharge ∧
    protonCount = positiveCharge ∧
      nominalMassToCharge masses
        (protonatedMacrocycleEFormula protonCount) positiveCharge = observed

/--
An intact positive protonated `C₄₈Eₖ` composition explains a peak when
`k > 0`, its added protons supply its positive charge, and the generic nominal
mass/charge equation equals the observation.  There is deliberately no upper
bound on `k`, the proton count, or the charge.
-/
private def ProtonatedIntactCatenaneExplainsPeak
    (masses : IntegerAtomicMasses) (observed : MassToCharge)
    (macrocycleECount protonCount positiveCharge : ℕ) : Prop :=
  0 < macrocycleECount ∧
    0 < positiveCharge ∧
      protonCount = positiveCharge ∧
        nominalMassToCharge masses
          (intactCatenaneFormula macrocycleECount protonCount)
          positiveCharge = observed

/-- The formula masses that enter every peak equation. -/
private theorem source_formula_mass_bridge
    (masses : IntegerAtomicMasses)
    (hmasses : masses.matchesSuppliedConvention) :
    macrocycleEFormula.nominalMass masses = 590 ∧
      cyclo48CarbonFormula.nominalMass masses = 576 := by
  rcases hmasses with ⟨hC, hH, hN, hO⟩
  norm_num [MolecularFormula.nominalMass, macrocycleEFormula,
    cyclo48CarbonFormula, hC, hH, hN, hO]

/-!
The three catenane equations below instantiate the unbounded generic equation

`z * (m/z) = 576 + k * 590 + p`, with `p = z > 0`.

They give witnesses `(k,p,z) = (3,3,3)`, `(2,2,2)`, and `(3,2,2)` for
the observations 783, 879, and 1174 respectively.  Since the source asks for
suggestions and does not bound the admissible integers, no uniqueness result is
claimed.  The 591 example is the analogous free-macrocycle equation.
-/

/--
T6-A4.  The generic intact-composition and nominal mass/charge equations verify
the suggested assignments
`[E+H]⁺`, `[C₄₈E₃+3H]³⁺`, `[C₄₈E₂+2H]²⁺`, and
`[C₄₈E₃+2H]²⁺` for the peaks 591, 783, 879, and 1174.
-/
theorem identify_ions_at_observed_peaks
    (masses : IntegerAtomicMasses)
    (hmasses : masses.matchesSuppliedConvention) :
    macrocycleEFormula.nominalMass masses = 590 ∧
      cyclo48CarbonFormula.nominalMass masses = 576 ∧
      ProtonatedMacrocycleEExplainsPeak masses 591 1 1 ∧
      ProtonatedIntactCatenaneExplainsPeak masses 783 3 3 3 ∧
      ProtonatedIntactCatenaneExplainsPeak masses 879 2 2 2 ∧
      ProtonatedIntactCatenaneExplainsPeak masses 1174 3 2 2 := by
  rcases masses with ⟨carbon, hydrogen, nitrogen, oxygen⟩
  simp only [IntegerAtomicMasses.matchesSuppliedConvention] at hmasses
  rcases hmasses with ⟨rfl, rfl, rfl, rfl⟩
  norm_num [ProtonatedMacrocycleEExplainsPeak,
    ProtonatedIntactCatenaneExplainsPeak, nominalMassToCharge,
    protonatedMacrocycleEFormula, intactCatenaneFormula,
    MolecularFormula.nominalMass, MolecularFormula.add, MolecularFormula.scale,
    macrocycleEFormula, cyclo48CarbonFormula, protonFormula]

end IChO2026Problems.T6A4
