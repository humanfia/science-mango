import IChO2026Chem
import Mathlib

/-!
# IChO 2026 T5-A3: molecular formula of the fatty-acid residue in PL1

The source treats the formula of the hydrocarbon substituent `R` numerically,
but the sample, the fatty-acid residue, and the reductive-ozonolysis products
remain separate objects.  Atom counts are natural numbers; the two displayed
chemical calculation laws are expressed over `ℤ` and `ℚ` to avoid truncated
subtraction and to retain the half-bond contributions in the supplied count.
-/

namespace IChO2026Problems.T5A3

/-- The molecular formula requested in this subquestion, restricted to the
three elements occurring in a fatty acid `RCOOH`. -/
private structure MolecularFormula where
  carbonAtoms : ℕ
  hydrogenAtoms : ℕ
  oxygenAtoms : ℕ
  deriving Repr

/-- The hydrocarbon substituent `R = CₓHᵧ` of the fatty acid `RCOOH`. -/
private structure HydrocarbonResidue where
  carbonAtoms : ℕ
  hydrogenAtoms : ℕ
  deriving Repr

/-- Adding the carboxyl group converts `R = CₓHᵧ` into `RCOOH`. -/
private def fattyAcidFormula (residue : HydrocarbonResidue) : MolecularFormula where
  carbonAtoms := residue.carbonAtoms + 1
  hydrogenAtoms := residue.hydrogenAtoms + 1
  oxygenAtoms := 2

/-- A non-ionised PL1 molecule has four copies of its fatty-acid residue. -/
private def nonIonisedPL1ResidueMultiplicity : ℕ := 4

/-- A structural identifier for one organic product of reductive ozonolysis.
It distinguishes products without assuming any formula for them. -/
private structure OrganicProduct where
  structuralDescription : String
  deriving Repr

/-- The observed organic products of the reductive-ozonolysis experiment.
`productsDistinct` records “different organic products”; `equimolar` records
the equal-molar-amount condition from the source. -/
private structure ReductiveOzonolysisObservation where
  organicProductCount : ℕ
  products : Fin organicProductCount → OrganicProduct
  productsDistinct : Function.Injective products
  molarAmount : Fin organicProductCount → ℚ
  equimolar : ∀ i j, molarAmount i = molarAmount j

/-- The two count readouts attached to the same PL1 fatty-acid analysis. -/
private structure PL1FattyAcidAnalysis where
  residue : HydrocarbonResidue
  carbonCarbonDoubleBonds : ℕ
  ozonolysis : ReductiveOzonolysisObservation

/--
For an acyclic hydrocarbon substituent attached to the carboxyl carbon, every
C=C bond removes two hydrogens from the saturated `CₓH₂ₓ₊₁` residue.  This is
the source's equation `y = (2x + 1) - 2 N_{C=C}`, written without natural-number
subtraction.
-/
private def hasHydrocarbonValenceBalance (analysis : PL1FattyAcidAnalysis) : Prop :=
  (analysis.residue.hydrogenAtoms : ℤ) =
    2 * (analysis.residue.carbonAtoms : ℤ) + 1 -
      2 * (analysis.carbonCarbonDoubleBonds : ℤ)

/--
Reductive ozonolysis cleaves each C=C bond of the acyclic fatty-acid chain,
so the number of different organic products is one more than the number of
such double bonds.  This is the chemical bridge from the observation to the
unsaturation count.
-/
private def ozonolysisProductCountLaw (analysis : PL1FattyAcidAnalysis) : Prop :=
  analysis.ozonolysis.organicProductCount = analysis.carbonCarbonDoubleBonds + 1

/--
The total number of sigma and pi bonds in non-ionised PL1, using the fragment
calculation displayed in the official solution:
`(1/2)·1 + 5·2 + (23/2)·3 + 4·(3 + 2x + (1/2)y)`.
The factor `4` is the four fatty-acid residues and is kept explicit through
`nonIonisedPL1ResidueMultiplicity`.
-/
private def nonIonisedPL1BondCount (residue : HydrocarbonResidue) : ℚ :=
  (1 : ℚ) / 2 * 1 + 5 * 2 + (23 : ℚ) / 2 * 3 +
    nonIonisedPL1ResidueMultiplicity *
      (3 + 2 * (residue.carbonAtoms : ℚ) + (1 : ℚ) / 2 * residue.hydrogenAtoms)

/--
T5-A3.  If reductive ozonolysis of the fatty acid gives three different
equimolar organic products, the cleavage-count law gives two C=C bonds.  The
hydrocarbon valence balance and the supplied 255-bond total then determine
`R = C₁₇H₃₁` and hence `RCOOH = C₁₈H₃₂O₂`.

The hypotheses are source data or governing chemical laws.  In particular,
none contains the requested carbon or hydrogen atom counts as a premise.
-/
theorem fatty_acid_formula_from_ozonolysis_and_bond_total
    (analysis : PL1FattyAcidAnalysis)
    (hthree_products : analysis.ozonolysis.organicProductCount = 3)
    (hozonolysis_count : ozonolysisProductCountLaw analysis)
    (hvalence : hasHydrocarbonValenceBalance analysis)
    (hbond_total : nonIonisedPL1BondCount analysis.residue = 255) :
    analysis.carbonCarbonDoubleBonds = 2 ∧
    analysis.residue.carbonAtoms = 17 ∧
      analysis.residue.hydrogenAtoms = 31 ∧
          fattyAcidFormula analysis.residue = ⟨18, 32, 2⟩ := by
  rcases analysis with ⟨⟨x, y⟩, d, ozonolysis⟩
  have hd : d = 2 := by
    have hthree : ozonolysis.organicProductCount = 3 := by
      simpa using hthree_products
    have hcount : ozonolysis.organicProductCount = d + 1 := by
      simpa [ozonolysisProductCountLaw] using hozonolysis_count
    omega
  subst d
  have hvalence' : (y : ℤ) = 2 * (x : ℤ) - 3 := by
    unfold hasHydrocarbonValenceBalance at hvalence
    norm_num at hvalence ⊢
    linarith
  have hvalenceQ : (y : ℚ) = 2 * (x : ℚ) - 3 := by
    exact_mod_cast hvalence'
  have hbond' : (4 : ℚ) * x + y = 99 := by
    norm_num [nonIonisedPL1BondCount, nonIonisedPL1ResidueMultiplicity] at hbond_total ⊢
    linarith
  have hxQ : (x : ℚ) = 17 := by
    linarith [hvalenceQ, hbond']
  have hyQ : (y : ℚ) = 31 := by
    linarith [hvalenceQ, hxQ]
  have hx : x = 17 := by exact_mod_cast hxQ
  have hy : y = 31 := by exact_mod_cast hyQ
  subst x
  subst y
  norm_num [fattyAcidFormula]

end IChO2026Problems.T5A3
