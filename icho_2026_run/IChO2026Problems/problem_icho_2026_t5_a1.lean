import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T5-A1: parity of the number of type-a cardiolipin fragments

The wavy line on a supplied fragment denotes one atom-side of a bond that is
to be made when PL1 is assembled.  The source diagram gives one such site on a
fragment of type `a`, two on `b`, three on `c`, and one on `d`.  A completed
assembly pairs every open site with exactly one other open site.

The chemical information that PL1 is non-ionised, its `R` group is a
hydrocarbon substituent, and it has no peroxide bond is retained in the model,
although the parity calculation itself uses only the fragment-site equation.
-/

namespace IChO2026Problems.T5A1

/-- The four structural-element types displayed for the PL1 construction. -/
private inductive FragmentType where
  | typeA
  | typeBPhosphoricAcid
  | typeCGlycerol
  | typeDFattyAcid
  deriving DecidableEq, Fintype, Repr

/-- The types of covalent bonds relevant to the source's peroxide exclusion. -/
private inductive BondKind where
  | ordinaryCovalent
  | peroxide
  deriving DecidableEq, Repr

/-- A hydrocarbon substituent `R`, represented only by its carbon and hydrogen
inventory; no heteroatom can occur in this type. -/
private structure HydrocarbonSubstituent where
  carbonAtomCount : ℕ
  hydrogenAtomCount : ℕ
  carbonAtomCount_pos : 0 < carbonAtomCount

/-- Multiplicities of the four supplied structural elements. -/
private structure FragmentInventory where
  count : FragmentType → ℕ

/-- The number of open (wavy-line) atom sites supplied by one fragment. -/
private def openSiteCount : FragmentType → ℕ
  | .typeA => 1
  | .typeBPhosphoricAcid => 2
  | .typeCGlycerol => 3
  | .typeDFattyAcid => 1

/-- The total number of atom sites carrying a broken bond in the fragments
before the molecule is assembled. -/
private def totalBrokenBondSites (inventory : FragmentInventory) : ℕ :=
  inventory.count .typeA * openSiteCount .typeA +
    inventory.count .typeBPhosphoricAcid * openSiteCount .typeBPhosphoricAcid +
      inventory.count .typeCGlycerol * openSiteCount .typeCGlycerol +
        inventory.count .typeDFattyAcid * openSiteCount .typeDFattyAcid

/-- Data for an attempted assembly of the named PL1 sample.  `joiningBondCount`
counts only the new bonds that join fragment sites; `productBondKind` records
all bonds of the resulting product, so the peroxide condition concerns the
whole product rather than merely the new joins. -/
private structure PL1Assembly where
  fragments : FragmentInventory
  R : HydrocarbonSubstituent
  netCharge : ℤ
  joiningBondCount : ℕ
  productBondCount : ℕ
  productBondKind : Fin productBondCount → BondKind
  joiningBondsAreProductBonds : joiningBondCount ≤ productBondCount

/-- The non-ionised form has zero net charge. -/
private def IsNonIonised (assembly : PL1Assembly) : Prop :=
  assembly.netCharge = 0

/-- PL1 contains no peroxide bond. -/
private def HasNoPeroxideBonds (assembly : PL1Assembly) : Prop :=
  ∀ bond, assembly.productBondKind bond ≠ .peroxide

/-- The source fixes the multiplicities of types `b`, `c`, and `d`; the
multiplicity of type `a` is the unknown `n` asked for in T5-A1. -/
private def MatchesT5A1FragmentQuantities (assembly : PL1Assembly) : Prop :=
  assembly.fragments.count .typeBPhosphoricAcid = 2 ∧
    assembly.fragments.count .typeCGlycerol = 3 ∧
      assembly.fragments.count .typeDFattyAcid = 4

/-- Completeness of the assembly: every broken-bond atom site is paired with
one other site, and hence contributes to exactly one newly formed bond. -/
private def AllFragmentSitesArePaired (assembly : PL1Assembly) : Prop :=
  totalBrokenBondSites assembly.fragments = 2 * assembly.joiningBondCount

/--
For the non-ionised, peroxide-free PL1 assembled from the displayed fragment
multiplicities, the unknown number `n` of type-a fragments is odd.  The
recorded answer is not assumed: it follows from the fixed 17 non-a open sites
and the fact that completed bonds consume open sites in pairs.
-/
theorem type_a_fragment_count_is_odd
    (assembly : PL1Assembly)
    (hquantities : MatchesT5A1FragmentQuantities assembly)
    (hneutral : IsNonIonised assembly)
    (hperoxideFree : HasNoPeroxideBonds assembly)
    (hpaired : AllFragmentSitesArePaired assembly) :
    Odd (assembly.fragments.count .typeA) := by
  rcases hquantities with ⟨hB, hC, hD⟩
  have hfixedSites :
      totalBrokenBondSites assembly.fragments =
        assembly.fragments.count .typeA + 17 := by
    norm_num [totalBrokenBondSites, openSiteCount, hB, hC, hD]
  have hparityEquation :
      assembly.fragments.count .typeA + 17 = 2 * assembly.joiningBondCount :=
    hfixedSites.symm.trans hpaired
  /- The remaining arithmetic step rewrites `Odd` as `2 * q + 1` and uses
  `q = joiningBondCount - 9`.  The chemical hypotheses above deliberately
  remain contextual: the source's pairing equation is the only parity bridge. -/
  refine ⟨assembly.joiningBondCount - 9, ?_⟩
  omega

end IChO2026Problems.T5A1
