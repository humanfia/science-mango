import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T5-A4: identification of iodine monobromide

The official solution makes the chemistry hidden behind “reacts in a similar
way” explicit: the reagent is `I–Hal`, and one molecule adds across each C=C
bond.  This file does not turn that statement into a four-item answer list.
Instead, elements range over the whole 118-element periodic table, molecular
formulae are arbitrary multisets of those elements, and the partner is
quantified subject only to membership in the complete group-17 family.

Molar mass and iodine mass are computed from the same formula inventory.  In
particular, choosing iodine as the partner produces `I₂` with two iodine atoms;
that branch is represented and rejected by the observed mass fraction before
the partner mass is identified from periodic-table data.
-/

namespace IChO2026Problems.T5A4

/-- A periodic-table element, represented by atomic number minus one.  Thus
the carrier has exactly the 118 currently named elements, rather than only the
elements occurring in the expected answer. -/
abbrev PeriodicElement := Fin 118

namespace PeriodicElement

def fluorine : PeriodicElement := ⟨8, by decide⟩
def chlorine : PeriodicElement := ⟨16, by decide⟩
def bromine : PeriodicElement := ⟨34, by decide⟩
def iodine : PeriodicElement := ⟨52, by decide⟩
def astatine : PeriodicElement := ⟨84, by decide⟩
def tennessine : PeriodicElement := ⟨116, by decide⟩

/-- Membership in group 17 of the periodic table.  The six alternatives are
the complete group, including astatine and tennessine; they are not a list of
candidate answers chosen for this problem. -/
def IsHalogen (element : PeriodicElement) : Prop :=
  element = fluorine ∨ element = chlorine ∨ element = bromine ∨
    element = iodine ∨ element = astatine ∨ element = tennessine

end PeriodicElement

/-- A molecular formula is a finite multiset of arbitrary periodic-table
elements. -/
structure MolecularFormula where
  atoms : Multiset PeriodicElement
  deriving DecidableEq

namespace MolecularFormula

/-- Formula mass is obtained by summing the atomic masses of the formula's
actual atom inventory. -/
noncomputable def molarMass
    (atomicMass : PeriodicElement → ℝ) (formula : MolecularFormula) : ℝ :=
  (formula.atoms.map atomicMass).sum

/-- Iodine mass is likewise determined by the iodine count in the same
inventory. -/
noncomputable def iodineMass
    (atomicMass : PeriodicElement → ℝ) (formula : MolecularFormula) : ℝ :=
  (formula.atoms.count PeriodicElement.iodine : ℝ) *
    atomicMass PeriodicElement.iodine

/-- The generic formula `IHal` displayed in the official solution.  When the
partner is iodine, the multiset contains two iodine atoms and hence is `I₂`. -/
def iodineHalide (partner : PeriodicElement) : MolecularFormula :=
  ⟨{PeriodicElement.iodine, partner}⟩

def diiodine : MolecularFormula := iodineHalide PeriodicElement.iodine
def iodineMonobromide : MolecularFormula := iodineHalide PeriodicElement.bromine

@[simp] theorem molarMass_iodineHalide
    (atomicMass : PeriodicElement → ℝ) (partner : PeriodicElement) :
    molarMass atomicMass (iodineHalide partner) =
      atomicMass PeriodicElement.iodine + atomicMass partner := by
  simp [molarMass, iodineHalide]

@[simp] theorem iodineMass_iodineHalide_of_ne
    (atomicMass : PeriodicElement → ℝ) (partner : PeriodicElement)
    (hpartner : partner ≠ PeriodicElement.iodine) :
    iodineMass atomicMass (iodineHalide partner) =
      atomicMass PeriodicElement.iodine := by
  have hiodine : PeriodicElement.iodine ≠ partner := Ne.symm hpartner
  simp [iodineMass, iodineHalide, hiodine]

@[simp] theorem iodineMass_diiodine
    (atomicMass : PeriodicElement → ℝ) :
    iodineMass atomicMass diiodine = 2 * atomicMass PeriodicElement.iodine := by
  simp [iodineMass, diiodine, iodineHalide]

end MolecularFormula

/-- Half a unit in the last place for a value printed to one decimal. -/
def RoundsToOneDecimal (value reported : ℝ) : Prop :=
  |value - reported| ≤ (1 : ℝ) / 20

/-- Periodic-table knowledge at the precision used in the competition.  It is
a general mass function on all 118 elements.  The fields expose the complete
group-17 lookup used here; bromine's standard mass is recorded by its printed
one-decimal interval because the source itself reports `79.9`. -/
structure PeriodicTableMassData where
  relativeAtomicMass : PeriodicElement → ℝ
  mass_positive : ∀ element, 0 < relativeAtomicMass element
  fluorine_mass : relativeAtomicMass PeriodicElement.fluorine = 19.0
  chlorine_mass : relativeAtomicMass PeriodicElement.chlorine = 35.45
  bromine_mass : RoundsToOneDecimal
    (relativeAtomicMass PeriodicElement.bromine) 79.9
  iodine_mass : relativeAtomicMass PeriodicElement.iodine = 126.9
  astatine_mass : relativeAtomicMass PeriodicElement.astatine = 210
  tennessine_mass : relativeAtomicMass PeriodicElement.tennessine = 294

/-- The fatty acid whose C=C bonds undergo both addition experiments. -/
structure FattyAcidSample where
  formula : MolecularFormula
  molarMass : ℝ
  molarMass_positive : 0 < molarMass
  carbonCarbonDoubleBonds : ℕ

/-- The printed iodine-number experiment: `100 g` of fatty acid consumes
`181.0 g` of molecular iodine. -/
structure IodineNumberExperiment (fattyAcid : FattyAcidSample) where
  sampleMass : ℝ
  iodineMassConsumed : ℝ
  sampleMass_value : sampleMass = 100
  iodineMassConsumed_value : iodineMassConsumed = 181.0

/-- One `I₂` molecule is consumed for each carbon-carbon double bond. -/
def IodineNumberExperiment.satisfiesAdditionMassLaw
    {fattyAcid : FattyAcidSample}
    (experiment : IodineNumberExperiment fattyAcid)
    (masses : PeriodicTableMassData) : Prop :=
  experiment.iodineMassConsumed =
    (fattyAcid.carbonCarbonDoubleBonds : ℝ) *
      MolecularFormula.molarMass masses.relativeAtomicMass
        MolecularFormula.diiodine /
      fattyAcid.molarMass * experiment.sampleMass

/-- The experiment with the unknown reagent.  The formula remains an
arbitrary periodic-element inventory.  `reagent_formula` is the explicit
`I–Hal` reaction bridge drawn in the official solution, and `partner_isHalogen`
ranges over the complete periodic-table group. -/
structure SimilarIodineAdditionExperiment
    (fattyAcid : FattyAcidSample) (reagent : MolecularFormula) where
  partner : PeriodicElement
  partner_isHalogen : partner.IsHalogen
  reagent_formula : reagent = MolecularFormula.iodineHalide partner
  iodineMassFraction : ℝ
  iodineMassFraction_value : iodineMassFraction = 0.3657

/-- Formula-derived mass conservation for adding one whole reagent molecule
per C=C bond.  The numerator uses the iodine count of that same formula, so
the `I₂` branch automatically contributes two iodine atoms. -/
def SimilarIodineAdditionExperiment.satisfiesAdductMassLaw
    {fattyAcid : FattyAcidSample} {reagent : MolecularFormula}
    (experiment : SimilarIodineAdditionExperiment fattyAcid reagent)
    (masses : PeriodicTableMassData) : Prop :=
  experiment.iodineMassFraction =
    (fattyAcid.carbonCarbonDoubleBonds : ℝ) *
        MolecularFormula.iodineMass masses.relativeAtomicMass reagent /
      (fattyAcid.molarMass +
        (fattyAcid.carbonCarbonDoubleBonds : ℝ) *
          MolecularFormula.molarMass masses.relativeAtomicMass reagent)

/-- The iodine-number calculation gives the official intermediate
`M(RCOOH) / N(C=C) ≈ 140.2 g mol⁻¹`. -/
theorem molar_mass_per_double_bond_from_iodine_number
    (fattyAcid : FattyAcidSample)
    (iodineExperiment : IodineNumberExperiment fattyAcid)
    (masses : PeriodicTableMassData)
    (hunsaturation : fattyAcid.carbonCarbonDoubleBonds = 2)
    (hstoichiometry : iodineExperiment.satisfiesAdditionMassLaw masses) :
    RoundsToOneDecimal
      (fattyAcid.molarMass / (fattyAcid.carbonCarbonDoubleBonds : ℝ)) 140.2 := by
  unfold IodineNumberExperiment.satisfiesAdditionMassLaw at hstoichiometry
  norm_num [MolecularFormula.diiodine, hunsaturation,
    iodineExperiment.sampleMass_value, iodineExperiment.iodineMassConsumed_value,
    masses.iodine_mass] at hstoichiometry
  have hMne : fattyAcid.molarMass ≠ 0 := ne_of_gt fattyAcid.molarMass_positive
  field_simp [hMne] at hstoichiometry
  unfold RoundsToOneDecimal
  rw [hunsaturation]
  norm_num
  rw [abs_le]
  constructor <;> nlinarith [hstoichiometry]

/-- The molecular-iodine alternative is represented by `partner = I`; the
formula-derived numerator then contains two iodine atoms and predicts the
officially rejected fraction near `0.6441`, not `0.3657`. -/
theorem partner_is_not_iodine
    (fattyAcid : FattyAcidSample)
    (reagent : MolecularFormula)
    (iodineExperiment : IodineNumberExperiment fattyAcid)
    (adductExperiment : SimilarIodineAdditionExperiment fattyAcid reagent)
    (masses : PeriodicTableMassData)
    (hunsaturation : fattyAcid.carbonCarbonDoubleBonds = 2)
    (hiodine : iodineExperiment.satisfiesAdditionMassLaw masses)
    (hadduct : adductExperiment.satisfiesAdductMassLaw masses) :
    adductExperiment.partner ≠ PeriodicElement.iodine := by
  intro hpartner
  unfold IodineNumberExperiment.satisfiesAdditionMassLaw at hiodine
  unfold SimilarIodineAdditionExperiment.satisfiesAdductMassLaw at hadduct
  have hformula : reagent = MolecularFormula.diiodine := by
    calc
      reagent = MolecularFormula.iodineHalide adductExperiment.partner :=
        adductExperiment.reagent_formula
      _ = MolecularFormula.diiodine := by
        rw [hpartner]
        simp [MolecularFormula.diiodine]
  have hreagentMass := congrArg
    (MolecularFormula.molarMass masses.relativeAtomicMass) hformula
  have hreagentIodineMass := congrArg
    (MolecularFormula.iodineMass masses.relativeAtomicMass) hformula
  rw [hreagentMass, hreagentIodineMass] at hadduct
  simp only [MolecularFormula.iodineMass_diiodine] at hadduct
  norm_num [MolecularFormula.diiodine, hunsaturation,
    iodineExperiment.sampleMass_value, iodineExperiment.iodineMassConsumed_value,
    adductExperiment.iodineMassFraction_value, masses.iodine_mass] at hiodine hadduct
  have hMne : fattyAcid.molarMass ≠ 0 := ne_of_gt fattyAcid.molarMass_positive
  have hdenom : 5 * fattyAcid.molarMass + 2538 ≠ 0 := by
    nlinarith [fattyAcid.molarMass_positive]
  field_simp [hMne] at hiodine
  field_simp [hdenom] at hadduct
  nlinarith [hiodine, hadduct]

/-- After the `I₂` branch is excluded, the two mass laws yield the official
co-atom calculation `A(Hal) ≈ 79.9 g mol⁻¹`. -/
theorem partner_atomic_mass_from_measurements
    (fattyAcid : FattyAcidSample)
    (reagent : MolecularFormula)
    (iodineExperiment : IodineNumberExperiment fattyAcid)
    (adductExperiment : SimilarIodineAdditionExperiment fattyAcid reagent)
    (masses : PeriodicTableMassData)
    (hunsaturation : fattyAcid.carbonCarbonDoubleBonds = 2)
    (hiodine : iodineExperiment.satisfiesAdditionMassLaw masses)
    (hadduct : adductExperiment.satisfiesAdductMassLaw masses) :
    RoundsToOneDecimal
      (masses.relativeAtomicMass adductExperiment.partner) 79.9 := by
  have hpartner := partner_is_not_iodine fattyAcid reagent iodineExperiment
    adductExperiment masses hunsaturation hiodine hadduct
  unfold IodineNumberExperiment.satisfiesAdditionMassLaw at hiodine
  unfold SimilarIodineAdditionExperiment.satisfiesAdductMassLaw at hadduct
  have hreagentMass := congrArg
    (MolecularFormula.molarMass masses.relativeAtomicMass)
      adductExperiment.reagent_formula
  have hreagentIodineMass := congrArg
    (MolecularFormula.iodineMass masses.relativeAtomicMass)
      adductExperiment.reagent_formula
  rw [hreagentMass, hreagentIodineMass] at hadduct
  simp only [MolecularFormula.molarMass_iodineHalide,
    MolecularFormula.iodineMass_iodineHalide_of_ne
      masses.relativeAtomicMass adductExperiment.partner hpartner] at hadduct
  norm_num [MolecularFormula.diiodine, hunsaturation,
    iodineExperiment.sampleMass_value, iodineExperiment.iodineMassConsumed_value,
    adductExperiment.iodineMassFraction_value, masses.iodine_mass] at hiodine hadduct
  have hMne : fattyAcid.molarMass ≠ 0 := ne_of_gt fattyAcid.molarMass_positive
  have hdenom :
      fattyAcid.molarMass * 10 +
        2 * (1269 + 10 * masses.relativeAtomicMass adductExperiment.partner) ≠ 0 := by
    have hp := masses.mass_positive adductExperiment.partner
    nlinarith [fattyAcid.molarMass_positive, hp]
  field_simp [hMne] at hiodine
  field_simp [hdenom] at hadduct
  unfold RoundsToOneDecimal
  rw [abs_le]
  constructor <;> nlinarith [hiodine, hadduct]

/-- Complete group-17 periodic-table lookup: a halogen whose atomic mass
rounds to `79.9` is bromine. -/
theorem halogen_of_atomic_mass_near_79_9
    (masses : PeriodicTableMassData)
    (element : PeriodicElement)
    (hhalogen : element.IsHalogen)
    (hmass : RoundsToOneDecimal (masses.relativeAtomicMass element) 79.9) :
    element = PeriodicElement.bromine := by
  rcases hhalogen with hF | hCl | hBr | hI | hAt | hTs
  · subst element
    norm_num [RoundsToOneDecimal, masses.fluorine_mass] at hmass
  · subst element
    norm_num [RoundsToOneDecimal, masses.chlorine_mass] at hmass
  · exact hBr
  · subst element
    norm_num [RoundsToOneDecimal, masses.iodine_mass] at hmass
  · subst element
    norm_num [RoundsToOneDecimal, masses.astatine_mass] at hmass
  · subst element
    norm_num [RoundsToOneDecimal, masses.tennessine_mass] at hmass

/--
T5-A4.  The T5-A3 conclusion of two C=C bonds is restated as the permitted
natural-language prerequisite.  The source iodine number, the official
`I–Hal` one-molecule addition scheme, the formula-derived adduct mass law, and
complete group-17 periodic-table data first determine the partner mass and
then the formula of the unknown reagent: `X = IBr`.
-/
theorem molecular_formula_of_X_is_IBr
    (fattyAcid : FattyAcidSample)
    (reagent : MolecularFormula)
    (iodineExperiment : IodineNumberExperiment fattyAcid)
    (adductExperiment : SimilarIodineAdditionExperiment fattyAcid reagent)
    (masses : PeriodicTableMassData)
    (hprevious_unsaturation : fattyAcid.carbonCarbonDoubleBonds = 2)
    (hiodine : iodineExperiment.satisfiesAdditionMassLaw masses)
    (hadduct : adductExperiment.satisfiesAdductMassLaw masses) :
    RoundsToOneDecimal
        (fattyAcid.molarMass / (fattyAcid.carbonCarbonDoubleBonds : ℝ)) 140.2 ∧
      RoundsToOneDecimal
          (masses.relativeAtomicMass adductExperiment.partner) 79.9 ∧
        adductExperiment.partner = PeriodicElement.bromine ∧
          reagent = MolecularFormula.iodineMonobromide := by
  have hmassPerBond := molar_mass_per_double_bond_from_iodine_number
    fattyAcid iodineExperiment masses hprevious_unsaturation hiodine
  have hpartnerMass := partner_atomic_mass_from_measurements fattyAcid reagent
    iodineExperiment adductExperiment masses hprevious_unsaturation hiodine hadduct
  have hpartner : adductExperiment.partner = PeriodicElement.bromine :=
    halogen_of_atomic_mass_near_79_9 masses adductExperiment.partner
      adductExperiment.partner_isHalogen hpartnerMass
  refine ⟨hmassPerBond, hpartnerMass, hpartner, ?_⟩
  rw [adductExperiment.reagent_formula, hpartner]
  rfl

end IChO2026Problems.T5A4
