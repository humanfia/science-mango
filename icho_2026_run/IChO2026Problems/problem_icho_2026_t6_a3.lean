import IChO2026Chem
import Mathlib

/-!
# IChO 2026 T6-A3: halogen choice for AFM-mediated C18 synthesis

The source gives bond-dissociation energies for the four carbon-halogen
bonds and asks which halogenated reagent can be dehalogenated by electrons
accelerated through a 2.5 V potential.  Chemical identities (the C18 ring,
the C-X bond, the halogenated reagent, and the retro-Bergman route) remain
separate from their numerical energy readouts.
-/

namespace IChO2026Problems.T6A3

/-- The four halogens explicitly offered by the C-X bond-energy table. -/
private inductive Halogen where
  | fluorine
  | chlorine
  | bromine
  | iodine
  deriving DecidableEq, Repr

/-- A monocyclic all-carbon species, identified here by its number of carbon atoms. -/
private structure Cyclocarbon where
  carbonAtomCount : ℕ
  deriving DecidableEq, Repr

/-- The C18 carbon nanoring which is the intended product of this synthesis. -/
private def C18 : Cyclocarbon := ⟨18⟩

/-- A carbon-halogen bond.  Its carbon endpoint is fixed by the constructor. -/
private structure CarbonHalogenBond where
  halogen : Halogen
  deriving DecidableEq, Repr

/-- The route named in the current subquestion. -/
private inductive SynthesisRoute where
  | retroBergman
  deriving DecidableEq, Repr

/-- A halogenated precursor together with its stated nanoring product and route. -/
private structure HalogenatedReagent where
  productRing : Cyclocarbon
  carbonHalogenBond : CarbonHalogenBond
  route : SynthesisRoute
  deriving Repr

/-- Numerical voltage in V. -/
private abbrev Voltage := ℝ

/-- Numerical energy in kJ mol⁻¹. -/
private abbrev MolarEnergy := ℝ

/-- The voltage applied to the electrons in T6-A3. -/
private def appliedVoltage : Voltage := 2.5

/--
The standard conversion for the energy acquired by one mole of singly charged
electrons through one volt: `1 eV particle⁻¹ = 96.485 kJ mol⁻¹`.
This empirical conversion is used by the official solution to bridge voltage
and the bond-dissociation-energy units.
-/
private def electronVoltToMolarEnergy : MolarEnergy := 96.485

/-- The molar energy made available by electrons at a stated voltage. -/
private def molarElectronEnergyAt (voltage : Voltage) : MolarEnergy :=
  voltage * electronVoltToMolarEnergy

/-- The available energy for the 2.5 V condition in this subquestion. -/
private def availableMolarEnergy : MolarEnergy :=
  molarElectronEnergyAt appliedVoltage

/--
The source C-X bond-dissociation-energy table, in kJ mol⁻¹:
C-F 467, C-Cl 346, C-Br 290, and C-I 228.
-/
private def carbonHalogenBondDissociationEnergy (bond : CarbonHalogenBond) : MolarEnergy :=
  match bond.halogen with
  | .fluorine => 467
  | .chlorine => 346
  | .bromine => 290
  | .iodine => 228

/-- A reagent is in the stated C18 retro-Bergman context precisely when its
product and named route agree with the current subquestion. -/
private def IsC18RetroBergmanReagent (reagent : HalogenatedReagent) : Prop :=
  reagent.productRing = C18 ∧ reagent.route = .retroBergman

/--
The energetic bridge used for this classification: a C-X bond can be cleaved
by the AFM-mediated electron process when its dissociation energy does not
exceed the molar electron energy supplied by the applied voltage.
-/
private def IsCleavableAtAppliedVoltage (bond : CarbonHalogenBond) : Prop :=
  carbonHalogenBondDissociationEnergy bond ≤ availableMolarEnergy

/-- A stated C18 retro-Bergman precursor is possible exactly when its C-X bond
is energetically cleavable under the applied-electron condition. -/
private def IsPossibleC18RetroBergmanReagent (reagent : HalogenatedReagent) : Prop :=
  IsC18RetroBergmanReagent reagent ∧
    IsCleavableAtAppliedVoltage reagent.carbonHalogenBond

/-- The unit conversion in the official calculation before the halogen choice. -/
private theorem available_energy_from_2_5_volts :
    availableMolarEnergy = 241.2125 := by
  norm_num [availableMolarEnergy, molarElectronEnergyAt, appliedVoltage,
    electronVoltToMolarEnergy]

/--
T6-A3.  Under the supplied 2.5 V AFM-electron condition and the displayed
C-X bond-dissociation-energy table, iodine is the unique possible halogen in
a reagent for C18 synthesis by the retro-Bergman route.

The requested identity is a conclusion, not a field of the reagent or an
assumption.
-/
theorem possible_halogen_for_C18_retroBergman_at_2_5_volts
    (reagent : HalogenatedReagent)
    (hcontext : IsC18RetroBergmanReagent reagent) :
    IsPossibleC18RetroBergmanReagent reagent ↔
      reagent.carbonHalogenBond.halogen = .iodine := by
  constructor
  · rintro ⟨_, hcleavable⟩
    cases hhalogen : reagent.carbonHalogenBond.halogen
    · norm_num [IsCleavableAtAppliedVoltage,
        carbonHalogenBondDissociationEnergy, availableMolarEnergy,
        molarElectronEnergyAt, appliedVoltage, electronVoltToMolarEnergy,
        hhalogen] at hcleavable
    · norm_num [IsCleavableAtAppliedVoltage,
        carbonHalogenBondDissociationEnergy, availableMolarEnergy,
        molarElectronEnergyAt, appliedVoltage, electronVoltToMolarEnergy,
        hhalogen] at hcleavable
    · norm_num [IsCleavableAtAppliedVoltage,
        carbonHalogenBondDissociationEnergy, availableMolarEnergy,
        molarElectronEnergyAt, appliedVoltage, electronVoltToMolarEnergy,
        hhalogen] at hcleavable
    · simp
  · intro hhalogen
    constructor
    · exact hcontext
    · norm_num [IsCleavableAtAppliedVoltage,
        carbonHalogenBondDissociationEnergy, availableMolarEnergy,
        molarElectronEnergyAt, appliedVoltage, electronVoltToMolarEnergy,
        hhalogen]

end IChO2026Problems.T6A3
