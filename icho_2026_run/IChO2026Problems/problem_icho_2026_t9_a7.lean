import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T9-A7: nominal `m/z` values of the degradation products of L

This question uses integer atomic masses.  The two molecular formulae are kept
separate from the observed positive-ion readouts: each readout is assigned to
the singly charged sodium adduct of a named degradation product from `L`.
The formulae record the two or three `C₂₇H₂₈O₅` units, one `C₂₂H₂₅O₄` unit,
and the `C₂H₃O₂` acetate contribution displayed in the source figure.
-/

namespace IChO2026Problems.T9A7

/-- A molecular formula restricted to the four elements occurring in the
neutral products and their sodium adducts. -/
private structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  sodium : ℕ
  deriving DecidableEq, Repr

namespace MolecularFormula

/-- Formula addition, used to assemble a degradation product from its
displayed fragments and to add sodium to a neutral product. -/
private def add (left right : MolecularFormula) : MolecularFormula where
  carbon := left.carbon + right.carbon
  hydrogen := left.hydrogen + right.hydrogen
  oxygen := left.oxygen + right.oxygen
  sodium := left.sodium + right.sodium

/-- Repeated copies of one fragment formula. -/
private def scale (count : ℕ) (formula : MolecularFormula) : MolecularFormula where
  carbon := count * formula.carbon
  hydrogen := count * formula.hydrogen
  oxygen := count * formula.oxygen
  sodium := count * formula.sodium

/-- The `C₂₇H₂₈O₅` fragment (unit 1) labelled in the degradation scheme. -/
private def unitOne : MolecularFormula := ⟨27, 28, 5, 0⟩

/-- The `C₂₂H₂₅O₄` fragment (unit 2) labelled in the degradation scheme. -/
private def unitTwo : MolecularFormula := ⟨22, 25, 4, 0⟩

/-- The `C₂H₃O₂` acetate contribution indicated by `OAc` in the scheme. -/
private def acetateContribution : MolecularFormula := ⟨2, 3, 2, 0⟩

/-- The formula contribution of the singly charged sodium cation in a
`[M + Na]⁺` adduct. -/
private def sodiumCation : MolecularFormula := ⟨0, 0, 0, 1⟩

end MolecularFormula

/-- The two degradation-product compositions from `L` that give the observed
sodium-adduct peaks.  They differ only by one additional unit-1 fragment. -/
private inductive LDegradationProduct where
  | withTwoUnitOne
  | withThreeUnitOne
  deriving DecidableEq, Repr

/-- Neutral formulae of the two products from the hexo-5-enose degradation.
Both contain one unit-2 fragment and one acetate contribution. -/
private def LDegradationProduct.neutralFormula : LDegradationProduct → MolecularFormula
  | .withTwoUnitOne =>
      MolecularFormula.add
        (MolecularFormula.scale 2 MolecularFormula.unitOne)
        (MolecularFormula.add MolecularFormula.unitTwo
          MolecularFormula.acetateContribution)
  | .withThreeUnitOne =>
      MolecularFormula.add
        (MolecularFormula.scale 3 MolecularFormula.unitOne)
        (MolecularFormula.add MolecularFormula.unitTwo
          MolecularFormula.acetateContribution)

/-- Integer nominal atomic masses required for the calculation. -/
private structure IntegerAtomicMasses where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  sodium : ℕ

/-- The conventional integer atomic-mass data used for this source
calculation.  These are explicit supplied empirical inputs, rather than a
fact inferred from the requested peak positions. -/
private def IntegerAtomicMasses.matchesRequiredIntegerValues
    (masses : IntegerAtomicMasses) : Prop :=
  masses.carbon = 12 ∧
    masses.hydrogen = 1 ∧
      masses.oxygen = 16 ∧
        masses.sodium = 23

/-- Nominal mass of a formula under the supplied integer atomic-mass
convention. -/
private def MolecularFormula.nominalMass
    (masses : IntegerAtomicMasses) (formula : MolecularFormula) : ℕ :=
  formula.carbon * masses.carbon +
    formula.hydrogen * masses.hydrogen +
      formula.oxygen * masses.oxygen +
        formula.sodium * masses.sodium

/-- A singly charged sodium adduct of one of the two degradation products.
The charge condition represents the superscript `+` in `[M + Na]⁺`. -/
private structure SodiumAdductIon where
  neutralProduct : LDegradationProduct
  charge : ℕ
  charge_is_one : charge = 1

/-- The displayed ion formula `[M + Na]⁺`. -/
private def SodiumAdductIon.formula (ion : SodiumAdductIon) : MolecularFormula :=
  MolecularFormula.add ion.neutralProduct.neutralFormula
    MolecularFormula.sodiumCation

/-- The nominal mass-to-charge ratio.  Rationals retain the division by the
ion charge even though the present sodium adducts are singly charged. -/
private abbrev MassToCharge := ℚ

private def SodiumAdductIon.massToCharge
    (masses : IntegerAtomicMasses) (ion : SodiumAdductIon) : MassToCharge :=
  (ion.formula.nominalMass masses : MassToCharge) / (ion.charge : MassToCharge)

/-- The `[M + Na]⁺` ion of a specified degradation product. -/
private def sodiumAdduct (product : LDegradationProduct) : SodiumAdductIon where
  neutralProduct := product
  charge := 1
  charge_is_one := rfl

/-- The two positive-mode readouts observed for the degradation products of
`L`, with their assignment to the corresponding sodium adducts kept explicit.
-/
private structure DegradationProductMassSpectrum where
  twoUnitOneSodiumAdductPeak : MassToCharge
  threeUnitOneSodiumAdductPeak : MassToCharge

/-- A spectrum is chemically assigned exactly when each of its two reported
readouts is the nominal `m/z` of the appropriate `[M + Na]⁺` ion. -/
private def DegradationProductMassSpectrum.assignedToSodiumAdducts
    (masses : IntegerAtomicMasses) (spectrum : DegradationProductMassSpectrum) : Prop :=
  spectrum.twoUnitOneSodiumAdductPeak =
      (sodiumAdduct .withTwoUnitOne).massToCharge masses ∧
    spectrum.threeUnitOneSodiumAdductPeak =
      (sodiumAdduct .withThreeUnitOne).massToCharge masses

/-- The neutral nominal masses that precede sodium-adduct formation. -/
private theorem degradation_product_nominal_masses
    (masses : IntegerAtomicMasses)
    (hmasses : masses.matchesRequiredIntegerValues) :
    (LDegradationProduct.withTwoUnitOne.neutralFormula).nominalMass masses = 1276 ∧
      (LDegradationProduct.withThreeUnitOne.neutralFormula).nominalMass masses = 1708 := by
  rcases hmasses with ⟨hcarbon, hhydrogen, hoxygen, hsodium⟩
  constructor <;>
    norm_num [LDegradationProduct.neutralFormula, MolecularFormula.nominalMass,
      MolecularFormula.add, MolecularFormula.scale, MolecularFormula.unitOne,
      MolecularFormula.unitTwo, MolecularFormula.acetateContribution, hcarbon,
      hhydrogen, hoxygen, hsodium]

/--
T9-A7.  With integer atomic masses, the two observed singly charged sodium
adducts of the degradation products from `L` have `m/z` values 1299 and 1731.
The spectrum-assignment hypothesis bridges the empirical peak readouts to the
chemical formulas without placing either requested numerical answer in a
premise.
-/
theorem sodium_adduct_peaks_of_L_degradation_products
    (masses : IntegerAtomicMasses)
    (spectrum : DegradationProductMassSpectrum)
    (hmasses : masses.matchesRequiredIntegerValues)
    (hassignment : spectrum.assignedToSodiumAdducts masses) :
    spectrum.twoUnitOneSodiumAdductPeak = 1299 ∧
      spectrum.threeUnitOneSodiumAdductPeak = 1731 := by
  rcases hmasses with ⟨hcarbon, hhydrogen, hoxygen, hsodium⟩
  rcases hassignment with ⟨htwo, hthree⟩
  constructor
  · rw [htwo]
    norm_num [SodiumAdductIon.massToCharge, SodiumAdductIon.formula,
      sodiumAdduct, LDegradationProduct.neutralFormula,
      MolecularFormula.nominalMass, MolecularFormula.add, MolecularFormula.scale,
      MolecularFormula.unitOne, MolecularFormula.unitTwo,
      MolecularFormula.acetateContribution, MolecularFormula.sodiumCation,
      hcarbon, hhydrogen, hoxygen, hsodium]
  · rw [hthree]
    norm_num [SodiumAdductIon.massToCharge, SodiumAdductIon.formula,
      sodiumAdduct, LDegradationProduct.neutralFormula,
      MolecularFormula.nominalMass, MolecularFormula.add, MolecularFormula.scale,
      MolecularFormula.unitOne, MolecularFormula.unitTwo,
      MolecularFormula.acetateContribution, MolecularFormula.sodiumCation,
      hcarbon, hhydrogen, hoxygen, hsodium]

end IChO2026Problems.T9A7
