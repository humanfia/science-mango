import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T4-A9: fission count and enriched-uranium mass

This file models the two requested outputs as numerical readouts derived from
two explicit physical balances.  The explosion's TNT equivalent fixes its
released energy; that energy is balanced by a number of uranium-235 fissions.
The number of fissions is then balanced against the fissioned fraction of the
uranium-235 present in the enriched-uranium fuel.  The T4-A4 value is passed
as an explicit hypothesis because its dependency policy is
`natural_language_prerequisite_only`.

All scalar quantities use the numerical units stated in the problem or needed
for the official calculation: energies in J or MeV, molar mass in g mol⁻¹,
fuel mass in kg, and the Avogadro constant in nuclei mol⁻¹.
-/

namespace IChO2026Problems.T4A9

/-- A released energy readout in MeV. -/
private abbrev EnergyMeV := ℝ

/-- A released energy readout in J. -/
private abbrev EnergyJoule := ℝ

/-- A TNT equivalent readout in kilotons of TNT. -/
private abbrev TNTEquivalentKilotons := ℝ

/-- Energy in J released by one ton of TNT equivalent. -/
private abbrev JoulesPerTNTTon := ℝ

/-- The conversion factor from MeV to J. -/
private abbrev JoulesPerMeV := ℝ

/-- The numerical count of nuclear fissions in the macroscopic calculation. -/
private abbrev FissionCount := ℝ

/-- A molar mass readout in g mol⁻¹. -/
private abbrev MolarMassGramPerMol := ℝ

/-- A macroscopic fuel mass in kg. -/
private abbrev MassKilogram := ℝ

/-- A dimensionless mass or participation fraction. -/
private abbrev Fraction := ℝ

/-- A numerical Avogadro constant in nuclei mol⁻¹. -/
private abbrev NucleiPerMol := ℝ

/-- The uranium isotopes relevant to the enriched-fuel composition. -/
private inductive UraniumIsotope where
  | uranium235
  | uranium238
  deriving DecidableEq, Repr

/--
The isotopic mass composition of the enriched uranium.  The current problem
uses only the uranium-235 entry, but retaining both isotopes prevents the
given 90% mass fraction from being treated as an unlabelled scalar.
-/
private structure EnrichedUraniumComposition where
  isotopeMassFraction : UraniumIsotope → Fraction
  massFraction_nonneg : ∀ isotope, 0 ≤ isotopeMassFraction isotope
  massFraction_sum :
    isotopeMassFraction .uranium235 + isotopeMassFraction .uranium238 = 1

/--
Numerical data and conversion conventions needed for the T4-A9 calculation.
Neither the requested fission count nor the requested fuel mass is a field of
this structure.
-/
private structure FissionExplosionData where
  tntEquivalent : TNTEquivalentKilotons
  tntEnergyPerTon : JoulesPerTNTTon
  joulesPerMeV : JoulesPerMeV
  avogadroConstant : NucleiPerMol
  uranium235MolarMass : MolarMassGramPerMol
  enrichedFuel : EnrichedUraniumComposition
  uranium235FissionedFraction : Fraction

/--
The two unknown output readouts for one nuclear explosion.  Their numerical
values are not supplied here: the energy and uranium-mass balances below are
the bridges that constrain them.
-/
private structure NuclearExplosion where
  data : FissionExplosionData
  totalFissions : FissionCount
  enrichedUraniumMassUsed : MassKilogram

/-- The energy corresponding to the stated TNT equivalent.  One kiloton is
`1000` tons, and the source's `4.184 GJ` per ton is represented in J. -/
private def NuclearExplosion.tntEquivalentEnergy
    (explosion : NuclearExplosion) : EnergyJoule :=
  explosion.data.tntEquivalent * 1000 * explosion.data.tntEnergyPerTon

/-- The energy in J released by one uranium-235 fission. -/
private def NuclearExplosion.energyPerFissionJoule
    (explosion : NuclearExplosion) (releasedFissionEnergy : EnergyMeV) :
    EnergyJoule :=
  releasedFissionEnergy * explosion.data.joulesPerMeV

/--
Energy conservation for the macroscopic explosion: its TNT-equivalent energy
is the number of uranium-235 fissions times the energy per fission.
-/
private def ObeysFissionEnergyBalance (explosion : NuclearExplosion)
    (releasedFissionEnergy : EnergyMeV) : Prop :=
  explosion.tntEquivalentEnergy =
    explosion.totalFissions * explosion.energyPerFissionJoule releasedFissionEnergy

/-- The number of moles of uranium-235 in the enriched fuel mass. -/
noncomputable def NuclearExplosion.uranium235Amount_mol
    (explosion : NuclearExplosion) : ℝ :=
  explosion.enrichedUraniumMassUsed * 1000 *
      explosion.data.enrichedFuel.isotopeMassFraction .uranium235 /
    explosion.data.uranium235MolarMass

/--
Material balance for the fissions.  The right-hand side is Avogadro's constant
times the moles of uranium-235 in the fuel which undergo fission.  Thus the
90% isotope mass fraction and the 33% fission fraction both affect the
requested total fuel mass.
-/
private def ObeysUranium235FissionMassBalance (explosion : NuclearExplosion) : Prop :=
  explosion.totalFissions = explosion.data.avogadroConstant *
    (explosion.data.uranium235FissionedFraction *
      explosion.uranium235Amount_mol)

/-- Positivity and fraction-domain conditions for the two balance equations. -/
private def HasPhysicalFissionExplosionConditions (explosion : NuclearExplosion) : Prop :=
  0 < explosion.data.tntEquivalent ∧
    0 < explosion.data.tntEnergyPerTon ∧
      0 < explosion.data.joulesPerMeV ∧
        0 < explosion.data.avogadroConstant ∧
          0 < explosion.data.uranium235MolarMass ∧
            0 < explosion.data.enrichedFuel.isotopeMassFraction .uranium235 ∧
              explosion.data.enrichedFuel.isotopeMassFraction .uranium235 ≤ 1 ∧
                0 < explosion.data.uranium235FissionedFraction ∧
                  explosion.data.uranium235FissionedFraction ≤ 1 ∧
                    0 ≤ explosion.enrichedUraniumMassUsed

/--
The empirical values printed in the T4 context: a 30-kiloton TNT-equivalent
explosion, 4.184 GJ per ton of TNT, a 90% mass fraction of uranium-235, a 33%
fissioned fraction, and the earlier T4 isotope mass `235.04 g mol⁻¹`.

`4.184 GJ` is written as `4.184 × 10⁹ J`; this is a unit conversion, not an
additional empirical input.
-/
private def MatchesT4A9SourceData (data : FissionExplosionData) : Prop :=
  data.tntEquivalent = 30 ∧
    data.tntEnergyPerTon = 4.184 * 10 ^ 9 ∧
      data.uranium235MolarMass = 235.04 ∧
        data.enrichedFuel.isotopeMassFraction .uranium235 = 0.90 ∧
          data.uranium235FissionedFraction = 0.33

/--
The standard numerical conversion readouts used in the official calculation.
They are explicit hypotheses because neither the current question nor T4-A4
prints these constants.
-/
private def UsesOfficialCalculationConversions (data : FissionExplosionData) : Prop :=
  data.joulesPerMeV = 1.602 * 10 ^ (-13 : ℤ) ∧
    data.avogadroConstant = 6.022 * 10 ^ 23

/--
T4-A9 using the previous T4-A4 result `ΔE = 185.2 MeV`.  The exact balance
formulae are stated before the numerical intervals.  The intervals retain the
three-significant-figure presentation of the official results
`4.23 × 10²⁴` fissions and `5.56 kg`, without putting either answer in a
premise or data field.
-/
theorem fissions_and_enriched_uranium_mass_from_t4_a4
    (explosion : NuclearExplosion) (releasedFissionEnergy : EnergyMeV)
    (hphysical : HasPhysicalFissionExplosionConditions explosion)
    (hsource : MatchesT4A9SourceData explosion.data)
    (hconversions : UsesOfficialCalculationConversions explosion.data)
    (hpreviousT4A4 : releasedFissionEnergy = 185.2 ∧ 0 < releasedFissionEnergy)
    (henergy : ObeysFissionEnergyBalance explosion releasedFissionEnergy)
    (hmass : ObeysUranium235FissionMassBalance explosion) :
    explosion.totalFissions =
        explosion.tntEquivalentEnergy /
          explosion.energyPerFissionJoule releasedFissionEnergy ∧
    explosion.enrichedUraniumMassUsed =
        explosion.totalFissions / explosion.data.avogadroConstant *
            explosion.data.uranium235MolarMass / 1000 /
          (explosion.data.enrichedFuel.isotopeMassFraction .uranium235 *
            explosion.data.uranium235FissionedFraction) ∧
        4.225 * 10 ^ 24 < explosion.totalFissions ∧
          explosion.totalFissions < 4.235 * 10 ^ 24 ∧
            5.555 < explosion.enrichedUraniumMassUsed ∧
              explosion.enrichedUraniumMassUsed < 5.565 := by
  rcases hphysical with ⟨_, _, hjoulesPerMeV_pos, _, _, _, _, _, _, _⟩
  rcases hsource with ⟨htnt, htntEnergy, hmolarMass, henrichment, hfissioned⟩
  rcases hconversions with ⟨hjoulePerMeV, havogadro⟩
  rcases hpreviousT4A4 with ⟨hreleasedEnergy, hreleasedEnergy_pos⟩
  simp only [ObeysFissionEnergyBalance, ObeysUranium235FissionMassBalance,
    NuclearExplosion.tntEquivalentEnergy,
    NuclearExplosion.energyPerFissionJoule,
    NuclearExplosion.uranium235Amount_mol] at henergy hmass ⊢
  have henergyPerFission_ne :
      releasedFissionEnergy * explosion.data.joulesPerMeV ≠ 0 :=
    ne_of_gt (mul_pos hreleasedEnergy_pos hjoulesPerMeV_pos)
  have hFissionFormula : explosion.totalFissions =
      (explosion.data.tntEquivalent * 1000 * explosion.data.tntEnergyPerTon) /
        (releasedFissionEnergy * explosion.data.joulesPerMeV) :=
    (eq_div_iff henergyPerFission_ne).2 henergy.symm
  norm_num [htnt, htntEnergy, hmolarMass, henrichment, hfissioned,
    hjoulePerMeV, havogadro, hreleasedEnergy] at henergy hmass hFissionFormula ⊢
  ring_nf at henergy hmass
  have hFissionProduct : explosion.totalFissions * 370863 =
      1569000000000000000000000000000 := by
    calc
      explosion.totalFissions * 370863 =
          (explosion.totalFissions * (370863 / 12500000000000000)) *
            12500000000000000 := by ring
      _ = 125520000000000 * 12500000000000000 := by rw [← henergy]
      _ = 1569000000000000000000000000000 := by norm_num
  have hFissionValue : explosion.totalFissions =
      1569000000000000000000000000000 / 370863 := by
    apply (eq_div_iff (by norm_num : (370863 : ℝ) ≠ 0)).2
    exact hFissionProduct
  have hFuelMass : explosion.enrichedUraniumMassUsed =
      (1569000000000000000000000000000 * 1469) /
        (1117833750000000000000000000 * 370863) := by
    apply (eq_div_iff (by norm_num :
      (1117833750000000000000000000 * 370863 : ℝ) ≠ 0)).2
    calc
      explosion.enrichedUraniumMassUsed *
          (1117833750000000000000000000 * 370863) =
          (explosion.enrichedUraniumMassUsed *
            (1117833750000000000000000000 / 1469) * 370863) * 1469 := by
            ring
      _ = (explosion.totalFissions * 370863) * 1469 := by rw [← hmass]
      _ = 1569000000000000000000000000000 * 1469 := by rw [hFissionProduct]
  constructor
  · exact hFissionFormula
  constructor
  · linarith
  constructor
  · rw [hFissionValue]
    norm_num
  constructor
  · rw [hFissionValue]
    norm_num
  constructor
  · rw [hFuelMass]
    norm_num
  · rw [hFuelMass]
    norm_num

/--
The alternate instruction in T4-A9 when the preceding T4-A4 calculation is
unavailable: substitute `ΔE = 200 MeV` in the same energy and mass balances.
This branch preserves the source's conditional alternative rather than
silently selecting the previous-part value.
-/
private theorem fissions_and_enriched_uranium_mass_from_supplied_fallback
    (explosion : NuclearExplosion) (fallbackFissionEnergy : EnergyMeV)
    (hphysical : HasPhysicalFissionExplosionConditions explosion)
    (hsource : MatchesT4A9SourceData explosion.data)
    (hconversions : UsesOfficialCalculationConversions explosion.data)
    (hsuppliedFallback : fallbackFissionEnergy = 200 ∧ 0 < fallbackFissionEnergy)
    (henergy : ObeysFissionEnergyBalance explosion fallbackFissionEnergy)
    (hmass : ObeysUranium235FissionMassBalance explosion) :
    explosion.totalFissions =
        explosion.tntEquivalentEnergy /
          explosion.energyPerFissionJoule fallbackFissionEnergy ∧
    explosion.enrichedUraniumMassUsed =
        explosion.totalFissions / explosion.data.avogadroConstant *
            explosion.data.uranium235MolarMass / 1000 /
          (explosion.data.enrichedFuel.isotopeMassFraction .uranium235 *
            explosion.data.uranium235FissionedFraction) ∧
        3.91 * 10 ^ 24 < explosion.totalFissions ∧
          explosion.totalFissions < 3.92 * 10 ^ 24 ∧
            5.14 < explosion.enrichedUraniumMassUsed ∧
              explosion.enrichedUraniumMassUsed < 5.15 := by
  rcases hphysical with ⟨_, _, hjoulesPerMeV_pos, _, _, _, _, _, _, _⟩
  rcases hsource with ⟨htnt, htntEnergy, hmolarMass, henrichment, hfissioned⟩
  rcases hconversions with ⟨hjoulePerMeV, havogadro⟩
  rcases hsuppliedFallback with ⟨hreleasedEnergy, hreleasedEnergy_pos⟩
  simp only [ObeysFissionEnergyBalance, ObeysUranium235FissionMassBalance,
    NuclearExplosion.tntEquivalentEnergy,
    NuclearExplosion.energyPerFissionJoule,
    NuclearExplosion.uranium235Amount_mol] at henergy hmass ⊢
  have henergyPerFission_ne :
      fallbackFissionEnergy * explosion.data.joulesPerMeV ≠ 0 :=
    ne_of_gt (mul_pos hreleasedEnergy_pos hjoulesPerMeV_pos)
  have hFissionFormula : explosion.totalFissions =
      (explosion.data.tntEquivalent * 1000 * explosion.data.tntEnergyPerTon) /
        (fallbackFissionEnergy * explosion.data.joulesPerMeV) :=
    (eq_div_iff henergyPerFission_ne).2 henergy.symm
  norm_num [htnt, htntEnergy, hmolarMass, henrichment, hfissioned,
    hjoulePerMeV, havogadro, hreleasedEnergy] at henergy hmass hFissionFormula ⊢
  ring_nf at henergy hmass
  have hFissionProduct : explosion.totalFissions * 801 =
      3138000000000000000000000000 := by
    calc
      explosion.totalFissions * 801 =
          (explosion.totalFissions * (801 / 25000000000000)) *
            25000000000000 := by ring
      _ = 125520000000000 * 25000000000000 := by rw [← henergy]
      _ = 3138000000000000000000000000 := by norm_num
  have hFissionValue : explosion.totalFissions =
      3138000000000000000000000000 / 801 := by
    apply (eq_div_iff (by norm_num : (801 : ℝ) ≠ 0)).2
    exact hFissionProduct
  have hFuelMass : explosion.enrichedUraniumMassUsed =
      (3138000000000000000000000000 * 1469) /
        (1117833750000000000000000000 * 801) := by
    apply (eq_div_iff (by norm_num :
      (1117833750000000000000000000 * 801 : ℝ) ≠ 0)).2
    calc
      explosion.enrichedUraniumMassUsed *
          (1117833750000000000000000000 * 801) =
          (explosion.enrichedUraniumMassUsed *
            (1117833750000000000000000000 / 1469) * 801) * 1469 := by
            ring
      _ = (explosion.totalFissions * 801) * 1469 := by rw [← hmass]
      _ = 3138000000000000000000000000 * 1469 := by rw [hFissionProduct]
  constructor
  · exact hFissionFormula
  constructor
  · linarith
  constructor
  · rw [hFissionValue]
    norm_num
  constructor
  · rw [hFissionValue]
    norm_num
  constructor
  · rw [hFuelMass]
    norm_num
  · rw [hFuelMass]
    norm_num

end IChO2026Problems.T4A9
