import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T7-A2: annual methane requirement for ammonia synthesis

The displayed Haber--Bosch plant first reforms methane with steam, partially
oxidizes the remaining methane with the oxygen in an air feed, and shifts all
carbon monoxide with steam before carbon-dioxide scrubbing.  The three
conversion reactions are quantitative; the ammonia formation step has the
stated 97.0% overall yield.

The problem asks for an annual mass of methane.  Amounts of named gaseous
species are consequently recorded in mol, molar masses in g mol⁻¹, and the
reported annual masses in metric tonnes.  No units are silently cancelled in
the mass/amount conversion definitions below.
-/

namespace IChO2026Problems.T7A2

/-- The chemical species shown in the T7 ammonia-synthesis flow diagram. -/
private inductive GasSpecies where
  | methane
  | water
  | carbonMonoxide
  | oxygen
  | hydrogen
  | nitrogen
  | ammonia
  | carbonDioxide
  deriving DecidableEq, Repr

/-- The four reactions printed in the process diagram. -/
private inductive PlantReaction where
  | steamReforming
  | partialOxidation
  | waterGasShift
  | ammoniaFormation
  deriving DecidableEq, Repr

/--
Reactant-side complexes in the displayed reactions.  A `CRNT.Complex` is a
species-indexed natural-number coefficient vector, so this records the source
stoichiometry without identifying a chemical species with a scalar readout.
-/
private def reactantCoefficient : PlantReaction → CRNT.Complex GasSpecies
  | .steamReforming, .methane => 1
  | .steamReforming, .water => 1
  | .partialOxidation, .methane => 2
  | .partialOxidation, .oxygen => 1
  | .waterGasShift, .carbonMonoxide => 1
  | .waterGasShift, .water => 1
  | .ammoniaFormation, .nitrogen => 1
  | .ammoniaFormation, .hydrogen => 3
  | _, _ => 0

/-- Product-side complexes in the displayed reactions. -/
private def productCoefficient : PlantReaction → CRNT.Complex GasSpecies
  | .steamReforming, .carbonMonoxide => 1
  | .steamReforming, .hydrogen => 3
  | .partialOxidation, .carbonMonoxide => 2
  | .partialOxidation, .hydrogen => 4
  | .waterGasShift, .carbonDioxide => 1
  | .waterGasShift, .hydrogen => 1
  | .ammoniaFormation, .ammonia => 2
  | _, _ => 0

/-- The four process reactions as source and target stoichiometric complexes. -/
private def displayedReaction (reaction : PlantReaction) : CRNT.Reaction GasSpecies where
  source := reactantCoefficient reaction
  target := productCoefficient reaction

/-- The `4 N₂ : 1 O₂` air-feed relation printed above the oxidation stage. -/
private def nitrogenPerOxygenInAir : ℕ := 4

/-- Numerical amount of substance in mol. -/
private abbrev AmountMol := ℝ

/-- A molar mass in g mol⁻¹. -/
private abbrev MolarMassGramPerMol := ℝ

/-- A macroscopic mass in metric tonnes. -/
private abbrev MassTonne := ℝ

/-- A dimensionless yield fraction. -/
private abbrev YieldFraction := ℝ

/-- The source data required to turn the material balances into annual masses. -/
private structure NitrogenFixationData where
  annualAmmoniaMass : MassTonne
  overallYield : YieldFraction
  ammoniaMolarMass : MolarMassGramPerMol
  methaneMolarMass : MolarMassGramPerMol

/--
The independent amount readouts and reaction extents for one annual operation
of the named Navoiazot plant.  `methaneFeed` is an unknown input readout, not
the reported answer; its mass is derived below from its amount and molar mass.
-/
private structure NitrogenFixationRun where
  data : NitrogenFixationData
  methaneFeed : AmountMol
  waterFeed : AmountMol
  nitrogenFeed : AmountMol
  oxygenFeed : AmountMol
  ammoniaProduct : AmountMol
  steamReformingExtent : AmountMol
  partialOxidationExtent : AmountMol
  waterGasShiftExtent : AmountMol

/-- Conversion of a mass in tonnes to an amount in mol, using `10^6 g/t`. -/
private noncomputable def amountFromMassTonnes (mass : MassTonne)
    (molarMass : MolarMassGramPerMol) : AmountMol :=
  mass * 1_000_000 / molarMass

/-- Conversion of an amount in mol to a mass in tonnes, using `10^6 g/t`. -/
private noncomputable def massTonnesFromAmount (amount : AmountMol)
    (molarMass : MolarMassGramPerMol) : MassTonne :=
  amount * molarMass / 1_000_000

/-- The annual ammonia amount corresponding to the stated annual product mass. -/
private noncomputable def NitrogenFixationRun.annualAmmoniaAmount (run : NitrogenFixationRun) :
    AmountMol :=
  amountFromMassTonnes run.data.annualAmmoniaMass run.data.ammoniaMolarMass

/-- The annual methane mass requested in the current subquestion. -/
private noncomputable def NitrogenFixationRun.annualMethaneMass (run : NitrogenFixationRun) :
    MassTonne :=
  massTonnesFromAmount run.methaneFeed run.data.methaneMolarMass

/--
The hydrogen amount made by the three quantitative carbon-conversion stages:
three per steam-reforming event, four per partial-oxidation event, and one per
water-gas-shift event.
-/
private def NitrogenFixationRun.hydrogenProduced (run : NitrogenFixationRun) :
    AmountMol :=
  (productCoefficient .steamReforming .hydrogen : ℝ) *
      run.steamReformingExtent +
    (productCoefficient .partialOxidation .hydrogen : ℝ) *
      run.partialOxidationExtent +
    (productCoefficient .waterGasShift .hydrogen : ℝ) *
      run.waterGasShiftExtent

/-- The carbon monoxide entering the water-gas-shift stage. -/
private def NitrogenFixationRun.carbonMonoxideProduced (run : NitrogenFixationRun) :
    AmountMol :=
  (productCoefficient .steamReforming .carbonMonoxide : ℝ) *
      run.steamReformingExtent +
    (productCoefficient .partialOxidation .carbonMonoxide : ℝ) *
      run.partialOxidationExtent

/-- Positivity and fraction-domain conditions for the annual plant operation. -/
private def HasPhysicalPlantConditions (run : NitrogenFixationRun) : Prop :=
  0 < run.data.annualAmmoniaMass ∧
    0 < run.data.overallYield ∧ run.data.overallYield ≤ 1 ∧
      0 < run.data.ammoniaMolarMass ∧ 0 < run.data.methaneMolarMass ∧
        0 ≤ run.methaneFeed ∧ 0 ≤ run.waterFeed ∧ 0 ≤ run.nitrogenFeed ∧
          0 ≤ run.oxygenFeed ∧ 0 ≤ run.ammoniaProduct ∧
            0 ≤ run.steamReformingExtent ∧
              0 ≤ run.partialOxidationExtent ∧ 0 ≤ run.waterGasShiftExtent

/--
The quantitative process balances read from Fig. 1.  In particular, the air
feed supplies four moles of nitrogen per mole of oxygen; all CO formed by the
first two reactions enters the shift reaction; and the hydrogen delivered to
the Haber--Bosch loop is in the `3 H₂ : 1 N₂` ratio.  Only ammonia formation
is reduced by the stated overall yield.
-/
private def ObeysT7PlantBalances (run : NitrogenFixationRun) : Prop :=
  run.ammoniaProduct = run.annualAmmoniaAmount ∧
    run.ammoniaProduct =
      (productCoefficient .ammoniaFormation .ammonia : ℝ) *
        run.data.overallYield * run.nitrogenFeed ∧
      run.nitrogenFeed = (nitrogenPerOxygenInAir : ℝ) * run.oxygenFeed ∧
        run.oxygenFeed =
          (reactantCoefficient .partialOxidation .oxygen : ℝ) *
            run.partialOxidationExtent ∧
          run.methaneFeed =
            (reactantCoefficient .steamReforming .methane : ℝ) *
              run.steamReformingExtent +
              (reactantCoefficient .partialOxidation .methane : ℝ) *
                run.partialOxidationExtent ∧
            run.waterFeed =
              (reactantCoefficient .steamReforming .water : ℝ) *
                run.steamReformingExtent +
                (reactantCoefficient .waterGasShift .water : ℝ) *
                  run.waterGasShiftExtent ∧
              run.waterGasShiftExtent = run.carbonMonoxideProduced ∧
                run.hydrogenProduced =
                  (reactantCoefficient .ammoniaFormation .hydrogen : ℝ) *
                    run.nitrogenFeed

/--
The numerical facts supplied in T7-A2 and used by its official calculation.
The 17 and 16 g mol⁻¹ values are the molar masses of the named `NH₃` and
`CH₄` species, respectively.  The methane amount or mass sought by the
question is deliberately absent.
-/
private def MatchesT7A2SourceData (data : NitrogenFixationData) : Prop :=
  data.annualAmmoniaMass = 660_000 ∧
    data.overallYield = 0.970 ∧
      data.ammoniaMolarMass = 17 ∧ data.methaneMolarMass = 16

/--
`reported` is the result of rounding `mass` to the nearest thousand tonnes.
The source prints `280,000 tons`; this predicate retains the necessary
rounding tolerance rather than treating that displayed rounded value as an
exact premise.
-/
private def RoundsToNearestThousandTonnes (mass reported : MassTonne) : Prop :=
  reported - 500 ≤ mass ∧ mass < reported + 500

/--
T7-A2.  The quantitative reaction balances and the 97.0% overall yield first
fix the methane amount as seven eighths of the nitrogen input needed for the
annual ammonia output.  After the labelled CH₄ molar-mass conversion, its
annual mass rounds to the requested `280,000` tonnes.

The exact formula is included because the problem's displayed intermediate
mole amounts are rounded; the final source answer must therefore be an
appropriately rounded mass conclusion, not a false exact equality obtained by
copying a rounded intermediate into a hypothesis.
-/
theorem annual_methane_requirement_for_660000_tonnes_ammonia
    (run : NitrogenFixationRun)
    (hphysical : HasPhysicalPlantConditions run)
    (hsource : MatchesT7A2SourceData run.data)
    (hbalances : ObeysT7PlantBalances run) :
    run.methaneFeed =
      (7 / 8 : ℝ) *
        (run.annualAmmoniaAmount /
          (2 * run.data.overallYield)) ∧
      RoundsToNearestThousandTonnes run.annualMethaneMass 280_000 := by
  rcases hphysical with ⟨_, hyield_pos, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases hsource with ⟨hmass, hyield, hammonia_molar_mass, hmethane_molar_mass⟩
  rcases hbalances with ⟨hammonia_amount, hammonia_yield, hnitrogen_air,
    hoxygen_extent, hmethane_balance, _, hshift, hhydrogen⟩
  norm_num [nitrogenPerOxygenInAir, reactantCoefficient, productCoefficient,
    NitrogenFixationRun.hydrogenProduced,
    NitrogenFixationRun.carbonMonoxideProduced] at hnitrogen_air hoxygen_extent hmethane_balance hshift hhydrogen hammonia_yield
  have hmethane_nitrogen :
      run.methaneFeed = (7 / 8 : ℝ) * run.nitrogenFeed := by
    linarith [hnitrogen_air, hoxygen_extent, hmethane_balance, hshift, hhydrogen]
  have htwo_yield_ne : 2 * run.data.overallYield ≠ 0 := by
    exact mul_ne_zero (by norm_num) (ne_of_gt hyield_pos)
  have hnitrogen_amount :
      run.nitrogenFeed =
        run.annualAmmoniaAmount / (2 * run.data.overallYield) := by
    apply (eq_div_iff htwo_yield_ne).2
    nlinarith [hammonia_amount, hammonia_yield]
  constructor
  · rw [hmethane_nitrogen, hnitrogen_amount]
  · rw [NitrogenFixationRun.annualMethaneMass, massTonnesFromAmount,
      hmethane_nitrogen, hnitrogen_amount,
      NitrogenFixationRun.annualAmmoniaAmount, amountFromMassTonnes,
      hmass, hyield, hammonia_molar_mass, hmethane_molar_mass]
    norm_num [RoundsToNearestThousandTonnes]

end IChO2026Problems.T7A2
