import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T3-A7: equilibrium adsorption of uranyl ions by COF-9

Scalar fields in this file are numerical values in the units printed in the
question: concentrations are in `mg dm⁻³`, volume in `dm³`, sample mass in
`g`, molar masses in `g mol⁻¹`, and temperature in `K`.  Chemical identity,
phase, the COF-9 repeat-unit formula, and the one-pore-per-repeat-unit
structural fact are retained separately from these readouts.
-/

namespace IChO2026Problems.T3A7

/-- The two material identities relevant to the adsorption experiment. -/
private inductive ChemicalEntity where
  | cof9RepeatUnit
  | uranylDication
  deriving DecidableEq, Repr

/-- The phases distinguished by the experiment. -/
private inductive Phase where
  | solid
  | aqueous
  deriving DecidableEq, Repr

/-- Element counts needed to record the COF-9 repeat unit and `UO₂²⁺`. -/
private structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  uranium : ℕ
  deriving DecidableEq, Repr

/-- The repeat-unit formula `C₃₆H₂₇N₉O₃` used for one COF-9 pore. -/
private def cof9RepeatUnitFormula : MolecularFormula where
  carbon := 36
  hydrogen := 27
  nitrogen := 9
  oxygen := 3
  uranium := 0

/-- Formula of the dissolved uranyl dication, `UO₂²⁺`. -/
private def uranylDicationFormula : MolecularFormula where
  carbon := 0
  hydrogen := 0
  nitrogen := 0
  oxygen := 2
  uranium := 1

/--
The equilibrium experiment at one fixed temperature.  `poresPerRepeatUnit`
is a structural multiplicity, whereas all concentration and mass fields are
numerical measurements in the units documented above.
-/
private structure AdsorptionExperiment where
  temperature_K : ℝ
  adsorbent : ChemicalEntity
  adsorbentPhase : Phase
  dissolvedUraniumSpecies : ChemicalEntity
  dissolvedUraniumPhase : Phase
  formula : ChemicalEntity → MolecularFormula
  molarMass_g_per_mol : ChemicalEntity → ℝ
  initialConcentration_mg_per_dm3 : ℝ
  equilibriumConcentration_mg_per_dm3 : ℝ
  solutionVolume_dm3 : ℝ
  cof9Mass_g : ℝ
  poresPerRepeatUnit : ℝ
  temperature_positive : 0 < temperature_K
  initialConcentration_nonnegative : 0 ≤ initialConcentration_mg_per_dm3
  equilibriumConcentration_nonnegative : 0 ≤ equilibriumConcentration_mg_per_dm3
  equilibriumConcentration_le_initial :
    equilibriumConcentration_mg_per_dm3 ≤ initialConcentration_mg_per_dm3
  solutionVolume_positive : 0 < solutionVolume_dm3
  cof9Mass_positive : 0 < cof9Mass_g
  molarMass_positive : ∀ entity, 0 < molarMass_g_per_mol entity
  poresPerRepeatUnit_positive : 0 < poresPerRepeatUnit

/-- The supplied assumption that no uranium species other than `UO₂²⁺` occurs. -/
private def AllUraniumExistsAsUranyl (experiment : AdsorptionExperiment) : Prop :=
  experiment.dissolvedUraniumSpecies = .uranylDication

/-- The mass of dissolved uranyl removed from solution at equilibrium, in mg. -/
private def adsorbedUranylMass_mg (experiment : AdsorptionExperiment) : ℝ :=
  (experiment.initialConcentration_mg_per_dm3 -
      experiment.equilibriumConcentration_mg_per_dm3) *
    experiment.solutionVolume_dm3

/-- The equilibrium absorption capacity `qₑ`, numerically in `mg g⁻¹`. -/
noncomputable def equilibriumAbsorptionCapacity_mg_per_g
    (experiment : AdsorptionExperiment) : ℝ :=
  adsorbedUranylMass_mg experiment / experiment.cof9Mass_g

/-- Amount of adsorbed dissolved uranium species, in mol. -/
noncomputable def adsorbedDissolvedUraniumAmount_mol
    (experiment : AdsorptionExperiment) : ℝ :=
  (adsorbedUranylMass_mg experiment / 1000) /
    experiment.molarMass_g_per_mol experiment.dissolvedUraniumSpecies

/-- Amount of COF-9 repeat units in the adsorbent sample, in mol. -/
noncomputable def cof9RepeatUnitAmount_mol (experiment : AdsorptionExperiment) : ℝ :=
  experiment.cof9Mass_g /
    experiment.molarMass_g_per_mol experiment.adsorbent

/-- Amount of pores represented by the adsorbent sample, in mol. -/
noncomputable def poreAmount_mol (experiment : AdsorptionExperiment) : ℝ :=
  experiment.poresPerRepeatUnit * cof9RepeatUnitAmount_mol experiment

/-- The mean number of dissolved uranium ions per COF-9 pore. -/
noncomputable def averageUranylIonsPerPore (experiment : AdsorptionExperiment) : ℝ :=
  adsorbedDissolvedUraniumAmount_mol experiment / poreAmount_mol experiment

/-- A dimensionless value is reported as a whole-number count by nearest-integer
rounding.  This is needed because the displayed molar masses are rounded. -/
private def ReportsAsWholeNumber (value : ℝ) (reported : ℕ) : Prop :=
  |value - reported| < (1 : ℝ) / 2

/--
The numerical source data and the structural/molar-mass facts used in the
official calculation.  These are inputs; neither requested output (`qₑ` nor
the ions-per-pore count) is stored here.
-/
private def AdsorptionExperiment.matchesPrintedExperiment
    (experiment : AdsorptionExperiment) : Prop :=
  experiment.adsorbent = .cof9RepeatUnit ∧
    experiment.adsorbentPhase = .solid ∧
      AllUraniumExistsAsUranyl experiment ∧
        experiment.dissolvedUraniumPhase = .aqueous ∧
          experiment.formula .cof9RepeatUnit = cof9RepeatUnitFormula ∧
            experiment.formula .uranylDication = uranylDicationFormula ∧
              experiment.molarMass_g_per_mol .cof9RepeatUnit = 633.67 ∧
                experiment.molarMass_g_per_mol .uranylDication = 270.03 ∧
                  experiment.poresPerRepeatUnit = 1 ∧
                    experiment.initialConcentration_mg_per_dm3 = 19.90 ∧
                      experiment.equilibriumConcentration_mg_per_dm3 = 9.225 ∧
                        experiment.solutionVolume_dm3 = 200.0 / 1000 ∧
                          experiment.cof9Mass_g = 5.000 / 1000

/--
For the printed equilibrium experiment, the concentration drop gives
`qₑ = 427.0 mg g⁻¹`.  Converting the removed uranyl mass and the COF-9
repeat-unit mass to amounts gives a ratio that reports as one `UO₂²⁺` ion per
pore.  The rounding carrier is explicit because the reported molar masses
are themselves decimal approximations.
-/
theorem cof9_equilibrium_absorption_capacity_and_ions_per_pore
    (experiment : AdsorptionExperiment)
    (hsource : experiment.matchesPrintedExperiment) :
    equilibriumAbsorptionCapacity_mg_per_g experiment = 427 ∧
      ReportsAsWholeNumber (averageUranylIonsPerPore experiment) 1 := by
  rcases hsource with
    ⟨hadsorbent, hAdsorbentPhase, huranyl, hUraniumPhase, hCof9Formula,
      hUranylFormula, hCof9Mass, hUranylMass, hPores, hInitial, hEquilibrium,
      hVolume, hMass⟩
  unfold AllUraniumExistsAsUranyl at huranyl
  constructor
  · rw [equilibriumAbsorptionCapacity_mg_per_g, adsorbedUranylMass_mg,
      hInitial, hEquilibrium, hVolume, hMass]
    norm_num
  · rw [ReportsAsWholeNumber, averageUranylIonsPerPore,
      adsorbedDissolvedUraniumAmount_mol, poreAmount_mol,
      cof9RepeatUnitAmount_mol, adsorbedUranylMass_mg, hInitial, hEquilibrium,
      hVolume, hMass, huranyl, hUranylMass, hPores, hadsorbent, hCof9Mass]
    norm_num

end IChO2026Problems.T3A7
