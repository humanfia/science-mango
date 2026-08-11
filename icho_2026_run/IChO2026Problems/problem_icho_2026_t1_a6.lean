import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T1-A6: thermogravimetry of the mysterious stone

Masses in this file are measured in grams, temperatures in degrees Celsius,
and molar masses in grams per mole.  A displayed two-decimal mass is modeled
as an actual mass in its half-hundredth calibration interval.  `Formula`
keeps chemical identity separate from those scalar readouts.

The identifications of aluminium and of the mellitate anion from T1-A4 and
T1-A5 are hypotheses below, rather than imports from those generated files:
their dependency policy is `natural_language_prerequisite_only`.
-/

namespace IChO2026Problems.T1A6

/-- The elements occurring in the formulae relevant to this subquestion. -/
private inductive Element where
  | aluminium
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Fintype

/-- A stoichiometric formula records the number of atoms of each element. -/
private structure Formula where
  atoms : Element → ℕ

namespace Formula

/-- Addition of formulae, used to adjoin waters of crystallisation. -/
protected def add (left right : Formula) : Formula :=
  ⟨fun element => left.atoms element + right.atoms element⟩

/-- Repeated addition of a formula. -/
protected def nsmul (n : ℕ) (formula : Formula) : Formula :=
  ⟨fun element => n * formula.atoms element⟩

/-- The formula for water, `H₂O`. -/
private def water : Formula :=
  ⟨fun element =>
    match element with
    | .aluminium => 0
    | .carbon => 0
    | .hydrogen => 2
    | .oxygen => 1⟩

/-- The anhydrous aluminium salt `Al₂(C₆(COO)₆) = Al₂C₁₂O₁₂`. -/
private def aluminiumMellitate : Formula :=
  ⟨fun element =>
    match element with
    | .aluminium => 2
    | .carbon => 12
    | .hydrogen => 0
    | .oxygen => 12⟩

/-- The oxide formula `Al₂O₃`. -/
private def aluminiumOxide : Formula :=
  ⟨fun element =>
    match element with
    | .aluminium => 2
    | .carbon => 0
    | .hydrogen => 0
    | .oxygen => 3⟩

/-- The hydrate obtained by adjoining `n` waters of crystallisation. -/
private def hydrate (anhydrous : Formula) (n : ℕ) : Formula :=
  Formula.add anhydrous (Formula.nsmul n water)

/-- Atomic masses used in the official calculation, in grams per mole. -/
private def atomicMass : Element → ℝ
  | .aluminium => 26.98
  | .carbon => 12.01
  | .hydrogen => 1.008
  | .oxygen => 16

/-- Molar mass computed from the formula and the supplied atomic-mass data. -/
private def molarMass (formula : Formula) : ℝ :=
  (formula.atoms .aluminium : ℝ) * atomicMass .aluminium +
    (formula.atoms .carbon : ℝ) * atomicMass .carbon +
    (formula.atoms .hydrogen : ℝ) * atomicMass .hydrogen +
    (formula.atoms .oxygen : ℝ) * atomicMass .oxygen

end Formula

/-- Furnace atmosphere for the thermogravimetric experiment. -/
private inductive Atmosphere where
  | openAir
  deriving DecidableEq

/-- A labelled sample keeps its chemical formula distinct from scalar readouts. -/
private structure Sample where
  formula : Formula

/-- The usual maximum rounding error for a mass printed to two decimal places. -/
private def halfHundredth : ℝ := 0.005

/-- `actual` is compatible with a two-decimal mass printed as `displayed`. -/
private def CalibratedMass (displayed actual : ℝ) : Prop :=
  |actual - displayed| ≤ halfHundredth

/-- Numerical observations from one thermogravimetric experiment in open air. -/
private structure ThermogravimetricData where
  atmosphere : Atmosphere
  atmosphere_is_open_air : atmosphere = .openAir
  /-- Mass as a function of the furnace temperature. -/
  massAt : ℝ → ℝ
  /-- The observed onset temperature; the source gives no numerical tolerance. -/
  dehydrationOnset : ℝ
  onsetUncertainty : ℝ
  onsetUncertainty_nonnegative : 0 ≤ onsetUncertainty
  onset_is_approximately_100 : |dehydrationOnset - 100| ≤ onsetUncertainty
  /-- Actual masses whose displayed values were 10.00 g, 5.75 g, and 1.50 g. -/
  initialMass : ℝ
  dehydratedMass : ℝ
  finalMass : ℝ
  initialMass_calibrated : CalibratedMass 10.00 initialMass
  dehydratedMass_calibrated : CalibratedMass 5.75 dehydratedMass
  finalMass_calibrated : CalibratedMass 1.50 finalMass
  dehydratedMass_at_200 : massAt 200 = dehydratedMass
  finalMass_at_400 : massAt 400 = finalMass
  final_mass_stable_above_400 : ∀ temperature, 400 < temperature → massAt temperature = finalMass
  mass_lost_in_first_step : dehydratedMass < initialMass
  mass_lost_in_second_step : finalMass < dehydratedMass

/--
The first mass loss is solely water of crystallisation.  The equation is the
formula-unit mass balance after eliminating the (unknown) amount of dry salt.
-/
private structure HydrationConservation (data : ThermogravimetricData)
    (anhydrous : Formula) (waters : ℕ) : Prop where
  dehydration_mass_balance :
    (data.initialMass - data.dehydratedMass) * Formula.molarMass anhydrous =
      data.dehydratedMass * (waters : ℝ) * Formula.molarMass Formula.water

/--
The open-air second-step bridge contains no oxidation-state or charge premise.
It retains the aluminium atoms of the dry formula, removes carbon and hydrogen
from the stable residue, and conserves the number of formula units between the
5.75 g and 1.50 g plateaux.
-/
private structure OpenAirCalcinationLaw (data : ThermogravimetricData)
    (dryResidue stableResidue : Formula) : Prop where
  aluminium_retained :
    stableResidue.atoms .aluminium = dryResidue.atoms .aluminium
  carbon_removed : stableResidue.atoms .carbon = 0
  hydrogen_removed : stableResidue.atoms .hydrogen = 0
  dry_to_stable_molar_mass_balance :
    data.finalMass * Formula.molarMass dryResidue =
      data.dehydratedMass * Formula.molarMass stableResidue

/-- The formula `Al₂(C₆(COO)₆)` has the molar mass used in the rubric. -/
private lemma aluminiumMellitate_molarMass :
    Formula.molarMass Formula.aluminiumMellitate = 390.08 := by
  norm_num [Formula.molarMass, Formula.aluminiumMellitate, Formula.atomicMass]

/-- Water has molar mass `18.016 g mol⁻¹` for the supplied atomic masses. -/
private lemma water_molarMass : Formula.molarMass Formula.water = 18.016 := by
  norm_num [Formula.molarMass, Formula.water, Formula.atomicMass]

/--
Calibration and the first-step conservation equation bound the natural hydrate
count before the displayed-mass residual is evaluated.
-/
private theorem hydration_count_le_sixteen_from_calibration
    (data : ThermogravimetricData)
    (dryStone : Formula)
    (waters : ℕ)
    (hdryStone : dryStone = Formula.aluminiumMellitate)
    (hconservation : HydrationConservation data dryStone waters) :
    waters ≤ 16 := by
  subst dryStone
  have hinitial := data.initialMass_calibrated
  have hdehydrated := data.dehydratedMass_calibrated
  unfold CalibratedMass halfHundredth at hinitial hdehydrated
  rcases abs_le.mp hinitial with ⟨hinitial_lower, hinitial_upper⟩
  rcases abs_le.mp hdehydrated with ⟨hdehydrated_lower, hdehydrated_upper⟩
  have hmass := hconservation.dehydration_mass_balance
  rw [aluminiumMellitate_molarMass, water_molarMass] at hmass
  by_contra hnot
  have hnat : 17 ≤ waters := by omega
  have hwaters : (17 : ℝ) ≤ (waters : ℝ) := by exact_mod_cast hnat
  have hproduct : 0 ≤
      (data.dehydratedMass - 5.745) * ((waters : ℝ) - 17) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/--
Replacing the actual calibrated masses by their displays changes the
dry-molar-mass-scaled hydration equation by at most six in the source units.
-/
private theorem hydration_display_residual_bound
    (data : ThermogravimetricData)
    (dryStone : Formula)
    (waters : ℕ)
    (hdryStone : dryStone = Formula.aluminiumMellitate)
    (hconservation : HydrationConservation data dryStone waters)
    (hwaters : waters ≤ 16) :
    |(10.00 - 5.75) * Formula.molarMass dryStone -
        5.75 * (waters : ℝ) * Formula.molarMass Formula.water| ≤ 6 := by
  subst dryStone
  have hinitial := data.initialMass_calibrated
  have hdehydrated := data.dehydratedMass_calibrated
  unfold CalibratedMass halfHundredth at hinitial hdehydrated
  rcases abs_le.mp hinitial with ⟨hinitial_lower, hinitial_upper⟩
  rcases abs_le.mp hdehydrated with ⟨hdehydrated_lower, hdehydrated_upper⟩
  have hmass := hconservation.dehydration_mass_balance
  rw [aluminiumMellitate_molarMass, water_molarMass] at hmass
  have hwaters_nonnegative : 0 ≤ (waters : ℝ) := Nat.cast_nonneg _
  have hwaters_bound : (waters : ℝ) ≤ 16 := by exact_mod_cast hwaters
  have hproduct_lower : 0 ≤
      (data.dehydratedMass - 5.745) * (waters : ℝ) :=
    mul_nonneg (by linarith) hwaters_nonnegative
  have hproduct_upper : 0 ≤
      (5.755 - data.dehydratedMass) * (waters : ℝ) :=
    mul_nonneg (by linarith) hwaters_nonnegative
  rw [aluminiumMellitate_molarMass, water_molarMass]
  apply abs_le.mpr
  constructor <;> nlinarith

/--
The first mass loss, together with the known anhydrous aluminium mellitate,
selects sixteen waters of crystallisation.  The calibrated data and
conservation equation, rather than an answer-equivalent residual premise,
supply the approximation bridge.
-/
private theorem hydration_number_from_thermogravimetry
    (data : ThermogravimetricData)
    (dryStone : Formula)
    (waters : ℕ)
    (hdryStone : dryStone = Formula.aluminiumMellitate)
    (hconservation : HydrationConservation data dryStone waters) :
    waters = 16 := by
  have hwaters := hydration_count_le_sixteen_from_calibration
    data dryStone waters hdryStone hconservation
  have hresidual := hydration_display_residual_bound
    data dryStone waters hdryStone hconservation hwaters
  by_contra hnot
  have hlt : waters < 16 := lt_of_le_of_ne hwaters hnot
  have hsmall : waters ≤ 15 := by omega
  have hsmall_real : (waters : ℝ) ≤ 15 := by exact_mod_cast hsmall
  rw [hdryStone, aluminiumMellitate_molarMass, water_molarMass] at hresidual
  rcases abs_le.mp hresidual with ⟨_, hresidual_upper⟩
  norm_num at hresidual_upper
  nlinarith

/--
The 5.75 g to 1.50 g conservation law puts the molar mass of the stable
residue in the `101--103 g mol⁻¹` interval, even after display calibration.
-/
private theorem stable_residue_molar_mass_interval
    (data : ThermogravimetricData)
    (dryStone stableResidue : Formula)
    (hdryStone : dryStone = Formula.aluminiumMellitate)
    (hcalcination : OpenAirCalcinationLaw data dryStone stableResidue) :
    101 < Formula.molarMass stableResidue ∧
      Formula.molarMass stableResidue < 103 := by
  subst dryStone
  have hfinal := data.finalMass_calibrated
  have hdehydrated := data.dehydratedMass_calibrated
  unfold CalibratedMass halfHundredth at hfinal hdehydrated
  rcases abs_le.mp hfinal with ⟨hfinal_lower, hfinal_upper⟩
  rcases abs_le.mp hdehydrated with ⟨hdehydrated_lower, hdehydrated_upper⟩
  have hmass := hcalcination.dry_to_stable_molar_mass_balance
  rw [aluminiumMellitate_molarMass] at hmass
  have hmolar_nonnegative : 0 ≤ Formula.molarMass stableResidue := by
    simp only [Formula.molarMass, Formula.atomicMass]
    positivity
  constructor
  · by_contra hnot
    have hmolar_upper : Formula.molarMass stableResidue ≤ 101 := le_of_not_gt hnot
    have hproduct : 0 ≤
        (5.755 - data.dehydratedMass) * Formula.molarMass stableResidue :=
      mul_nonneg (by linarith) hmolar_nonnegative
    nlinarith
  · by_contra hnot
    have hmolar_lower : 103 ≤ Formula.molarMass stableResidue := le_of_not_gt hnot
    have hproduct : 0 ≤
        (data.dehydratedMass - 5.745) * Formula.molarMass stableResidue :=
      mul_nonneg (by linarith) hmolar_nonnegative
    nlinarith

/--
An open-air residue with the conserved aluminium atoms and no carbon or
hydrogen has formula `Al₂O₃` when its molar mass is in the interval derived
from the final plateau.  The oxygen count is selected by this interval; no
oxide charge equation is assumed.
-/
private theorem formula_of_stable_residue
    (data : ThermogravimetricData)
    (dryStone stableResidue : Formula)
    (hdryStone : dryStone = Formula.aluminiumMellitate)
    (hcalcination : OpenAirCalcinationLaw data dryStone stableResidue) :
    stableResidue = Formula.aluminiumOxide := by
  subst dryStone
  have hinterval := stable_residue_molar_mass_interval
    data Formula.aluminiumMellitate stableResidue rfl hcalcination
  have haluminium := hcalcination.aluminium_retained
  have hcarbon := hcalcination.carbon_removed
  have hhydrogen := hcalcination.hydrogen_removed
  change stableResidue.atoms .aluminium = 2 at haluminium
  have hmolar : Formula.molarMass stableResidue =
      53.96 + (stableResidue.atoms .oxygen : ℝ) * 16 := by
    simp [Formula.molarMass, Formula.atomicMass, haluminium, hcarbon, hhydrogen]
    ring
  have hoxygen_lower : (2 : ℝ) < (stableResidue.atoms .oxygen : ℝ) := by
    nlinarith [hinterval.1, hmolar]
  have hoxygen_upper : (stableResidue.atoms .oxygen : ℝ) < 4 := by
    nlinarith [hinterval.2, hmolar]
  have hoxygen_lower_nat : 2 < stableResidue.atoms .oxygen := by
    exact_mod_cast hoxygen_lower
  have hoxygen_upper_nat : stableResidue.atoms .oxygen < 4 := by
    exact_mod_cast hoxygen_upper
  have hoxygen : stableResidue.atoms .oxygen = 3 := by omega
  have hatoms : stableResidue.atoms = Formula.aluminiumOxide.atoms := by
    funext element
    cases element <;>
      simp [Formula.aluminiumOxide, haluminium, hcarbon, hhydrogen, hoxygen]
  cases stableResidue
  cases hatoms
  rfl

/--
T1-A6 requested formulae.  The source's two previous-part identifications are
restated only as hypotheses, while the current outputs remain conclusions:
the stone is `Al₂(C₆(COO)₆)·16H₂O` and the stable compound `H` is `Al₂O₃`.
-/
theorem identify_stone_and_compound_H
    (data : ThermogravimetricData)
    (stone dryStone compoundH : Sample)
    (waters : ℕ)
    (hdryStone : dryStone.formula = Formula.aluminiumMellitate)
    (hstone_hydrate : stone.formula = Formula.hydrate dryStone.formula waters)
    (hmassBalance : HydrationConservation data dryStone.formula waters)
    (hcompoundH_open_air :
      OpenAirCalcinationLaw data dryStone.formula compoundH.formula) :
    stone.formula = Formula.hydrate Formula.aluminiumMellitate 16 ∧
      compoundH.formula = Formula.aluminiumOxide := by
  have hwaters := hydration_number_from_thermogravimetry
    data dryStone.formula waters hdryStone hmassBalance
  constructor
  · rw [hstone_hydrate, hdryStone, hwaters]
  · exact formula_of_stable_residue data dryStone.formula compoundH.formula
      hdryStone hcompoundH_open_air

end IChO2026Problems.T1A6
