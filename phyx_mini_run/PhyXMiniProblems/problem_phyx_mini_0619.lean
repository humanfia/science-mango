import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy

namespace PhyXMini0619

open Dimension
open UnitChoices

/-!
The local types below retain physical dimensions through Physlib's
`Dimensionful (WithDim ...)` interface.  Scalar-valued functions are explicitly
SI readouts, rather than definitions of the underlying physical quantities.
-/

/-- A physical length, used for the source-to-worker distance in the figure. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical duration. -/
abbrev DimTime : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical mass. -/
abbrev DimMass : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A radioactive activity, with dimension inverse time. -/
abbrev DimActivity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Energy per unit mass, the common dimension of gray and sievert. -/
abbrev DimSpecificEnergy : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- SI readout of a length, in meters. -/
noncomputable def lengthInMeters (x : DimLength) : ℝ :=
  (x.1 SI).1

/-- SI readout of a duration, in seconds. -/
noncomputable def timeInSeconds (x : DimTime) : ℝ :=
  (x.1 SI).1

/-- Readout of a duration in hours. -/
noncomputable def timeInHours (x : DimTime) : ℝ :=
  timeInSeconds x / 3600

/-- SI readout of a mass, in kilograms. -/
noncomputable def massInKilograms (x : DimMass) : ℝ :=
  (x.1 SI).1

/-- SI readout of an activity, in becquerels (decays per second). -/
noncomputable def activityInBecquerels (x : DimActivity) : ℝ :=
  (x.1 SI).1

/-- Activity readout in millicuries, using `1 mCi = 3.7 * 10^7 Bq`. -/
noncomputable def activityInMilliCuries (x : DimActivity) : ℝ :=
  activityInBecquerels x / 37000000

/-- SI readout of an area, in square meters. -/
noncomputable def areaInSquareMeters (x : DimArea) : ℝ :=
  ((x.1 SI).1 : ℝ)

/-- SI readout of an energy, in joules. -/
noncomputable def energyInJoules (x : DimEnergy) : ℝ :=
  (x.1 SI).1

/-- Energy readout in MeV, grounded by Physlib's electron-volt constant. -/
noncomputable def energyInMegaElectronVolts (x : DimEnergy) : ℝ :=
  energyInJoules x /
    (10 ^ 6 * energyInJoules DimEnergy.electronVolt)

/-- SI specific-energy readout.  For absorbed dose, this is measured in gray. -/
noncomputable def specificEnergyInSI (x : DimSpecificEnergy) : ℝ :=
  (x.1 SI).1

/-- The radionuclide identity needed by this problem. -/
inductive Nuclide
  | cobalt60
  deriving DecidableEq

/--
The physical quantities describing the daily cobalt-60 exposure.  The two
gamma energies are separate because cobalt-60 emits both photons in quick
succession in each decay.
-/
structure Cobalt60Exposure where
  nuclide : Nuclide
  sourceActivity : DimActivity
  workerMass : DimMass
  bodyCrossSection : DimArea
  sourceDistance : DimLength
  dailyExposure : DimTime
  gammaEnergyHigh : DimEnergy
  gammaEnergyLow : DimEnergy
  depositionFraction : ℝ
  transmissionFraction : ℝ
  gammaRadiationWeightingFactor : ℝ

/-- Absorbed and gamma-equivalent whole-body dose for the same exposure. -/
structure WholeBodyDose where
  absorbedSpecificEnergy : DimSpecificEnergy
  equivalentSpecificEnergy : DimSpecificEnergy

/-- Intermediate physical quantities produced by a dose calculation. -/
structure DoseComputation (setup : Cobalt60Exposure) where
  numberOfDecays : ℝ
  geometricInterceptionFraction : ℝ
  depositedEnergy : DimEnergy
  wholeBodyDose : WholeBodyDose

/--
Problem-statement and figure readouts.  The approximate values in the source
are modeled by their stated central values; approximation is restored in the
rounded target below.
-/
structure MatchesProblemData (setup : Cobalt60Exposure) : Prop where
  nuclide_eq : setup.nuclide = .cobalt60
  sourceActivity_milliCurie :
    activityInMilliCuries setup.sourceActivity = 40
  workerMass_kilogram :
    massInKilograms setup.workerMass = 70
  bodyCrossSection_squareMeter :
    areaInSquareMeters setup.bodyCrossSection = 1.5
  figureDistance_meter :
    lengthInMeters setup.sourceDistance = 4
  dailyExposure_hour :
    timeInHours setup.dailyExposure = 4
  gammaEnergyHigh_megaElectronVolt :
    energyInMegaElectronVolts setup.gammaEnergyHigh = 1.33
  gammaEnergyLow_megaElectronVolt :
    energyInMegaElectronVolts setup.gammaEnergyLow = 1.17
  depositionFraction_eq : setup.depositionFraction = (1 / 2 : ℝ)
  transmissionFraction_eq : setup.transmissionFraction = (1 / 2 : ℝ)

/--
Governing physics for the calculation: interaction/transmission partition,
activity integrated over time, inverse-square interception by the body,
full-energy deposition for interacting photons, energy per unit mass, and the
unit radiation weighting factor for gamma rays.
-/
structure ValidDosePhysics
    (setup : Cobalt60Exposure) (result : DoseComputation setup) : Prop where
  interaction_transmission_partition :
    setup.depositionFraction + setup.transmissionFraction = 1
  gamma_radiation_weighting_factor :
    setup.gammaRadiationWeightingFactor = 1
  decays_during_exposure :
    result.numberOfDecays =
      activityInBecquerels setup.sourceActivity *
        timeInSeconds setup.dailyExposure
  isotropic_point_source_interception :
    result.geometricInterceptionFraction =
      areaInSquareMeters setup.bodyCrossSection /
        (4 * Real.pi * lengthInMeters setup.sourceDistance ^ 2)
  deposited_energy :
    energyInJoules result.depositedEnergy =
      result.numberOfDecays * result.geometricInterceptionFraction *
        setup.depositionFraction *
        (energyInJoules setup.gammaEnergyHigh +
          energyInJoules setup.gammaEnergyLow)
  absorbed_whole_body_dose :
    specificEnergyInSI result.wholeBodyDose.absorbedSpecificEnergy =
      energyInJoules result.depositedEnergy /
        massInKilograms setup.workerMass
  gamma_equivalent_dose :
    specificEnergyInSI result.wholeBodyDose.equivalentSpecificEnergy =
      setup.gammaRadiationWeightingFactor *
        specificEnergyInSI result.wholeBodyDose.absorbedSpecificEnergy

/-- Equivalent whole-body dose readout in millisieverts. -/
noncomputable def doseInMilliSieverts (dose : WholeBodyDose) : ℝ :=
  1000 * specificEnergyInSI dose.equivalentSpecificEnergy

/-- The four answer labels shown in the problem. -/
inductive DoseAnswerChoice
  | A
  | B
  | C
  | D
  deriving DecidableEq

/-- Numerical answer-choice readouts, in millisieverts. -/
def answerValueMilliSievert : DoseAnswerChoice → ℝ
  | .A => 0.42
  | .B => 0.48
  | .C => 0.45
  | .D => 0.51

/--
Blueprint target `thm:physics:phyx_mini_0619:target`:
the daily whole-body dose rounds to `0.45 mSv`, and choice C is the unique
closest listed answer.
-/
theorem dailyWholeBodyDose_is_choice_C
    (setup : Cobalt60Exposure) (result : DoseComputation setup)
    (hData : MatchesProblemData setup)
    (hPhysics : ValidDosePhysics setup result) :
    |doseInMilliSieverts result.wholeBodyDose -
        answerValueMilliSievert .C| < 0.005 ∧
      ∀ choice : DoseAnswerChoice, choice ≠ .C →
        |doseInMilliSieverts result.wholeBodyDose -
            answerValueMilliSievert .C| <
          |doseInMilliSieverts result.wholeBodyDose -
            answerValueMilliSievert choice| := by
  have hElectronVolt :
      energyInJoules DimEnergy.electronVolt = (1.602176634e-19 : ℝ) := by
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hActivity :
      activityInBecquerels setup.sourceActivity = 40 * 37000000 := by
    have h := hData.sourceActivity_milliCurie
    rw [activityInMilliCuries] at h
    calc
      activityInBecquerels setup.sourceActivity =
          (activityInBecquerels setup.sourceActivity / 37000000) * 37000000 := by
            rw [div_mul_cancel₀]
            norm_num
      _ = 40 * 37000000 := by rw [h]
  have hTime : timeInSeconds setup.dailyExposure = 4 * 3600 := by
    have h := hData.dailyExposure_hour
    rw [timeInHours] at h
    calc
      timeInSeconds setup.dailyExposure =
          (timeInSeconds setup.dailyExposure / 3600) * 3600 := by
            rw [div_mul_cancel₀]
            norm_num
      _ = 4 * 3600 := by rw [h]
  have hHigh :
      energyInJoules setup.gammaEnergyHigh =
        1.33 * (10 ^ 6 * (1.602176634e-19 : ℝ)) := by
    have h := hData.gammaEnergyHigh_megaElectronVolt
    rw [energyInMegaElectronVolts, hElectronVolt] at h
    calc
      energyInJoules setup.gammaEnergyHigh =
          (energyInJoules setup.gammaEnergyHigh /
              (10 ^ 6 * (1.602176634e-19 : ℝ))) *
            (10 ^ 6 * (1.602176634e-19 : ℝ)) := by
              rw [div_mul_cancel₀]
              norm_num
      _ = 1.33 * (10 ^ 6 * (1.602176634e-19 : ℝ)) := by rw [h]
  have hLow :
      energyInJoules setup.gammaEnergyLow =
        1.17 * (10 ^ 6 * (1.602176634e-19 : ℝ)) := by
    have h := hData.gammaEnergyLow_megaElectronVolt
    rw [energyInMegaElectronVolts, hElectronVolt] at h
    calc
      energyInJoules setup.gammaEnergyLow =
          (energyInJoules setup.gammaEnergyLow /
              (10 ^ 6 * (1.602176634e-19 : ℝ))) *
            (10 ^ 6 * (1.602176634e-19 : ℝ)) := by
              rw [div_mul_cancel₀]
              norm_num
      _ = 1.17 * (10 ^ 6 * (1.602176634e-19 : ℝ)) := by rw [h]
  have hDose :
      doseInMilliSieverts result.wholeBodyDose =
        ((800287228683 : ℝ) / 560000000000) / Real.pi := by
    rw [doseInMilliSieverts, hPhysics.gamma_equivalent_dose,
      hPhysics.absorbed_whole_body_dose, hPhysics.deposited_energy,
      hPhysics.decays_during_exposure,
      hPhysics.isotropic_point_source_interception,
      hPhysics.gamma_radiation_weighting_factor, hActivity, hTime,
      hData.bodyCrossSection_squareMeter, hData.figureDistance_meter,
      hData.depositionFraction_eq, hHigh, hLow,
      hData.workerMass_kilogram]
    ring
  have hSinLt : ∀ {x : ℝ}, 0 < x → Real.sin x < x := by
    intro x hx
    rcases lt_or_ge 1 x with h' | h'
    · exact (Real.sin_le_one x).trans_lt h'
    have hax : |x| = x := abs_of_nonneg hx.le
    have hb := le_of_abs_le
      (Real.sin_bound (show |x| ≤ 1 by rwa [hax]))
    rw [sub_le_iff_le_add', hax] at hb
    apply hb.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le h'
    simp
  have hPiLowerSeries : ∀ n : ℕ,
      (2 : ℝ) ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) <
        Real.pi := by
    intro n
    have h :
        √(2 - Real.sqrtTwoAddSeries 0 n) / 2 * (2 : ℝ) ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply hSinLt
        apply div_pos Real.pi_pos
      all_goals positivity
    refine lt_of_le_of_lt (le_of_eq ?_) h
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have hPiLowerStart : ∀ (n : ℕ) {a : ℝ},
      Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
          (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2 →
        a < Real.pi := by
    intro n a h
    refine lt_of_le_of_lt ?_ (hPiLowerSeries n)
    rw [mul_comm]
    refine (div_le_iff₀ (pow_pos (by norm_num) _)).mp
      (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm,
      show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by norm_num]
  have hPiLowerStep : ∀ (c d : ℕ) {a b n : ℕ} {z : ℝ},
      Real.sqrtTwoAddSeries (c / d) n ≤ z →
      0 < b → 0 < d →
      (2 * b + a) * d ^ 2 ≤ c ^ 2 * b →
      Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
    intro c d a b n z hz hb hd h
    refine le_trans ?_ hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
      div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
      div_le_div_iff₀ hb' (pow_pos hd' _)]
    exact_mod_cast h
  have hPiLower : (3.1415 : ℝ) < Real.pi := by
    refine hPiLowerStart 6 ?_
    refine hPiLowerStep 1970 1393 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine hPiLowerStep 3010 1629 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine hPiLowerStep 11689 5959 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine hPiLowerStep 10127 5088 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine hPiLowerStep 33997 17019 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine hPiLowerStep 23235 11621 ?_ (by norm_num) (by norm_num) (by norm_num)
    norm_num [Real.sqrtTwoAddSeries]
  have hSinGtSubCube : ∀ {x : ℝ}, 0 < x → x ≤ 1 →
      x - x ^ 3 / 4 < Real.sin x := by
    intro x hx hx1
    have hax : |x| = x := abs_of_nonneg hx.le
    have hb := neg_le_of_abs_le
      (Real.sin_bound (show |x| ≤ 1 by rwa [hax]))
    rw [le_sub_iff_add_le, hax] at hb
    refine lt_of_lt_of_le ?_ hb
    have heq :
        x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', heq]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx1
    simp
  have hPiUpperSeries : ∀ n : ℕ,
      Real.pi <
        (2 : ℝ) ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) +
          1 / (4 : ℝ) ^ n := by
    intro n
    have h : Real.pi <
        (√(2 - Real.sqrtTwoAddSeries 0 n) / 2 +
            1 / ((2 : ℝ) ^ n) ^ 3 / 4) *
          (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by positivity),
        ← Real.sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
      calc
        Real.pi / (2 : ℝ) ^ (n + 2) -
              Real.sin (Real.pi / (2 : ℝ) ^ (n + 2)) <
            (Real.pi / (2 : ℝ) ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <| hSinGtSubCube (by positivity) <|
            div_le_one_of_le₀ (by
              calc
                Real.pi ≤ 4 := Real.pi_le_four
                _ = (2 : ℝ) ^ (0 + 2) := by norm_num
                _ ≤ (2 : ℝ) ^ (n + 2) := by
                  gcongr <;> norm_num)
              (by positivity)
        _ ≤ (4 / (2 : ℝ) ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / ((2 : ℝ) ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le h (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      div_div, ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc,
        mul_comm n]
    all_goals norm_num
  have hsqrt2 : (1.414 : ℝ) ≤ √2 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hsqrtNested :
      (1.847 : ℝ) ≤ Real.sqrtTwoAddSeries 0 2 := by
    simp only [Real.sqrtTwoAddSeries]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqrtOuter :
      √(2 - Real.sqrtTwoAddSeries 0 2) ≤ (0.392 : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hsqrtOuter' :
      √(2 - √(2 + √2)) ≤ (0.392 : ℝ) := by
    simpa [Real.sqrtTwoAddSeries] using hsqrtOuter
  have hPiUpper : Real.pi < (3.21 : ℝ) := by
    have h := hPiUpperSeries 2
    norm_num at h
    nlinarith
  rw [hDose]
  have hDoseLower :
      (0.445 : ℝ) <
        ((800287228683 : ℝ) / 560000000000) / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith
  have hDoseUpper :
      ((800287228683 : ℝ) / 560000000000) / Real.pi <
        (0.455 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith
  have hClose :
      |((800287228683 : ℝ) / 560000000000) / Real.pi - 0.45| <
        (0.005 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  constructor
  · simpa [answerValueMilliSievert] using hClose
  intro choice hchoice
  cases choice with
  | A =>
      simp only [answerValueMilliSievert]
      have hpos :
          0 < ((800287228683 : ℝ) / 560000000000) / Real.pi -
            0.42 := by
        nlinarith
      rw [abs_of_pos hpos]
      nlinarith [hClose]
  | B =>
      simp only [answerValueMilliSievert]
      have hneg :
          ((800287228683 : ℝ) / 560000000000) / Real.pi -
            0.48 < 0 := by
        nlinarith
      rw [abs_of_neg hneg]
      nlinarith [hClose]
  | C =>
      exact (hchoice rfl).elim
  | D =>
      simp only [answerValueMilliSievert]
      have hneg :
          ((800287228683 : ℝ) / 560000000000) / Real.pi -
            0.51 < 0 := by
        nlinarith
      rw [abs_of_neg hneg]
      nlinarith [hClose]

end PhyXMini0619
