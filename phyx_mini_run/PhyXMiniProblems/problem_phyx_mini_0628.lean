import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0628

open Dimension

/-!
# Wavelength of the `l = 1` to `l = 0` carbon-monoxide rotational line

The problem models a carbon-monoxide molecule as a rigid rotor.  Its moment of
inertia, rotational energies, emitted-photon energy, and wavelength are
unit-independent dimensionful quantities.  Their coherent-SI readouts are
related by the rigid-rotor spectrum, conservation of energy, and the
Planck--Einstein wavelength law.

The supplied figure gives astronomical context: a visible-light view of Orion
is connected by a pink outline to a radio map of the molecular cloud.  Blue and
red radio regions encode motion toward and away from the observer.  These
qualitative readouts do not determine the requested wavelength.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- The physical dimension of a moment of inertia, `mass * length^2`. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- The physical dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-!
A unit-independent speed with a real carrier.  This is the exact dimensional
type used by Physlib's `DimSpeed.speedOfLight`.
-/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Millimetre readout used by the four displayed choices. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Coherent-SI readout of a moment of inertia, in `kg m^2`. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Coherent-SI readout of a speed, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-! ## Molecular-cloud and primary-figure vocabulary -/

/-- Molecular species explicitly discussed in the problem statement. -/
inductive MolecularSpecies where
  | hydrogen
  | carbonMonoxide
  deriving DecidableEq, Repr

/-- Electromagnetic bands used for the two views of the cloud. -/
inductive TelescopeBand where
  | visible
  | radio
  deriving DecidableEq, Repr

/-- The two panels identifiable in the primary image. -/
inductive FigurePanel where
  | upperVisibleOrion
  | lowerRadioCloud
  deriving DecidableEq, Fintype, Repr

/-- Radio-map colors whose Doppler interpretation is stated in the prose. -/
inductive DopplerColor where
  | blue
  | red
  deriving DecidableEq, Fintype, Repr

/-- Motion relative to the molecular cloud as a whole. -/
inductive RelativeLineOfSightMotion where
  | towardObserver
  | awayFromObserver
  deriving DecidableEq, Repr

/-- The two rotational levels named in the transition. -/
inductive RotationalLevel where
  | l0
  | l1
  deriving DecidableEq, Fintype, Repr

/-- Angular-momentum quantum number associated with each named level. -/
def RotationalLevel.quantumNumber : RotationalLevel → ℕ
  | .l0 => 0
  | .l1 => 1

/-!
Qualitative content transcribed from image 628.  The color map records only
the stated Doppler interpretation; it is not a spectral calibration.
-/
structure OrionMolecularCloudFigure where
  panelIsShown : FigurePanel → Bool
  telescopeBand : FigurePanel → TelescopeBand
  orionConstellationLinesShown : Bool
  molecularCloudOutlineShown : Bool
  outlineColorIsPink : Bool
  visibleAndRadioViewsConnected : Bool
  dopplerColorIsShown : DopplerColor → Bool
  motionIndicatedBy : DopplerColor → RelativeLineOfSightMotion
  radioTuningWavelength : LengthQuantity

/-! ## Physical setup, source data, and governing laws -/

/-!
Independent physical objects in the cloud and rotor model.  In particular,
the emitted wavelength is a field, not a definition involving answer A.
-/
structure CarbonMonoxideRotationalTransitionSetup where
  cloudPrimarySpecies : MolecularSpecies
  radioTracerSpecies : MolecularSpecies
  hydrogenMoleculesPerCOMolecule : ℕ
  radiatesInBand : MolecularSpecies → TelescopeBand → Prop
  rotorMomentOfInertia : MomentOfInertiaQuantity
  rotationalEnergy : RotationalLevel → DimEnergy
  transitionInitialLevel : RotationalLevel
  transitionFinalLevel : RotationalLevel
  emittedPhotonEnergy : DimEnergy
  emittedPhotonWavelength : LengthQuantity
  reducedPlanckAction : ActionQuantity
  lightSpeed : SpeedQuantity
  figure : OrionMolecularCloudFigure

/-!
The chemical and transition roles stated in the prose.  This fixes the
transition direction `l = 1` to `l = 0`, but no energy gap or wavelength.
-/
structure MatchesCOMolecularCloudScenario
    (setup : CarbonMonoxideRotationalTransitionSetup) : Prop where
  hydrogenIsPrimarySpecies :
    setup.cloudPrimarySpecies = .hydrogen
  carbonMonoxideIsRadioTracer :
    setup.radioTracerSpecies = .carbonMonoxide
  approximateHydrogenToCORatio :
    setup.hydrogenMoleculesPerCOMolecule = 10000
  hydrogenDoesNotRadiateVisible :
    ¬ setup.radiatesInBand .hydrogen .visible
  hydrogenDoesNotRadiateRadio :
    ¬ setup.radiatesInBand .hydrogen .radio
  carbonMonoxideRadiatesInRadio :
    setup.radiatesInBand .carbonMonoxide .radio
  transitionStartsAtLOne : setup.transitionInitialLevel = .l1
  transitionEndsAtLZero : setup.transitionFinalLevel = .l0

/-!
Salient information from the primary bitmap and its Doppler explanation.  The
radio receiver is tuned to the same physical wavelength as the modeled CO
line, but no numerical wavelength occurs in this figure premise.
-/
structure MatchesPrimaryOrionCloudFigure
    (setup : CarbonMonoxideRotationalTransitionSetup) : Prop where
  bothPanelsShown : ∀ panel, setup.figure.panelIsShown panel = true
  upperPanelIsVisibleLight :
    setup.figure.telescopeBand .upperVisibleOrion = .visible
  lowerPanelIsRadio :
    setup.figure.telescopeBand .lowerRadioCloud = .radio
  constellationLinesShown :
    setup.figure.orionConstellationLinesShown = true
  cloudOutlineShown : setup.figure.molecularCloudOutlineShown = true
  pinkOutline : setup.figure.outlineColorIsPink = true
  viewsConnected : setup.figure.visibleAndRadioViewsConnected = true
  bothDopplerColorsShown :
    ∀ color, setup.figure.dopplerColorIsShown color = true
  blueMeansTowardObserver :
    setup.figure.motionIndicatedBy .blue = .towardObserver
  redMeansAwayFromObserver :
    setup.figure.motionIndicatedBy .red = .awayFromObserver
  radioTunedToEmittedCOLine :
    setup.figure.radioTuningWavelength = setup.emittedPhotonWavelength

/-!
The stated CO moment of inertia and the standard universal constants.  The
moment readout is in `kg m^2`; Physlib grounds `hbar` in joule-seconds and the
vacuum speed of light in metres per second.  No target wavelength occurs here.
-/
structure UsesProblemAndReferenceData
    (setup : CarbonMonoxideRotationalTransitionSetup) : Prop where
  carbonMonoxideMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared setup.rotorMomentOfInertia =
      (1.449 : ℝ) * 10 ^ (-46 : ℤ)
  standardReducedPlanckAction :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)
  standardSpeedOfLight :
    speedInMetersPerSecond setup.lightSpeed =
      speedInMetersPerSecond DimSpeed.speedOfLight

/-- Positivity conditions selecting the physical rotor and photon branch. -/
structure HasPhysicalCORotorParameters
    (setup : CarbonMonoxideRotationalTransitionSetup) : Prop where
  inertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared setup.rotorMomentOfInertia
  rotationalEnergiesNonnegative :
    ∀ level, 0 ≤ energyInJoules (setup.rotationalEnergy level)
  emittedPhotonEnergyPositive :
    0 < energyInJoules setup.emittedPhotonEnergy
  emittedPhotonWavelengthPositive :
    0 < lengthInMeters setup.emittedPhotonWavelength
  reducedPlanckActionPositive :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  lightSpeedPositive : 0 < speedInMetersPerSecond setup.lightSpeed

/-!
The governing physics used in the calculation:

* a rigid rotor has `E_l = hbar^2 l(l+1)/(2I)`;
* the emitted photon carries the initial-minus-final level energy; and
* the photon obeys `E lambda = h c = 2 pi hbar c`.

All equations relate independent fields.  None specializes the wavelength to
a displayed answer.
-/
structure SatisfiesRigidCORotorPhotonLaws
    (setup : CarbonMonoxideRotationalTransitionSetup) : Prop where
  rigidRotorSpectrum : ∀ level : RotationalLevel,
    energyInJoules (setup.rotationalEnergy level) =
      actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
          (level.quantumNumber : ℝ) *
          ((level.quantumNumber : ℝ) + 1) /
        (2 * momentOfInertiaInKilogramMetersSquared
          setup.rotorMomentOfInertia)
  photonEnergyIsTransitionGap :
    energyInJoules setup.emittedPhotonEnergy =
      energyInJoules
          (setup.rotationalEnergy setup.transitionInitialLevel) -
        energyInJoules
          (setup.rotationalEnergy setup.transitionFinalLevel)
  planckEinsteinWavelengthLaw :
    energyInJoules setup.emittedPhotonEnergy *
        lengthInMeters setup.emittedPhotonWavelength =
      2 * Real.pi *
        actionInJouleSeconds setup.reducedPlanckAction *
        speedInMetersPerSecond setup.lightSpeed

/-! ## Displayed choices and current target -/

/-- Labels of the four wavelength choices in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Wavelength printed beside each answer choice, in millimetres. -/
def AnswerChoice.wavelengthMillimeters : AnswerChoice → ℝ
  | .A => 2.59
  | .B => 2.37
  | .C => 1.99
  | .D => 3.12

/-- Dataset metadata records answer A; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
A physical millimetre readout agrees with a value displayed to the nearest
hundredth of a millimetre.  The strict half-step tolerance is `0.005 mm`.
-/
def RoundsToNearestHundredthMillimeter
    (value displayedValue : ℝ) : Prop :=
  |value - displayedValue| < 1 / 200

/-- A displayed choice agrees with the derived physical wavelength. -/
def MatchesDisplayedWavelength
    (setup : CarbonMonoxideRotationalTransitionSetup)
    (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthMillimeter
    (lengthInMillimeters setup.emittedPhotonWavelength)
    choice.wavelengthMillimeters

/-- A choice is the unique displayed value matching the derived wavelength. -/
def IsUniqueMatchingWavelengthChoice
    (setup : CarbonMonoxideRotationalTransitionSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedWavelength setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedWavelength setup other → other = choice

/-!
For the `l = 1` to `l = 0` gap, the rotor and photon laws imply the exact
symbolic relation `lambda = 2 pi I c / hbar`.  This is a derived conclusion,
not a law premise.
-/
lemma emittedWavelengthFormula
    (setup : CarbonMonoxideRotationalTransitionSetup)
    (_scenario : MatchesCOMolecularCloudScenario setup)
    (_physical : HasPhysicalCORotorParameters setup)
    (_laws : SatisfiesRigidCORotorPhotonLaws setup) :
    lengthInMeters setup.emittedPhotonWavelength =
      2 * Real.pi *
        momentOfInertiaInKilogramMetersSquared setup.rotorMomentOfInertia *
        speedInMetersPerSecond setup.lightSpeed /
        actionInJouleSeconds setup.reducedPlanckAction := by
  have hE1 := _laws.rigidRotorSpectrum .l1
  have hE0 := _laws.rigidRotorSpectrum .l0
  norm_num [RotationalLevel.quantumNumber] at hE1 hE0
  have hgap := _laws.photonEnergyIsTransitionGap
  rw [_scenario.transitionStartsAtLOne, _scenario.transitionEndsAtLZero,
    hE1, hE0] at hgap
  have hI0 := ne_of_gt _physical.inertiaPositive
  have ha0 := ne_of_gt _physical.reducedPlanckActionPositive
  have hwave := _laws.planckEinsteinWavelengthLaw
  rw [hgap] at hwave
  field_simp [hI0] at hwave
  field_simp [ha0]
  apply mul_left_cancel₀ ha0
  linear_combination hwave

/-!
Substituting `I_CO = 1.449e-46 kg m^2`, Physlib's `hbar`, and the vacuum speed
of light gives about `2.58817 mm`.  It rounds to `2.59 mm`, uniquely selecting
recorded answer A.

This formalizes blueprint label `thm:physics:phyx_mini_0628:target`.
-/
theorem problem_phyx_mini_0628
    (setup : CarbonMonoxideRotationalTransitionSetup)
    (h_scenario : MatchesCOMolecularCloudScenario setup)
    (_figure : MatchesPrimaryOrionCloudFigure setup)
    (_reference : UsesProblemAndReferenceData setup)
    (h_physical : HasPhysicalCORotorParameters setup)
    (h_laws : SatisfiesRigidCORotorPhotonLaws setup) :
    lengthInMeters setup.emittedPhotonWavelength =
        2 * Real.pi *
          momentOfInertiaInKilogramMetersSquared setup.rotorMomentOfInertia *
          speedInMetersPerSecond setup.lightSpeed /
          actionInJouleSeconds setup.reducedPlanckAction ∧
      IsUniqueMatchingWavelengthChoice setup recordedDatasetAnswer := by
  refine
    ⟨emittedWavelengthFormula setup h_scenario h_physical h_laws, ?_⟩
  have hformula :=
    emittedWavelengthFormula setup h_scenario h_physical h_laws
  rw [_reference.carbonMonoxideMomentOfInertia,
    _reference.standardReducedPlanckAction,
    _reference.standardSpeedOfLight] at hformula
  norm_num [Constants.ℏ, speedInMetersPerSecond, DimSpeed.speedOfLight,
    CarriesDimension.toDimensionful_apply_apply] at hformula
  have meters_to_millimeters (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    let u_m : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.meters }
    let u_mm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.millimeters }
    let scaleFactor : NNReal := ⟨1000, by norm_num⟩
    have hscale : u_m.dimScale u_mm L𝓭 = scaleFactor := by
      norm_num [u_m, u_mm, scaleFactor, UnitChoices.dimScale,
        LengthUnit.millimeters, LengthUnit.scale, LengthUnit.meters,
        LengthUnit.div_eq_val]
    have hchange := congrArg WithDim.val (length.2 u_m u_mm)
    change (length u_mm).val = (1000 : ℝ) * (length u_m).val
    rw [hchange]
    simp only [WithDim.smul_val, WithDim.dim_apply, hscale, smul_eq_mul]
    rfl
  have hmm := meters_to_millimeters setup.emittedPhotonWavelength
  rw [hformula] at hmm
  ring_nf at hmm
  /-
  The packaged decimal bounds for `π` live in a stronger module than this
  file imports.  The following local argument derives just the two bounds
  needed here from `Real.sin_bound` and the imported half-angle identities.
  -/
  have sin_lt_local {x : ℝ} (h : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with h' | h'
    · exact (Real.sin_le_one x).trans_lt h'
    have hx : |x| = x := abs_of_nonneg h.le
    have hb :=
      le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
    rw [sub_le_iff_le_add', hx] at hb
    apply hb.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
    apply pow_le_pow_of_le_one h.le h'
    simp
  have sin_gt_sub_cube_local {x : ℝ} (h : 0 < x) (h' : x ≤ 1) :
      x - x ^ 3 / 4 < Real.sin x := by
    have hx : |x| = x := abs_of_nonneg h.le
    have hb :=
      neg_le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
    rw [le_sub_iff_add_le, hx] at hb
    refine lt_of_lt_of_le ?_ hb
    have hd : x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', hd]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
    apply pow_le_pow_of_le_one h.le h'
    simp
  have pi_gt_series (n : ℕ) :
      2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) <
        Real.pi := by
    have h :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply sin_lt_local
        apply div_pos Real.pi_pos
      all_goals
        apply pow_pos
        norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) h
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have pi_lt_series (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have hpow : Real.pi ≤ (2 : ℝ) ^ (n + 2) := calc
      Real.pi ≤ 4 := Real.pi_le_four
      _ = 2 ^ (0 + 2) := by norm_num
      _ ≤ 2 ^ (n + 2) := by
        gcongr
        · norm_num
        · norm_num
    have h :
        Real.pi <
          (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 +
            1 / (2 ^ n) ^ 3 / 4) * (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by simp), ← Real.sin_pi_over_two_pow_succ,
        ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <| sin_gt_sub_cube_local (by positivity) <|
            div_le_one_of_le₀ hpow (by positivity)
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le h (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div,
      ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc,
        mul_comm n]
    all_goals norm_num
  have pi_lower_start (n : ℕ) {a : ℝ}
      (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
        (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
      a < Real.pi := by
    refine lt_of_le_of_lt ?_ (pi_gt_series n)
    rw [mul_comm]
    refine
      (div_le_iff₀ (pow_pos (by simp) _)).mp
        (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm,
      show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
        rw [Nat.cast_zero, zero_div]]
  have sqrt_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ}
      (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
      (hb : 0 < b) (hd : 0 < d)
      (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
      Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
    refine le_trans ?_ hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
      div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
      div_le_div_iff₀ hb' (pow_pos hd' _)]
    exact_mod_cast h
  have pi_upper_start (n : ℕ) {a : ℝ}
      (h : (2 : ℝ) -
          ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
      (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
      Real.pi < a := by
    refine lt_of_lt_of_le (pi_lt_series n) ?_
    rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left,
      sub_le_comm]
    · rwa [Nat.cast_zero, zero_div] at h
    · exact
        div_nonneg (sub_nonneg.2 h₂)
          (pow_nonneg (le_of_lt zero_lt_two) _)
    · exact pow_pos zero_lt_two _
  have sqrt_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
      (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
      (hb : 0 < b) (hd : 0 < d)
      (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
      z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
    apply le_trans hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    apply Real.le_sqrt_of_sq_le
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
      div_le_div_iff₀ (pow_pos hb' _) hd']
    exact_mod_cast h
  have hpi_lower : (3.14 : ℝ) < Real.pi := by
    apply pi_lower_start 4
    refine
      sqrt_step_up 338 239 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine
      sqrt_step_up 704 381 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine
      sqrt_step_up 1940 989 ?_ (by norm_num) (by norm_num) (by norm_num)
    refine
      sqrt_step_up 1447 727 ?_ (by norm_num) (by norm_num) (by norm_num)
    simp [Real.sqrtTwoAddSeries]
    norm_num
  have hpi_upper : Real.pi < (3.1416 : ℝ) := by
    apply pi_upper_start 9
    · refine
        sqrt_step_down 4756 3363 ?_ (by norm_num) (by norm_num)
          (by norm_num)
      refine
        sqrt_step_down 14965 8099 ?_ (by norm_num) (by norm_num)
          (by norm_num)
      refine
        sqrt_step_down 21183 10799 ?_ (by norm_num) (by norm_num)
          (by norm_num)
      refine
        sqrt_step_down 49188 24713 ?_ (by norm_num) (by norm_num)
          (by norm_num)
      refine
        sqrt_step_down (2 * 22000 - 53) 22000 ?_ (by norm_num)
          (by norm_num) (by norm_num)
      refine
        sqrt_step_down (2 * 117869 - 71) 117869 ?_ (by norm_num)
          (by norm_num) (by norm_num)
      refine
        sqrt_step_down (2 * 312092 - 47) 312092 ?_ (by norm_num)
          (by norm_num) (by norm_num)
      refine
        sqrt_step_down (2 * 451533 - 17) 451533 ?_ (by norm_num)
          (by norm_num) (by norm_num)
      refine
        sqrt_step_down (2 * 424971 - 4) 424971 ?_ (by norm_num)
          (by norm_num) (by norm_num)
      simp [Real.sqrtTwoAddSeries]
      norm_num
    · norm_num
  have hmm_lower :
      (2.585 : ℝ) <
        lengthInMillimeters setup.emittedPhotonWavelength := by
    rw [hmm]
    nlinarith [hpi_lower]
  have hmm_upper :
      lengthInMillimeters setup.emittedPhotonWavelength <
        (2.595 : ℝ) := by
    rw [hmm]
    nlinarith [hpi_upper]
  have hmatchA : MatchesDisplayedWavelength setup .A := by
    rw [MatchesDisplayedWavelength, RoundsToNearestHundredthMillimeter,
      AnswerChoice.wavelengthMillimeters, abs_lt]
    constructor <;> norm_num <;> linarith
  refine ⟨hmatchA, ?_⟩
  intro other hother
  cases other with
  | A => rfl
  | B =>
      exfalso
      rw [MatchesDisplayedWavelength, RoundsToNearestHundredthMillimeter,
        AnswerChoice.wavelengthMillimeters, abs_lt] at hother
      norm_num at hother
      linarith
  | C =>
      exfalso
      rw [MatchesDisplayedWavelength, RoundsToNearestHundredthMillimeter,
        AnswerChoice.wavelengthMillimeters, abs_lt] at hother
      norm_num at hother
      linarith
  | D =>
      exfalso
      rw [MatchesDisplayedWavelength, RoundsToNearestHundredthMillimeter,
        AnswerChoice.wavelengthMillimeters, abs_lt] at hother
      norm_num at hother
      linarith

end PhyXMiniProblems.ProblemPhyXMini0628
