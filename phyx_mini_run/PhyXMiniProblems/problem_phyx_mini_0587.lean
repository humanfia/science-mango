import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0587

open Dimension

/-!
# Well width from the absorption spectrum of an electron

An electron is confined to a one-dimensional infinite square well and begins
in its first excited state, hence at quantum number `n = 2`.  The supplied
figure shows the five longest single-photon absorption wavelengths.  They are
the transitions from `n = 2` to `n = 3, 4, 5, 6, 7`, respectively.

Lengths, mass, action, speed, and energy are represented by unit-independent
Physlib quantities.  Real scalars occur only at explicit unit-readout
boundaries.  The printed wavelengths are decimal measurements to two places
in nanometres, so they are represented by rounding intervals rather than by
physically false exact equalities.  The requested well width is an independent
field; no premise sets it to `350 pm` or selects answer C.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A signed, unit-independent physical speed, matching Physlib's type for `c`. -/
abbrev LightSpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Read a physical length in picometres. -/
def lengthInPicometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.picometers length

/-- Read a mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read an action in coherent SI units, joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read a speed in coherent SI units, metres per second. -/
def speedInMetersPerSecond (speed : LightSpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Physical setup and primary-figure vocabulary -/

/-- Particle species distinguished by the problem statement. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- The confinement model used for the electron. -/
inductive PotentialWellModel where
  | infiniteSquareWell
  | other
  deriving DecidableEq, Repr

/-- Labels attached to the five plotted absorption wavelengths. -/
inductive AbsorptionLineLabel where
  | lambdaA
  | lambdaB
  | lambdaC
  | lambdaD
  | lambdaE
  deriving DecidableEq, Fintype, Repr

/-- Physical role of the horizontal axis in the supplied diagram. -/
inductive FigureAxisRole where
  | wavelength
  | other
  deriving DecidableEq, Repr

/-- Data carried by one single-photon absorption line. -/
structure AbsorptionLine where
  finalQuantumNumber : ℕ
  wavelength : LengthQuantity
  absorbedPhotonEnergy : DimEnergy

/-- Literal qualitative content visible in image `587.png`. -/
structure InfiniteWellAbsorptionFigure where
  horizontalAxisRole : FigureAxisRole
  horizontalAxisUnit : LengthUnit
  zeroTickShown : Bool
  subdivisionTicksShown : Bool
  redPointShown : AbsorptionLineLabel → Bool
  printedLineLabelShown : AbsorptionLineLabel → Bool
  lineAtLeftToRightPosition : Fin 5 → AbsorptionLineLabel

/--
Independent physical quantities in the absorption experiment.  In particular,
`wellWidth` is stored independently of the displayed answer choices.
-/
structure InfiniteWellAbsorptionSetup where
  particleSpecies : ParticleSpecies
  spatialDimension : ℕ
  potentialWellModel : PotentialWellModel
  wellWidth : LengthQuantity
  particleRestMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  vacuumLightSpeed : LightSpeedQuantity
  energyLevel : ℕ → DimEnergy
  initialQuantumNumber : ℕ
  absorptionLine : AbsorptionLineLabel → AbsorptionLine
  figure : InfiniteWellAbsorptionFigure

/-! ## Scenario, data readouts, figure evidence, and governing laws -/

/-- The prose scenario: an electron in the first excited state of a 1D infinite well. -/
structure MatchesFirstExcitedElectronInfiniteWell
    (setup : InfiniteWellAbsorptionSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  oneSpatialDimension : setup.spatialDimension = 1
  wellIsInfiniteSquareWell :
    setup.potentialWellModel = .infiniteSquareWell
  firstExcitedState : setup.initialQuantumNumber = 2

/-- Agreement with a wavelength printed to two decimal places in nanometres. -/
def AgreesWithTwoDecimalNanometerReadout
    (wavelength : LengthQuantity) (displayedNanometers : ℝ) : Prop :=
  |lengthInNanometers wavelength - displayedNanometers| < (1 / 200 : ℝ)

/-- The five wavelength values supplied in the problem statement. -/
structure MatchesGivenAbsorptionWavelengthReadouts
    (setup : InfiniteWellAbsorptionSetup) : Prop where
  lambdaAReadout :
    AgreesWithTwoDecimalNanometerReadout
      (setup.absorptionLine .lambdaA).wavelength 80.78
  lambdaBReadout :
    AgreesWithTwoDecimalNanometerReadout
      (setup.absorptionLine .lambdaB).wavelength 33.66
  lambdaCReadout :
    AgreesWithTwoDecimalNanometerReadout
      (setup.absorptionLine .lambdaC).wavelength 19.23
  lambdaDReadout :
    AgreesWithTwoDecimalNanometerReadout
      (setup.absorptionLine .lambdaD).wavelength 12.62
  lambdaEReadout :
    AgreesWithTwoDecimalNanometerReadout
      (setup.absorptionLine .lambdaE).wavelength 8.98

/--
Primary-image evidence from `587.png`: a wavelength axis in nanometres with a
zero tick, subdivision marks, and five red labelled points ordered
`lambdaE, lambdaD, lambdaC, lambdaB, lambdaA` from left to right.
-/
structure MatchesSuppliedAbsorptionFigure
    (figure : InfiniteWellAbsorptionFigure) : Prop where
  axisRepresentsWavelength : figure.horizontalAxisRole = .wavelength
  axisUsesNanometers : figure.horizontalAxisUnit = LengthUnit.nanometers
  zeroIsShown : figure.zeroTickShown = true
  subdivisionTicksAreShown : figure.subdivisionTicksShown = true
  everyRedPointIsShown : ∀ label, figure.redPointShown label = true
  everyLineLabelIsShown : ∀ label, figure.printedLineLabelShown label = true
  leftmostIsLambdaE : figure.lineAtLeftToRightPosition 0 = .lambdaE
  secondIsLambdaD : figure.lineAtLeftToRightPosition 1 = .lambdaD
  thirdIsLambdaC : figure.lineAtLeftToRightPosition 2 = .lambdaC
  fourthIsLambdaB : figure.lineAtLeftToRightPosition 3 = .lambdaB
  rightmostIsLambdaA : figure.lineAtLeftToRightPosition 4 = .lambdaA

/--
The five longest upward absorptions from `n = 2` reach the next five energy
levels.  This identifies the physical transition represented by each plotted
label without assuming anything about the requested well width.
-/
structure MatchesFiveLongestAbsorptionTransitions
    (setup : InfiniteWellAbsorptionSetup) : Prop where
  lambdaATransitionToThree :
    (setup.absorptionLine .lambdaA).finalQuantumNumber = 3
  lambdaBTransitionToFour :
    (setup.absorptionLine .lambdaB).finalQuantumNumber = 4
  lambdaCTransitionToFive :
    (setup.absorptionLine .lambdaC).finalQuantumNumber = 5
  lambdaDTransitionToSix :
    (setup.absorptionLine .lambdaD).finalQuantumNumber = 6
  lambdaETransitionToSeven :
    (setup.absorptionLine .lambdaE).finalQuantumNumber = 7
  everyTransitionIsUpward : ∀ label,
    setup.initialQuantumNumber <
      (setup.absorptionLine label).finalQuantumNumber

/-- Electron mass, reduced Planck constant, and vacuum light-speed calibrations. -/
structure UsesStandardReferenceData
    (setup : InfiniteWellAbsorptionSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.particleRestMass = 9.1093837015e-31
  reducedPlanckJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)
  vacuumLightSpeedCalibration :
    speedInMetersPerSecond setup.vacuumLightSpeed =
      speedInMetersPerSecond DimSpeed.speedOfLight

/-- Positivity conditions selecting a nondegenerate physical experiment. -/
structure HasPhysicalInfiniteWellParameters
    (setup : InfiniteWellAbsorptionSetup) : Prop where
  positiveWellWidth : 0 < lengthInMeters setup.wellWidth
  positiveElectronMass : 0 < massInKilograms setup.particleRestMass
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  positiveVacuumLightSpeed :
    0 < speedInMetersPerSecond setup.vacuumLightSpeed
  positiveWavelength : ∀ label,
    0 < lengthInMeters (setup.absorptionLine label).wavelength

/--
The one-dimensional infinite-square-well spectrum

`E_n = n^2 * pi^2 * hbar^2 / (2 m L^2)`

for positive quantum numbers.  Physlib currently has no dedicated infinite-
well spectrum declaration, so this is a local governing-law interface.
-/
structure SatisfiesInfiniteSquareWellSpectrum
    (setup : InfiniteWellAbsorptionSetup) : Prop where
  energySpectrum : ∀ n : ℕ, 0 < n →
    energyInJoules (setup.energyLevel n) =
      ((n : ℝ) ^ 2 * Real.pi ^ 2 *
          actionInJouleSeconds setup.reducedPlanckAction ^ 2) /
        (2 * massInKilograms setup.particleRestMass *
          lengthInMeters setup.wellWidth ^ 2)

/--
Each plotted line is a one-photon absorption: the photon energy is
`2 * pi * hbar * c / lambda` and equals the electron's final-minus-initial
level energy.  This is a governing law, not the requested numerical answer.
-/
structure SatisfiesSinglePhotonAbsorptionLaw
    (setup : InfiniteWellAbsorptionSetup) : Prop where
  photonEnergyFromWavelength : ∀ label,
    energyInJoules (setup.absorptionLine label).absorbedPhotonEnergy =
      2 * Real.pi * actionInJouleSeconds setup.reducedPlanckAction *
          speedInMetersPerSecond setup.vacuumLightSpeed /
        lengthInMeters (setup.absorptionLine label).wavelength
  photonRaisesElectron : ∀ label,
    energyInJoules (setup.absorptionLine label).absorbedPhotonEnergy =
      energyInJoules
          (setup.energyLevel
            (setup.absorptionLine label).finalQuantumNumber) -
        energyInJoules (setup.energyLevel setup.initialQuantumNumber)

/-! ## Derived width relation and displayed-answer semantics -/

/--
The `n = 2` to `n = 3` line implies the coherent-SI relation

`L^2 = 5 * pi * hbar * lambdaA / (4 m c)`.

This is a derived conclusion and does not contain the displayed `350 pm`
answer.
-/
lemma wellWidthSquared_from_longestAbsorptionLine
    (setup : InfiniteWellAbsorptionSetup)
    (_scenario : MatchesFirstExcitedElectronInfiniteWell setup)
    (_transitions : MatchesFiveLongestAbsorptionTransitions setup)
    (_physical : HasPhysicalInfiniteWellParameters setup)
    (_spectrum : SatisfiesInfiniteSquareWellSpectrum setup)
    (_absorption : SatisfiesSinglePhotonAbsorptionLaw setup) :
    lengthInMeters setup.wellWidth ^ 2 =
      (5 * Real.pi * actionInJouleSeconds setup.reducedPlanckAction *
          lengthInMeters (setup.absorptionLine .lambdaA).wavelength) /
        (4 * massInKilograms setup.particleRestMass *
          speedInMetersPerSecond setup.vacuumLightSpeed) := by
  have hE3 := _spectrum.energySpectrum 3 (by norm_num)
  have hE2 := _spectrum.energySpectrum 2 (by norm_num)
  have hPhoton := _absorption.photonRaisesElectron .lambdaA
  rw [_absorption.photonEnergyFromWavelength .lambdaA,
      _transitions.lambdaATransitionToThree, _scenario.firstExcitedState,
      hE3, hE2] at hPhoton
  have hL : lengthInMeters setup.wellWidth ≠ 0 :=
    ne_of_gt _physical.positiveWellWidth
  have hm : massInKilograms setup.particleRestMass ≠ 0 :=
    ne_of_gt _physical.positiveElectronMass
  have hh : actionInJouleSeconds setup.reducedPlanckAction ≠ 0 :=
    ne_of_gt _physical.positiveReducedPlanckAction
  have hc : speedInMetersPerSecond setup.vacuumLightSpeed ≠ 0 :=
    ne_of_gt _physical.positiveVacuumLightSpeed
  have hLam :
      lengthInMeters (setup.absorptionLine .lambdaA).wavelength ≠ 0 :=
    ne_of_gt (_physical.positiveWavelength .lambdaA)
  field_simp [hL, hm, hh, hc, hLam] at hPhoton ⊢
  ring_nf at hPhoton ⊢
  nlinarith [hPhoton, Real.pi_pos,
    _physical.positiveReducedPlanckAction]

/-- Labels of the four well-width choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The well width printed beside each answer label, measured in picometres. -/
def displayedWellWidthPicometers : AnswerChoice → ℝ
  | .A => 280
  | .B => 700
  | .C => 350
  | .D => 175

/-- Dataset metadata recording answer C; deliberately not used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a well width displayed to the nearest whole picometre. -/
def AgreesWhenRoundedToNearestPicometer
    (setup : InfiniteWellAbsorptionSetup) (choice : AnswerChoice) : Prop :=
  |lengthInPicometers setup.wellWidth -
      displayedWellWidthPicometers choice| < (1 / 2 : ℝ)

/-- The selected answer is strictly nearer than every other displayed width. -/
def IsUniqueNearestWellWidthChoice
    (setup : InfiniteWellAbsorptionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInPicometers setup.wellWidth -
        displayedWellWidthPicometers choice| <
      |lengthInPicometers setup.wellWidth -
        displayedWellWidthPicometers other|

/--
For the five absorption wavelengths shown in image 587, the infinite-well
width rounds to `350 pm`, uniquely selecting answer C.

This formalizes `thm:physics:phyx_mini_0587:target`.  Neither `350 pm` nor
choice C occurs in any theorem premise.
-/
theorem problem_phyx_mini_0587
    (setup : InfiniteWellAbsorptionSetup)
    (_scenario : MatchesFirstExcitedElectronInfiniteWell setup)
    (_readouts : MatchesGivenAbsorptionWavelengthReadouts setup)
    (_figure : MatchesSuppliedAbsorptionFigure setup.figure)
    (_transitions : MatchesFiveLongestAbsorptionTransitions setup)
    (_reference : UsesStandardReferenceData setup)
    (_physical : HasPhysicalInfiniteWellParameters setup)
    (_spectrum : SatisfiesInfiniteSquareWellSpectrum setup)
    (_absorption : SatisfiesSinglePhotonAbsorptionLaw setup) :
    AgreesWhenRoundedToNearestPicometer setup .C ∧
      IsUniqueNearestWellWidthChoice setup .C := by
  have nanometers_eq (length : LengthQuantity) :
      lengthInNanometers length = 10 ^ 9 * lengthInMeters length := by
    have h := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
      (length.2 UnitChoices.SI
        ({UnitChoices.SI with length := LengthUnit.nanometers} :
          UnitChoices))
    norm_num [lengthInNanometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.scale,
      LengthUnit.meters, LengthUnit.div_eq_val, NNReal.smul_def] at h ⊢
    exact h
  have picometers_eq (length : LengthQuantity) :
      lengthInPicometers length = 10 ^ 12 * lengthInMeters length := by
    have h := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
      (length.2 UnitChoices.SI
        ({UnitChoices.SI with length := LengthUnit.picometers} :
          UnitChoices))
    norm_num [lengthInPicometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.picometers, LengthUnit.scale,
      LengthUnit.meters, LengthUnit.div_eq_val, NNReal.smul_def] at h ⊢
    exact h
  have hLightSpeed :
      speedInMetersPerSecond setup.vacuumLightSpeed = 299792458 := by
    rw [_reference.vacuumLightSpeedCalibration]
    simp [speedInMetersPerSecond]
  have hWidth := wellWidthSquared_from_longestAbsorptionLine setup
    _scenario _transitions _physical _spectrum _absorption
  rw [_reference.electronMassKilograms,
    _reference.reducedPlanckJouleSeconds, hLightSpeed] at hWidth
  norm_num [Constants.ℏ] at hWidth
  have hPico := picometers_eq setup.wellWidth
  have hNano :=
    nanometers_eq (setup.absorptionLine .lambdaA).wavelength
  have hPicoSq := congrArg (fun z : ℝ => z ^ 2) hPico
  have hNanoPi := congrArg (fun z : ℝ => Real.pi * z) hNano
  have hSquared :
      lengthInPicometers setup.wellWidth ^ 2 =
        (35627426250000000000 / 73808771101022251 : ℝ) * Real.pi *
          lengthInNanometers
            (setup.absorptionLine .lambdaA).wavelength := by
    field_simp at hWidth ⊢
    ring_nf at hWidth hPicoSq hNanoPi ⊢
    nlinarith [hWidth, hPicoSq, hNanoPi]

  -- The precise numerical pi-bounds module is not among this file's frozen
  -- imports.  The next local arguments derive the required two-decimal
  -- enclosure directly from the imported sine error and half-angle bounds.
  have sinLt {x : ℝ} (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hOne | hOne
    · exact (Real.sin_le_one x).trans_lt hOne
    have hAbs : |x| = x := abs_of_nonneg hx.le
    have hSin := le_of_abs_le
      (Real.sin_bound (show |x| ≤ 1 by rwa [hAbs]))
    rw [sub_le_iff_le_add', hAbs] at hSin
    apply hSin.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hOne
    simp
  have piGtSeries (n : ℕ) :
      2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) < Real.pi := by
    have hSin :
        √(2 - Real.sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply sinLt
        apply div_pos Real.pi_pos
      all_goals apply pow_pos
      all_goals norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) hSin
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have piLowerStart (n : ℕ) {a : ℝ}
      (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
        (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
      a < Real.pi := by
    refine lt_of_le_of_lt ?_ (piGtSeries n)
    rw [mul_comm]
    refine (div_le_iff₀ (pow_pos (by simp) _)).mp
      (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm, show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
      rw [Nat.cast_zero, zero_div]]
  have sqrtStepUp (c d : ℕ) {a b n : ℕ} {z : ℝ}
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
  have hPiLower : (3.14 : ℝ) < Real.pi := by
    apply piLowerStart 4
    apply sqrtStepUp 338 239
      (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
    apply sqrtStepUp 704 381
      (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
    apply sqrtStepUp 1940 989
      (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
    apply sqrtStepUp 1447 727
      (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
    simp [Real.sqrtTwoAddSeries]
    norm_num1

  have sinGtSubCube {x : ℝ} (hx : 0 < x) (hOne : x ≤ 1) :
      x - x ^ 3 / 4 < Real.sin x := by
    have hAbs : |x| = x := abs_of_nonneg hx.le
    have hSin := neg_le_of_abs_le
      (Real.sin_bound (show |x| ≤ 1 by rwa [hAbs]))
    rw [le_sub_iff_add_le, hAbs] at hSin
    refine lt_of_lt_of_le ?_ hSin
    have hDiff :
        x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', hDiff]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hOne
    simp
  have piLtSeries (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have hSin : Real.pi <
        (√(2 - Real.sqrtTwoAddSeries 0 n) / 2 +
            1 / (2 ^ n) ^ 3 / 4) *
          (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by simp),
        ← Real.sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <| sinGtSubCube (by positivity)
            (div_le_one_of_le₀ (by
              calc
                Real.pi ≤ 4 := Real.pi_le_four
                _ = 2 ^ (0 + 2) := by norm_num
                _ ≤ 2 ^ (n + 2) := by
                  gcongr <;> norm_num) (by positivity))
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le hSin (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num,
      ← pow_mul, div_div, ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n,
        add_assoc, mul_comm n]
    all_goals norm_num
  have piUpperStart (n : ℕ) {a : ℝ}
      (h : (2 : ℝ) -
          ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
      (hSmall : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
      Real.pi < a := by
    refine lt_of_lt_of_le (piLtSeries n) ?_
    rw [← le_sub_iff_add_le, ← le_div_iff₀',
      Real.sqrt_le_left, sub_le_comm]
    · rwa [Nat.cast_zero, zero_div] at h
    · exact div_nonneg (sub_nonneg.2 hSmall)
        (pow_nonneg (le_of_lt zero_lt_two) _)
    · exact pow_pos zero_lt_two _
  have sqrtStepDown (a b : ℕ) {c d n : ℕ} {z : ℝ}
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
  have hPiUpper : Real.pi < (3.15 : ℝ) := by
    apply piUpperStart 4
    · apply sqrtStepDown 41 29
        (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
      apply sqrtStepDown 109 59
        (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
      apply sqrtStepDown 865 441
        (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
      apply sqrtStepDown 412 207
        (hb := by norm_num) (hd := by norm_num) (h := by norm_num)
      simp [Real.sqrtTwoAddSeries]
      norm_num1
    · norm_num

  have hReadout := _readouts.lambdaAReadout
  rw [AgreesWithTwoDecimalNanometerReadout, abs_lt] at hReadout
  norm_num at hReadout
  have hWaveLower : (80.775 : ℝ) <
      lengthInNanometers
        (setup.absorptionLine .lambdaA).wavelength := by
    nlinarith [hReadout.1]
  have hWaveUpper :
      lengthInNanometers
          (setup.absorptionLine .lambdaA).wavelength <
        (80.785 : ℝ) := by
    nlinarith [hReadout.2]
  have hWavePos : 0 <
      lengthInNanometers
        (setup.absorptionLine .lambdaA).wavelength := by
    nlinarith [hWaveLower]
  have hProductLower :
      (3.14 : ℝ) * 80.775 <
        Real.pi * lengthInNanometers
          (setup.absorptionLine .lambdaA).wavelength := by
    exact mul_lt_mul hPiLower hWaveLower.le
      (by norm_num) Real.pi_nonneg
  have hProductUpper :
      Real.pi * lengthInNanometers
          (setup.absorptionLine .lambdaA).wavelength <
        (3.15 : ℝ) * 80.785 := by
    exact mul_lt_mul hPiUpper hWaveUpper.le hWavePos (by norm_num)
  have hPicoPos : 0 < lengthInPicometers setup.wellWidth := by
    rw [picometers_eq]
    nlinarith [_physical.positiveWellWidth]
  have hWidthLower :
      (349.5 : ℝ) < lengthInPicometers setup.wellWidth := by
    have hSqLower :
        (349.5 : ℝ) ^ 2 <
          lengthInPicometers setup.wellWidth ^ 2 := by
      rw [hSquared]
      nlinarith [hProductLower]
    nlinarith
  have hWidthUpper :
      lengthInPicometers setup.wellWidth < (350.5 : ℝ) := by
    have hSqUpper :
        lengthInPicometers setup.wellWidth ^ 2 <
          (350.5 : ℝ) ^ 2 := by
      rw [hSquared]
      nlinarith [hProductUpper]
    nlinarith
  have hCenter :
      |lengthInPicometers setup.wellWidth - 350| < (1 / 2 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  constructor
  · simpa [AgreesWhenRoundedToNearestPicometer,
      displayedWellWidthPicometers] using hCenter
  · rw [IsUniqueNearestWellWidthChoice]
    intro other hOther
    fin_cases other
    · simp only [displayedWellWidthPicometers]
      rw [abs_of_pos (by linarith :
        0 < lengthInPicometers setup.wellWidth - 280)]
      linarith
    · simp only [displayedWellWidthPicometers]
      rw [abs_of_neg (by linarith :
        lengthInPicometers setup.wellWidth - 700 < 0)]
      linarith
    · exact (hOther rfl).elim
    · simp only [displayedWellWidthPicometers]
      rw [abs_of_pos (by linarith :
        0 < lengthInPicometers setup.wellWidth - 175)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0587
