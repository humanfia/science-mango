import Mathlib
import Physlib.QuantumMechanics.Hydrogen.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0637

open Dimension

/-!
# Hydrogen fluorescence after ultraviolet absorption

A ground-state hydrogen atom absorbs a photon whose measured wavelength is
`95.10 nm`.  The subsequently emitted photon accompanies a downward jump with
`Δn = 3`.  The supplied raster is a qualitative energy-level diagram: it shows
the ground line, a dashed ionization limit, an upward absorption arrow, and a
downward emission arrow.

Physical wavelengths and energies are represented by unit-independent Physlib
quantities.  Real numbers occur only at named-unit readout boundaries and in
the displayed multiple-choice data.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length used as a photon wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Read a unit-independent energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an energy in electron volts using Physlib's calibrated electron volt. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a physical wavelength in a selected unit of length. -/
def wavelengthReadout
    (unit : LengthUnit) (wavelength : WavelengthQuantity) : ℝ :=
  ((wavelength ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- Metre readout of a photon wavelength. -/
def wavelengthInMeters (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.meters wavelength

/-- Nanometre readout used for the measured and displayed wavelengths. -/
def wavelengthInNanometers (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.nanometers wavelength

/-!
The product `h c` in electron-volt nanometres.  Physlib supplies the reduced
Planck constant `ℏ`, the SI speed of light, and the electron-volt calibration;
`2π` converts `ℏ` to `h`, while `10^9` converts metres to nanometres.
-/
def planckTimesLightInElectronVoltNanometers : ℝ :=
  (2 * Real.pi * (Constants.ℏ : ℝ)) *
      (DimSpeed.speedOfLight UnitChoices.SI).val * (10 : ℝ) ^ 9 /
    energyInJoules DimEnergy.electronVolt

/-! ## Labels and qualitative facts from the supplied figure -/

/-- Text labels visibly printed in the raster. -/
inductive FigureTextLabel where
  | principalQuantumNumber
  | groundState
  | ionizationLimit
  | absorption
  | emission
  deriving DecidableEq, Fintype, Repr

/-- The two straight transition arrows in the diagram. -/
inductive TransitionArrow where
  | absorption
  | emission
  deriving DecidableEq, Fintype, Repr

/-!
Presentation data extracted from image `637.png`.  It deliberately records no
numerical emitted wavelength and does not identify either endpoint of the
emission arrow with a particular principal quantum number.
-/
structure HydrogenFluorescenceFigure where
  showsTextLabel : FigureTextLabel → Bool
  groundLevelLineShown : Bool
  displayedGroundPrincipalQuantumNumber : Option ℕ
  upperHorizontalLevelLineCount : ℕ
  ionizationLimitLineShown : Bool
  ionizationLimitLineDashed : Bool
  transitionArrowShown : TransitionArrow → Bool
  transitionArrowPointsUpward : TransitionArrow → Bool
  transitionArrowPointsDownward : TransitionArrow → Bool
  wavyPhotonMarkShown : TransitionArrow → Bool

/-!
Literal readouts from the primary raster.  The image shows six solid upper
level lines in addition to the ground line, a dashed ionization limit, an
upward absorption arrow, and a downward emission arrow.
-/
structure MatchesSuppliedFluorescenceFigure
    (figure : HydrogenFluorescenceFigure) : Prop where
  everyPrintedTextLabelShown :
    ∀ label, figure.showsTextLabel label = true
  groundLineVisible : figure.groundLevelLineShown = true
  groundLineLabelledOne :
    figure.displayedGroundPrincipalQuantumNumber = some 1
  sixUpperLevelLinesVisible : figure.upperHorizontalLevelLineCount = 6
  ionizationLimitVisible : figure.ionizationLimitLineShown = true
  ionizationLimitDashed : figure.ionizationLimitLineDashed = true
  absorptionArrowVisible :
    figure.transitionArrowShown .absorption = true
  absorptionArrowUpward :
    figure.transitionArrowPointsUpward .absorption = true
  emissionArrowVisible : figure.transitionArrowShown .emission = true
  emissionArrowDownward :
    figure.transitionArrowPointsDownward .emission = true
  bothWavyPhotonMarksVisible :
    ∀ arrow, figure.wavyPhotonMarkShown arrow = true

/-! ## Independent physical setup -/

/-!
The physical observables and state labels for the experiment.  In particular,
the emitted wavelength is an independent dimensionful field; it is not defined
from an answer choice or from the requested value.
-/
structure HydrogenFluorescenceSetup where
  atom : QuantumMechanics.HydrogenAtom
  initialPrincipalQuantumNumber : ℕ
  excitedPrincipalQuantumNumber : ℕ
  emissionFinalPrincipalQuantumNumber : ℕ
  levelEnergy : ℕ → DimEnergy
  absorbedPhotonEnergy : DimEnergy
  absorbedPhotonWavelength : WavelengthQuantity
  emittedPhotonEnergy : DimEnergy
  emittedPhotonWavelength : WavelengthQuantity
  figure : HydrogenFluorescenceFigure

/-! ## Scenario, measurement, reference data, and physical-domain conditions -/

/-- Qualitative facts stated in the problem, including the downward `Δn = 3` jump. -/
structure MatchesHydrogenFluorescenceScenario
    (setup : HydrogenFluorescenceSetup) : Prop where
  atomHasThreeSpatialDimensions : setup.atom.d = 3
  attractiveCoulombCoefficient : 0 < setup.atom.k
  atomInitiallyInGroundState : setup.initialPrincipalQuantumNumber = 1
  absorptionRaisesPrincipalLevel :
    setup.initialPrincipalQuantumNumber < setup.excitedPrincipalQuantumNumber
  emissionFinalLevelPositive :
    0 < setup.emissionFinalPrincipalQuantumNumber
  emissionJumpsDownByThree :
    setup.emissionFinalPrincipalQuantumNumber + 3 =
      setup.excitedPrincipalQuantumNumber
  fluorescenceHasLongerEmittedWavelength :
    wavelengthInNanometers setup.absorbedPhotonWavelength <
      wavelengthInNanometers setup.emittedPhotonWavelength

/-- The ultraviolet wavelength reported in the prose, as a nanometre readout. -/
structure MatchesAbsorbedPhotonMeasurement
    (setup : HydrogenFluorescenceSetup) : Prop where
  absorbedWavelengthNanometers :
    wavelengthInNanometers setup.absorbedPhotonWavelength = (951 / 10 : ℝ)

/-!
Standard ground-level calibration used by the elementary Bohr spectrum.  This
states `E₁ = -13.6 eV`; it does not state the excited level, emission endpoint,
or emitted wavelength.
-/
structure UsesStandardHydrogenReferenceData
    (setup : HydrogenFluorescenceSetup) : Prop where
  groundStateEnergyElectronVolts :
    energyInElectronVolts (setup.levelEnergy 1) = -(68 / 5 : ℝ)

/-- Positivity and bound-state conditions for the physical branch of the model. -/
structure HasPhysicalHydrogenFluorescenceParameters
    (setup : HydrogenFluorescenceSetup) : Prop where
  absorbedPhotonEnergyPositive :
    0 < energyInElectronVolts setup.absorbedPhotonEnergy
  emittedPhotonEnergyPositive :
    0 < energyInElectronVolts setup.emittedPhotonEnergy
  absorbedWavelengthPositive :
    0 < wavelengthInMeters setup.absorbedPhotonWavelength
  emittedWavelengthPositive :
    0 < wavelengthInMeters setup.emittedPhotonWavelength
  boundLevelEnergiesNegative :
    ∀ n : ℕ, 0 < n → energyInElectronVolts (setup.levelEnergy n) < 0

/-! ## Governing laws and rounded-data level identification -/

/-!
The elementary hydrogen spectrum, Planck--Einstein photon relations, and
emission energy balance.  Each law is uniform or relates independent physical
quantities; no field contains `n = 5`, `n = 2`, `434 nm`, or an answer label.
-/
structure SatisfiesHydrogenFluorescenceLaws
    (setup : HydrogenFluorescenceSetup) : Prop where
  hydrogenEnergySpectrum :
    ∀ n : ℕ, 0 < n →
      energyInElectronVolts (setup.levelEnergy n) =
        energyInElectronVolts (setup.levelEnergy 1) / (n : ℝ) ^ 2
  absorbedPhotonPlanckEinstein :
    energyInElectronVolts setup.absorbedPhotonEnergy *
        wavelengthInNanometers setup.absorbedPhotonWavelength =
      planckTimesLightInElectronVoltNanometers
  emittedPhotonEnergyIsLevelGap :
    energyInElectronVolts setup.emittedPhotonEnergy =
      energyInElectronVolts
          (setup.levelEnergy setup.excitedPrincipalQuantumNumber) -
        energyInElectronVolts
          (setup.levelEnergy setup.emissionFinalPrincipalQuantumNumber)
  emittedPhotonPlanckEinstein :
    energyInElectronVolts setup.emittedPhotonEnergy *
        wavelengthInNanometers setup.emittedPhotonWavelength =
      planckTimesLightInElectronVoltNanometers

/-!
Energy obtained by adding the absorbed photon energy to the initial atomic
energy.  It is a scalar electron-volt readout used only to interpret the
rounded wavelength datum.
-/
def postAbsorptionEnergyEstimateElectronVolts
    (setup : HydrogenFluorescenceSetup) : ℝ :=
  energyInElectronVolts
      (setup.levelEnergy setup.initialPrincipalQuantumNumber) +
    energyInElectronVolts setup.absorbedPhotonEnergy

/-!
A positive principal level is the unique closest discrete hydrogen level to
the energy estimate inferred from the rounded `95.10 nm` datum.
-/
def IsUniqueClosestPostAbsorptionLevel
    (setup : HydrogenFluorescenceSetup) (level : ℕ) : Prop :=
  0 < level ∧
    ∀ alternative : ℕ, 0 < alternative → alternative ≠ level →
      |postAbsorptionEnergyEstimateElectronVolts setup -
          energyInElectronVolts (setup.levelEnergy level)| <
        |postAbsorptionEnergyEstimateElectronVolts setup -
          energyInElectronVolts (setup.levelEnergy alternative)|

/-!
Interpretation rule for the rounded absorption measurement.  It selects the
closest positive stationary level without naming which level that is.
-/
structure UsesRoundedAbsorptionLevelIdentification
    (setup : HydrogenFluorescenceSetup) : Prop where
  excitedLevelIsUniqueClosest :
    IsUniqueClosestPostAbsorptionLevel
      setup setup.excitedPrincipalQuantumNumber

/-! ## Derived transition relations -/

/-- The rounded absorption datum and standard spectrum identify the excited level. -/
lemma absorbedPhoton_identifies_excitedLevelFive
    (setup : HydrogenFluorescenceSetup)
    (_scenario : MatchesHydrogenFluorescenceScenario setup)
    (_measurement : MatchesAbsorbedPhotonMeasurement setup)
    (_reference : UsesStandardHydrogenReferenceData setup)
    (_physical : HasPhysicalHydrogenFluorescenceParameters setup)
    (_laws : SatisfiesHydrogenFluorescenceLaws setup)
    (_identification : UsesRoundedAbsorptionLevelIdentification setup) :
    setup.excitedPrincipalQuantumNumber = 5 := by
  have hhc_lower :
      (1239 : ℝ) < planckTimesLightInElectronVoltNanometers := by
    rw [planckTimesLightInElectronVoltNanometers]
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, Constants.ℏ]
    norm_num
    nlinarith [Real.pi_gt_d6]
  have hhc_upper :
      planckTimesLightInElectronVoltNanometers < (1240 : ℝ) := by
    rw [planckTimesLightInElectronVoltNanometers]
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, Constants.ℏ]
    norm_num
    nlinarith [Real.pi_lt_d6]
  have habsorption := _laws.absorbedPhotonPlanckEinstein
  rw [_measurement.absorbedWavelengthNanometers] at habsorption
  have habsorbed_lower :
      (13 : ℝ) < energyInElectronVolts setup.absorbedPhotonEnergy := by
    nlinarith
  have habsorbed_upper :
      energyInElectronVolts setup.absorbedPhotonEnergy < (261 / 20 : ℝ) := by
    nlinarith
  have hpost_lower :
      (-3 / 5 : ℝ) < postAbsorptionEnergyEstimateElectronVolts setup := by
    simp only [postAbsorptionEnergyEstimateElectronVolts,
      _scenario.atomInitiallyInGroundState,
      _reference.groundStateEnergyElectronVolts]
    linarith
  have hpost_upper :
      postAbsorptionEnergyEstimateElectronVolts setup < (-11 / 20 : ℝ) := by
    simp only [postAbsorptionEnergyEstimateElectronVolts,
      _scenario.atomInitiallyInGroundState,
      _reference.groundStateEnergyElectronVolts]
    linarith
  have henergy_five :
      energyInElectronVolts (setup.levelEnergy 5) = (-68 / 125 : ℝ) := by
    rw [_laws.hydrogenEnergySpectrum 5 (by norm_num),
      _reference.groundStateEnergyElectronVolts]
    norm_num
  have hexcited_gt_one : 1 < setup.excitedPrincipalQuantumNumber := by
    simpa [_scenario.atomInitiallyInGroundState] using
      _scenario.absorptionRaisesPrincipalLevel
  by_contra hexcited_ne_five
  have hcloser :=
    _identification.excitedLevelIsUniqueClosest.2 5 (by norm_num)
      (Ne.symm hexcited_ne_five)
  have hfive_difference_neg :
      postAbsorptionEnergyEstimateElectronVolts setup -
          energyInElectronVolts (setup.levelEnergy 5) < 0 := by
    rw [henergy_five]
    linarith
  rcases (show setup.excitedPrincipalQuantumNumber = 2 ∨
      setup.excitedPrincipalQuantumNumber = 3 ∨
      setup.excitedPrincipalQuantumNumber = 4 ∨
      6 ≤ setup.excitedPrincipalQuantumNumber by omega) with
      htwo | hthree | hfour | hsix
  · have henergy_two :
        energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) =
          (-17 / 5 : ℝ) := by
      rw [_laws.hydrogenEnergySpectrum
          setup.excitedPrincipalQuantumNumber (by omega),
        _reference.groundStateEnergyElectronVolts, htwo]
      norm_num
    have hdifference_pos :
        0 < postAbsorptionEnergyEstimateElectronVolts setup -
          energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) := by
      rw [henergy_two]
      linarith
    rw [abs_of_pos hdifference_pos, abs_of_neg hfive_difference_neg,
      henergy_two, henergy_five] at hcloser
    linarith
  · have henergy_three :
        energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) =
          (-68 / 45 : ℝ) := by
      rw [_laws.hydrogenEnergySpectrum
          setup.excitedPrincipalQuantumNumber (by omega),
        _reference.groundStateEnergyElectronVolts, hthree]
      norm_num
    have hdifference_pos :
        0 < postAbsorptionEnergyEstimateElectronVolts setup -
          energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) := by
      rw [henergy_three]
      linarith
    rw [abs_of_pos hdifference_pos, abs_of_neg hfive_difference_neg,
      henergy_three, henergy_five] at hcloser
    linarith
  · have henergy_four :
        energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) =
          (-17 / 20 : ℝ) := by
      rw [_laws.hydrogenEnergySpectrum
          setup.excitedPrincipalQuantumNumber (by omega),
        _reference.groundStateEnergyElectronVolts, hfour]
      norm_num
    have hdifference_pos :
        0 < postAbsorptionEnergyEstimateElectronVolts setup -
          energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) := by
      rw [henergy_four]
      linarith
    rw [abs_of_pos hdifference_pos, abs_of_neg hfive_difference_neg,
      henergy_four, henergy_five] at hcloser
    linarith
  · have hprincipal_real :
        (6 : ℝ) ≤ (setup.excitedPrincipalQuantumNumber : ℝ) := by
      exact_mod_cast hsix
    have hsquare :
        (36 : ℝ) ≤ (setup.excitedPrincipalQuantumNumber : ℝ) ^ 2 := by
      nlinarith
    have hsquare_pos :
        0 < (setup.excitedPrincipalQuantumNumber : ℝ) ^ 2 := by
      positivity
    have henergy_formula :
        energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) =
          (-68 / 5 : ℝ) /
            (setup.excitedPrincipalQuantumNumber : ℝ) ^ 2 := by
      rw [_laws.hydrogenEnergySpectrum
          setup.excitedPrincipalQuantumNumber (by omega),
        _reference.groundStateEnergyElectronVolts]
      ring
    have henergy_lower :
        (-17 / 45 : ℝ) ≤
          energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) := by
      rw [henergy_formula]
      apply (le_div_iff₀ hsquare_pos).2
      nlinarith
    have hdifference_neg :
        postAbsorptionEnergyEstimateElectronVolts setup -
          energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) < 0 := by
      linarith
    rw [abs_of_neg hdifference_neg, abs_of_neg hfive_difference_neg,
      henergy_five] at hcloser
    linarith

/-- Combining the identified excited state with `Δn = 3` gives the `5 → 2` jump. -/
lemma emissionTransition_is_fiveToTwo
    (setup : HydrogenFluorescenceSetup)
    (_scenario : MatchesHydrogenFluorescenceScenario setup)
    (_measurement : MatchesAbsorbedPhotonMeasurement setup)
    (_reference : UsesStandardHydrogenReferenceData setup)
    (_physical : HasPhysicalHydrogenFluorescenceParameters setup)
    (_laws : SatisfiesHydrogenFluorescenceLaws setup)
    (_identification : UsesRoundedAbsorptionLevelIdentification setup) :
    setup.excitedPrincipalQuantumNumber = 5 ∧
      setup.emissionFinalPrincipalQuantumNumber = 2 := by
  have hexcited :
      setup.excitedPrincipalQuantumNumber = 5 :=
    absorbedPhoton_identifies_excitedLevelFive setup _scenario _measurement
      _reference _physical _laws _identification
  constructor
  · exact hexcited
  · have hjump := _scenario.emissionJumpsDownByThree
    omega

/-!
Solving the emission photon law expresses its wavelength through the physical
level-energy gap.  This helper does not assign a displayed numeric answer.
-/
lemma emittedPhotonWavelength_eq_planckTimesLight_div_levelGap
    (setup : HydrogenFluorescenceSetup)
    (_physical : HasPhysicalHydrogenFluorescenceParameters setup)
    (_laws : SatisfiesHydrogenFluorescenceLaws setup) :
    wavelengthInNanometers setup.emittedPhotonWavelength =
      planckTimesLightInElectronVoltNanometers /
        (energyInElectronVolts
            (setup.levelEnergy setup.excitedPrincipalQuantumNumber) -
          energyInElectronVolts
            (setup.levelEnergy setup.emissionFinalPrincipalQuantumNumber)) := by
  rw [← _laws.emittedPhotonEnergyIsLevelGap]
  apply (eq_div_iff (ne_of_gt _physical.emittedPhotonEnergyPositive)).2
  simpa [mul_comm] using _laws.emittedPhotonPlanckEinstein

/-! ## Displayed answers and target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Wavelength printed next to each answer label, in nanometres. -/
def AnswerChoice.wavelengthNanometers : AnswerChoice → ℝ
  | .A => 424
  | .B => 434
  | .C => 444
  | .D => 454

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A physical wavelength rounds to the displayed whole-nanometre value. -/
def RoundsToDisplayedWavelength
    (wavelength : WavelengthQuantity) (choice : AnswerChoice) : Prop :=
  |wavelengthInNanometers wavelength - choice.wavelengthNanometers| < (1 / 2 : ℝ)

/-- A displayed answer is strictly nearer to the physical wavelength than every alternative. -/
def IsUniqueClosestDisplayedWavelength
    (wavelength : WavelengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice, alternative ≠ choice →
    |wavelengthInNanometers wavelength - choice.wavelengthNanometers| <
      |wavelengthInNanometers wavelength - alternative.wavelengthNanometers|

/-!
The absorption measurement identifies `n = 5`; the stated downward
`Δn = 3` emission therefore ends at `n = 2`.  The resulting photon wavelength
rounds to `434 nm`, uniquely selecting choice B.

Blueprint: `thm:physics:phyx_mini_0637:target`.
-/
theorem emittedPhotonWavelength_is_recordedChoiceB
    (setup : HydrogenFluorescenceSetup)
    (_scenario : MatchesHydrogenFluorescenceScenario setup)
    (_measurement : MatchesAbsorbedPhotonMeasurement setup)
    (_figure : MatchesSuppliedFluorescenceFigure setup.figure)
    (_reference : UsesStandardHydrogenReferenceData setup)
    (_physical : HasPhysicalHydrogenFluorescenceParameters setup)
    (_laws : SatisfiesHydrogenFluorescenceLaws setup)
    (_identification : UsesRoundedAbsorptionLevelIdentification setup) :
    setup.excitedPrincipalQuantumNumber = 5 ∧
      setup.emissionFinalPrincipalQuantumNumber = 2 ∧
      RoundsToDisplayedWavelength setup.emittedPhotonWavelength .B ∧
      IsUniqueClosestDisplayedWavelength setup.emittedPhotonWavelength .B ∧
      recordedDatasetAnswer = .B := by
  have htransition :=
    emissionTransition_is_fiveToTwo setup _scenario _measurement _reference
      _physical _laws _identification
  rcases htransition with ⟨hexcited, hfinal⟩
  have henergy_five :
      energyInElectronVolts (setup.levelEnergy 5) = (-68 / 125 : ℝ) := by
    rw [_laws.hydrogenEnergySpectrum 5 (by norm_num),
      _reference.groundStateEnergyElectronVolts]
    norm_num
  have henergy_two :
      energyInElectronVolts (setup.levelEnergy 2) = (-17 / 5 : ℝ) := by
    rw [_laws.hydrogenEnergySpectrum 2 (by norm_num),
      _reference.groundStateEnergyElectronVolts]
    norm_num
  have hemission_energy :
      energyInElectronVolts setup.emittedPhotonEnergy = (357 / 125 : ℝ) := by
    rw [_laws.emittedPhotonEnergyIsLevelGap, hexcited, hfinal,
      henergy_five, henergy_two]
    norm_num
  have hhc_lower :
      (1239 : ℝ) < planckTimesLightInElectronVoltNanometers := by
    rw [planckTimesLightInElectronVoltNanometers]
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, Constants.ℏ]
    norm_num
    nlinarith [Real.pi_gt_d6]
  have hhc_upper :
      planckTimesLightInElectronVoltNanometers < (1240 : ℝ) := by
    rw [planckTimesLightInElectronVoltNanometers]
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, Constants.ℏ]
    norm_num
    nlinarith [Real.pi_lt_d6]
  have hemission_law := _laws.emittedPhotonPlanckEinstein
  rw [hemission_energy] at hemission_law
  have hwavelength_lower :
      (867 / 2 : ℝ) <
        wavelengthInNanometers setup.emittedPhotonWavelength := by
    nlinarith
  have hwavelength_upper :
      wavelengthInNanometers setup.emittedPhotonWavelength <
        (869 / 2 : ℝ) := by
    nlinarith
  have hrounds :
      RoundsToDisplayedWavelength setup.emittedPhotonWavelength .B := by
    change
      |wavelengthInNanometers setup.emittedPhotonWavelength - 434| <
        (1 / 2 : ℝ)
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  have hunique :
      IsUniqueClosestDisplayedWavelength
        setup.emittedPhotonWavelength .B := by
    have hround_abs :
        |wavelengthInNanometers setup.emittedPhotonWavelength - 434| <
          (1 / 2 : ℝ) := by
      exact abs_lt.2 ⟨by linarith, by linarith⟩
    intro alternative halternative
    cases alternative with
    | A =>
        change
          |wavelengthInNanometers setup.emittedPhotonWavelength - 434| <
            |wavelengthInNanometers setup.emittedPhotonWavelength - 424|
        have hpositive :
            0 <
              wavelengthInNanometers setup.emittedPhotonWavelength - 424 := by
          linarith
        rw [abs_of_pos hpositive]
        linarith
    | B =>
        exact (halternative rfl).elim
    | C =>
        change
          |wavelengthInNanometers setup.emittedPhotonWavelength - 434| <
            |wavelengthInNanometers setup.emittedPhotonWavelength - 444|
        have hnegative :
            wavelengthInNanometers setup.emittedPhotonWavelength - 444 < 0 := by
          linarith
        rw [abs_of_neg hnegative]
        linarith
    | D =>
        change
          |wavelengthInNanometers setup.emittedPhotonWavelength - 434| <
            |wavelengthInNanometers setup.emittedPhotonWavelength - 454|
        have hnegative :
            wavelengthInNanometers setup.emittedPhotonWavelength - 454 < 0 := by
          linarith
        rw [abs_of_neg hnegative]
        linarith
  exact ⟨hexcited, hfinal, hrounds, hunique, rfl⟩

end PhyXMiniProblems.ProblemPhyXMini0637
