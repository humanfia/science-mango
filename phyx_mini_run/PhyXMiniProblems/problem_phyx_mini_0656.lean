import Mathlib.Algebra.Order.Round
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

/-!
# Length of a rigid box from an electron wavefunction

The supplied graph shows the stationary wavefunction of a `6.0 eV` electron
in a one-dimensional rigid box.  Its four alternating half-wave lobes (two
complete oscillations) identify the fourth infinite-well mode.  The
infinite-square-well energy law then determines a box length close to
`1.0 nm`, answer C.

Lengths, mass, and energy below remain dimensionful physical quantities.
Real numbers are used only for calibrated unit readouts, dimensionless plot
counts and mode numbers, and the numerical values printed in the problem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0656

open Dimension MeasureTheory

/-! ## Physical quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout used by the displayed answer choices. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass ({UnitChoices.SI with mass := MassUnit.kilograms} : UnitChoices)).val : ℝ)

/-- SI joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Electron-volt readout, using Physlib's calibrated electron volt. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-! ## Physical roles and primary-image vocabulary -/

/-- Species of the particle represented by the plotted state. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Confining potential used in the physical model. -/
inductive ConfinementModel where
  | oneDimensionalInfiniteRigidBox
  | other
  deriving DecidableEq, Repr

/-- Axis labels printed in the primary figure. -/
inductive FigureLabel where
  | psiOfX
  | positionX
  deriving DecidableEq, Fintype, Repr

/-- Sign of one consecutive lobe of the plotted real wave amplitude. -/
inductive LobeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-!
Qualitative and integer-valued evidence read from the primary raster.  The
figure has no numerical axis scale and does not draw the vertical box walls;
its flat exterior pieces lie on the horizontal axis.
-/
structure RigidBoxWaveFunctionFigure where
  showsLabel : FigureLabel → Bool
  lobeSignSequence : List LobeSign
  completeOscillationCount : ℕ
  interiorAxisCrossingCount : ℕ
  curveStartsOnHorizontalAxis : Bool
  curveEndsOnHorizontalAxis : Bool
  curveIsRed : Bool
  containsNumericalAxisScale : Bool
  drawsVerticalBoxWalls : Bool

/-!
Independent physical data for the electron state and box.  In particular,
`boxLength` is an observable field and is not defined from the recorded answer.
The representative is retained because an `L²` state is an almost-everywhere
equivalence class while the plotted sine curve is pointwise.
-/
structure RigidBoxElectronSetup where
  particleSpecies : ParticleSpecies
  confinementModel : ConfinementModel
  particleMass : MassQuantity
  boxLength : LengthQuantity
  waveFunction : QuantumMechanics.SpaceDHilbertSpace 1
  waveRepresentative : Space 1 → ℂ
  modeNumber : ℕ
  stateEnergy : DimEnergy
  figure : RigidBoxWaveFunctionFigure

/-! ## Scenario, source data, and figure readouts -/

/-- Categorical facts stated in the physical scenario. -/
structure MatchesRigidBoxElectronScenario
    (setup : RigidBoxElectronSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  boxIsOneDimensionalAndRigid :
    setup.confinementModel = .oneDimensionalInfiniteRigidBox

/-- The energy value explicitly supplied in the question. -/
structure MatchesProblemEnergyReadout
    (setup : RigidBoxElectronSetup) : Prop where
  energyIsSixElectronVolts :
    energyInElectronVolts setup.stateEnergy = 6

/-!
Standard electron-mass data required to evaluate the energy law.  This is
reference data, separate from the problem and figure readouts.
-/
structure UsesElectronMassReferenceData
    (setup : RigidBoxElectronSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.particleMass = 9.1093837139e-31

/-- Raw facts visible in the supplied wavefunction graph. -/
structure MatchesSuppliedWaveFunctionFigure
    (figure : RigidBoxWaveFunctionFigure) : Prop where
  everyPrintedLabelShown : ∀ label, figure.showsLabel label = true
  alternatingFourLobes :
    figure.lobeSignSequence =
      [.positive, .negative, .positive, .negative]
  twoCompleteOscillations : figure.completeOscillationCount = 2
  threeInteriorCrossings : figure.interiorAxisCrossingCount = 3
  startsOnAxis : figure.curveStartsOnHorizontalAxis = true
  endsOnAxis : figure.curveEndsOnHorizontalAxis = true
  redCurve : figure.curveIsRed = true
  noNumericalScale : figure.containsNumericalAxisScale = false
  noVerticalWallsDrawn : figure.drawsVerticalBoxWalls = false

/-! ## Governing quantum-mechanical laws -/

/-!
Interpretation of the plot as the `n`th stationary infinite-well mode.  The
mode number counts half-wave lobes, and a pointwise representative has the
usual sine profile inside `[0,L]` and vanishes outside.  No numerical value of
`L` is part of this governing relation.
-/
structure RepresentsRigidBoxStationaryMode
    (setup : RigidBoxElectronSetup) : Prop where
  modeNumberCountsHalfWaveLobes :
    setup.modeNumber = setup.figure.lobeSignSequence.length
  positiveModeNumber : 0 < setup.modeNumber
  representativeIsSquareIntegrable :
    QuantumMechanics.SpaceDHilbertSpace.MemHS setup.waveRepresentative
  hilbertStateAgreesAlmostEverywhere :
    (setup.waveFunction : Space 1 → ℂ) =ᵐ[volume] setup.waveRepresentative
  sineModeProfile :
    ∃ amplitude : ℂ, amplitude ≠ 0 ∧
      ∀ x : Space 1,
        setup.waveRepresentative x =
          if (x 0 : ℝ) ∈ Set.Icc 0 (lengthInMeters setup.boxLength) then
            amplitude *
              (Real.sin
                ((setup.modeNumber : ℝ) * Real.pi * x 0 /
                  lengthInMeters setup.boxLength) : ℂ)
          else 0

/-!
The one-dimensional infinite-square-well spectrum

`Eₙ = (n π ℏ)² / (2 m L²)`.

The equation uses coherent SI readouts.  Physlib's `Constants.ℏ` is the
reduced Planck constant in joule-seconds.  This is a general law and does not
assume the requested box length or any answer choice.
-/
structure SatisfiesInfiniteRigidBoxEnergyLaw
    (setup : RigidBoxElectronSetup) : Prop where
  quantizedEnergy :
    energyInJoules setup.stateEnergy =
      (((setup.modeNumber : ℝ) * Real.pi * (Constants.ℏ : ℝ)) ^ 2) /
        (2 * massInKilograms setup.particleMass *
          (lengthInMeters setup.boxLength) ^ 2)

/-- Positivity conditions selecting a nondegenerate physical setup. -/
structure HasPhysicalRigidBoxParameters
    (setup : RigidBoxElectronSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.particleMass
  positiveLength : 0 < lengthInMeters setup.boxLength
  positiveEnergy : 0 < energyInJoules setup.stateEnergy

/-! ## Displayed choices and target conclusions -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Nanometre value printed beside each answer label. -/
def displayedLengthInNanometers : AnswerChoice → ℝ
  | .A => 1 / 2
  | .B => 3 / 4
  | .C => 1
  | .D => 2

/-- Answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Round a nanometre readout to the displayed tenth-nanometre precision. -/
def roundedToNearestTenth (value : ℝ) : ℝ :=
  (round (10 * value) : ℝ) / 10

/-- A displayed choice agrees with the calculated rounded box length. -/
def MatchesDisplayedLength
    (setup : RigidBoxElectronSetup)
    (choice : AnswerChoice) : Prop :=
  roundedToNearestTenth (lengthInNanometers setup.boxLength) =
    displayedLengthInNanometers choice

/-- The selected label is the unique displayed choice matching the length. -/
def IsUniqueMatchingDisplayedLength
    (setup : RigidBoxElectronSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedLength setup choice ∧
    ∀ other : AnswerChoice, MatchesDisplayedLength setup other → other = choice

/-!
Four alternating lobes in the supplied graph identify the fourth stationary
mode.  The numerical mode is derived from raw figure evidence and the general
lobe-count interpretation.
-/
lemma modeNumber_eq_four
    (setup : RigidBoxElectronSetup)
    (h_figure : MatchesSuppliedWaveFunctionFigure setup.figure)
    (h_mode : RepresentsRigidBoxStationaryMode setup) :
    setup.modeNumber = 4 := by
  simpa [h_figure.alternatingFourLobes] using
    h_mode.modeNumberCountsHalfWaveLobes

/-!
For mode `n = 4`, energy `6.0 eV`, the electron reference mass, and Physlib's
`ℏ`, the spectrum gives approximately `1.001 nm`.  The stated tolerance is
tighter than the tenth-nanometre precision of the answer choices.
-/
lemma boxLength_within_one_hundredth_nanometer
    (setup : RigidBoxElectronSetup)
    (h_scenario : MatchesRigidBoxElectronScenario setup)
    (h_energy : MatchesProblemEnergyReadout setup)
    (h_mass : UsesElectronMassReferenceData setup)
    (h_figure : MatchesSuppliedWaveFunctionFigure setup.figure)
    (h_mode : RepresentsRigidBoxStationaryMode setup)
    (h_law : SatisfiesInfiniteRigidBoxEnergyLaw setup)
    (h_physical : HasPhysicalRigidBoxParameters setup) :
    abs (lengthInNanometers setup.boxLength - 1) < 1 / 100 := by
  have h_units := setup.boxLength.2 UnitChoices.SI
    ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
  have h_units_val :=
    congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ)) h_units
  change lengthInNanometers setup.boxLength = _ at h_units_val
  simp [UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
    LengthUnit.scale] at h_units_val
  norm_num [LengthUnit.div_eq_val, NNReal.coe_div] at h_units_val
  change lengthInNanometers setup.boxLength =
    1000000000 * lengthInMeters setup.boxLength at h_units_val
  have h_meters : lengthInMeters setup.boxLength =
      lengthInNanometers setup.boxLength / 1000000000 := by
    linarith
  have h_n := modeNumber_eq_four setup h_figure h_mode
  have h_electronVolt :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale]
  have h_E : energyInJoules setup.stateEnergy = 6 * 1.602176634e-19 := by
    apply (div_eq_iff
      (by norm_num : (1.602176634e-19 : ℝ) ≠ 0)).mp
    simpa [energyInElectronVolts, h_electronVolt] using
      h_energy.energyIsSixElectronVolts
  have h_law' := h_law.quantizedEnergy
  rw [h_E, h_mass.electronMassKilograms, h_n] at h_law'
  norm_num [Constants.ℏ] at h_law'
  field_simp [ne_of_gt h_physical.positiveLength] at h_law'
  rw [h_meters] at h_law'
  ring_nf at h_law'
  have h_sq :
      24324736227584535021 * lengthInNanometers setup.boxLength ^ 2 =
        2471381593801514420 * Real.pi ^ 2 := by
    nlinarith [h_law']

  have h_pi_bounds :
      (311 / 100 : ℝ) < Real.pi ∧ Real.pi < (396 / 125 : ℝ) := by
    clear h_sq h_law' h_E h_electronVolt h_n h_meters h_units_val h_units
    clear h_scenario h_energy h_mass h_figure h_mode h_law h_physical setup
    have sin_lt_local : ∀ {x : ℝ}, 0 < x → Real.sin x < x := by
      intro x hx
      rcases lt_or_ge 1 x with hx_one | hx_one
      · exact (Real.sin_le_one x).trans_lt hx_one
      · have hx_abs : |x| = x := abs_of_nonneg hx.le
        have hbound := le_of_abs_le
          (Real.sin_bound (show |x| ≤ 1 by simpa [hx_abs] using hx_one))
        rw [sub_le_iff_le_add', hx_abs] at hbound
        apply hbound.trans_lt
        rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
        refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
        apply pow_le_pow_of_le_one hx.le hx_one
        simp

    have hs2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have hs2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hs2_lt : Real.sqrt 2 < (1415 / 1000 : ℝ) := by
      nlinarith
    have h_nested_sq :
        Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h_nested_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
      Real.sqrt_nonneg _
    have h_nested_lt :
        Real.sqrt (2 + Real.sqrt 2) < (1848 / 1000 : ℝ) := by
      nlinarith
    have h_rad_pos : 0 < 2 - Real.sqrt (2 + Real.sqrt 2) := by
      linarith
    have h_outer_sq :
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
          2 - Real.sqrt (2 + Real.sqrt 2) := by
      rw [Real.sq_sqrt h_rad_pos.le]
    have h_outer_nonneg :
        0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
      Real.sqrt_nonneg _
    have h_outer_lower :
        (389 / 1000 : ℝ) <
          Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
      nlinarith
    have h_pi_lower : (311 / 100 : ℝ) < Real.pi := by
      have hsin := sin_lt_local (x := Real.pi / 16) (by positivity)
      rw [Real.sin_pi_div_sixteen] at hsin
      nlinarith

    have hs2_gt : (1414 / 1000 : ℝ) < Real.sqrt 2 := by
      nlinarith
    have h_rad8_pos : 0 < 2 - Real.sqrt 2 := by
      linarith
    have h_outer8_sq :
        Real.sqrt (2 - Real.sqrt 2) ^ 2 = 2 - Real.sqrt 2 := by
      rw [Real.sq_sqrt h_rad8_pos.le]
    have h_outer8_nonneg : 0 ≤ Real.sqrt (2 - Real.sqrt 2) :=
      Real.sqrt_nonneg _
    have h_outer8_lt :
        Real.sqrt (2 - Real.sqrt 2) < (766 / 1000 : ℝ) := by
      nlinarith
    have h_sin_pi8_lt :
        Real.sin (Real.pi / 8) < (383 / 1000 : ℝ) := by
      rw [Real.sin_pi_div_eight]
      nlinarith
    have h_bound99 :=
      Real.sin_bound (x := (99 / 250 : ℝ)) (by norm_num)
    have h_sin99_gt :
        (383 / 1000 : ℝ) < Real.sin (99 / 250) := by
      rw [abs_le] at h_bound99
      norm_num [abs_of_nonneg] at h_bound99 ⊢
      linarith
    have h_pi_upper : Real.pi < (396 / 125 : ℝ) := by
      by_contra h
      have h_pi : (396 / 125 : ℝ) ≤ Real.pi := le_of_not_gt h
      have hx_le : (99 / 250 : ℝ) ≤ Real.pi / 8 := by
        nlinarith
      have hsin_le := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := (99 / 250 : ℝ)) (y := Real.pi / 8)
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) hx_le
      linarith
    exact ⟨h_pi_lower, h_pi_upper⟩
  rcases h_pi_bounds with ⟨h_pi_lower, h_pi_upper⟩

  have h_nm_pos : 0 < lengthInNanometers setup.boxLength := by
    nlinarith [h_physical.positiveLength]
  rw [abs_lt]
  constructor <;>
    nlinarith [sq_nonneg (Real.pi - 311 / 100),
      sq_nonneg (396 / 125 - Real.pi)]

/-!
At the precision shown in the problem, the box is `1.0 nm` long and answer C
is the unique matching displayed choice.

This formalizes `thm:physics:phyx_mini_0656:target`.  Neither the target
length, its tolerance, the rounded result, nor the matching answer appears in
the scenario, energy, mass, figure, mode, spectrum, or positivity premises.
-/
theorem problem_phyx_mini_0656
    (setup : RigidBoxElectronSetup)
    (h_scenario : MatchesRigidBoxElectronScenario setup)
    (h_energy : MatchesProblemEnergyReadout setup)
    (h_mass : UsesElectronMassReferenceData setup)
    (h_figure : MatchesSuppliedWaveFunctionFigure setup.figure)
    (h_mode : RepresentsRigidBoxStationaryMode setup)
    (h_law : SatisfiesInfiniteRigidBoxEnergyLaw setup)
    (h_physical : HasPhysicalRigidBoxParameters setup) :
    abs (lengthInNanometers setup.boxLength - 1) < 1 / 100 ∧
      roundedToNearestTenth (lengthInNanometers setup.boxLength) = 1 ∧
      IsUniqueMatchingDisplayedLength setup recordedDatasetAnswer := by
  have hclose := boxLength_within_one_hundredth_nanometer setup h_scenario
    h_energy h_mass h_figure h_mode h_law h_physical
  have hround :
      round (10 * lengthInNanometers setup.boxLength) = 10 := by
    apply (round_eq_iff).2
    rw [abs_lt] at hclose
    constructor <;> norm_num <;> nlinarith
  have hrounded :
      roundedToNearestTenth (lengthInNanometers setup.boxLength) = 1 := by
    norm_num [roundedToNearestTenth, hround]
  refine ⟨hclose, hrounded, ?_⟩
  constructor
  · simpa [MatchesDisplayedLength, recordedDatasetAnswer,
      displayedLengthInNanometers] using hrounded
  · intro other hother
    unfold MatchesDisplayedLength at hother
    rw [hrounded] at hother
    cases other with
    | A => norm_num [displayedLengthInNanometers] at hother
    | B => norm_num [displayedLengthInNanometers] at hother
    | C => rfl
    | D => norm_num [displayedLengthInNanometers] at hother

end PhyXMiniProblems.ProblemPhyXMini0656
