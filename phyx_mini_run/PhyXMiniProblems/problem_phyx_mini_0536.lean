import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0536

open Dimension

/-!
# Longest depicted Balmer-series wavelength

The supplied energy-level diagram represents hydrogen levels and downward
emission transitions ending at principal quantum number `n = 2`.  The physical
level energies and photon wavelengths below are unit-independent dimensional
quantities.  Real numbers occur only as calibrated electron-volt or length
readouts, counts, and displayed multiple-choice values.

The primary raster visibly contains four colored arrows: red from `n = 3`,
green from `n = 4`, blue from `n = 5`, and purple from the next unlabelled
level (`n = 6`).  This corrects the auxiliary caption, which omits the blue
arrow and assigns the purple arrow to `n = 5`.

The source's recorded choice D (`365 nm`) is inconsistent with these depicted
transitions.  The smallest depicted energy gap is the red `n = 3 → n = 2`
gap, `1.889 eV`, whose photon wavelength is between `656 nm` and `657 nm`.
Choice D is close instead to the Balmer-series limit, which is the *shortest*
series wavelength and is not one of the depicted finite-level transitions.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length, used for photon wavelength. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Coherent-SI readout of an energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Electron-volt readout grounded in Physlib's calibrated electron volt. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- Metre readout of a photon wavelength. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout used by the four displayed answers. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Ordinary Planck constant `h = 2πℏ`, read in joule-seconds. -/
def fullPlanckConstantInJouleSeconds : ℝ :=
  2 * Real.pi * Constants.ℏ.val

/-- Physlib's vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Hydrogen levels, depicted arrows, and figure vocabulary -/

/-- Hydrogen energy levels needed to describe the printed labels and arrows. -/
inductive HydrogenEnergyLevel where
  | n2
  | n3
  | n4
  | n5
  | n6
  | continuum
  deriving DecidableEq, Fintype, Repr

/-- The four downward transition arrows visibly present in the raster. -/
inductive BalmerTransition where
  | threeToTwo
  | fourToTwo
  | fiveToTwo
  | sixToTwo
  deriving DecidableEq, Fintype, Repr

/-- Initial level of each depicted Balmer transition. -/
def BalmerTransition.initialLevel : BalmerTransition → HydrogenEnergyLevel
  | .threeToTwo => .n3
  | .fourToTwo => .n4
  | .fiveToTwo => .n5
  | .sixToTwo => .n6

/-- Every depicted transition terminates in the Balmer-series level `n = 2`. -/
def BalmerTransition.finalLevel : BalmerTransition → HydrogenEnergyLevel
  | .threeToTwo | .fourToTwo | .fiveToTwo | .sixToTwo => .n2

/-- Colors of the four transition arrows, read from left to right. -/
inductive ArrowColor where
  | red
  | green
  | blue
  | purple
  deriving DecidableEq, Fintype, Repr

/-- Arrow color visibly associated with each transition. -/
def BalmerTransition.figureColor : BalmerTransition → ArrowColor
  | .threeToTwo => .red
  | .fourToTwo => .green
  | .fiveToTwo => .blue
  | .sixToTwo => .purple

/-- Printed text labels retained from the diagram. -/
inductive FigureTextLabel where
  | energyAxis
  | principalQuantumNumber
  | energyElectronVolts
  | balmerSeries
  deriving DecidableEq, Fintype, Repr

/-!
Raster-visible diagram data.  Optional scalar labels distinguish a printed
electron-volt number from a physical level energy.  The `n = 6` level is the
unlabelled horizontal line from which the purple arrow begins; three still
higher unlabelled lines are visible below the continuum line.
-/
structure BalmerEnergyLevelFigure where
  showsTextLabel : FigureTextLabel → Bool
  energyAxisPointsUpward : Bool
  showsHorizontalLevelLine : HydrogenEnergyLevel → Bool
  displayedPrincipalQuantumNumber : HydrogenEnergyLevel → Option ℕ
  displaysInfinityAtContinuum : Bool
  displayedEnergyElectronVolts : HydrogenEnergyLevel → Option ℝ
  showsTransitionArrow : BalmerTransition → Bool
  transitionArrowPointsDownward : BalmerTransition → Bool
  transitionArrowInitialLevel : BalmerTransition → HydrogenEnergyLevel
  transitionArrowFinalLevel : BalmerTransition → HydrogenEnergyLevel
  transitionArrowColor : BalmerTransition → ArrowColor
  additionalUnlabelledUpperLevelLineCount : ℕ

/-! ## Scenario, figure readouts, and governing physics -/

/-- Atomic species represented by the energy-level diagram. -/
inductive AtomicSpecies where
  | hydrogen
  | other
  deriving DecidableEq, Repr

/-- Spectral-series role of the transitions in the problem. -/
inductive SpectralSeries where
  | balmer
  | other
  deriving DecidableEq, Repr

/-!
Independent physical quantities in the problem.  In particular, each emitted
photon wavelength is an observable field, not a definition involving an
answer choice or the requested value.
-/
structure HydrogenBalmerSetup where
  atom : AtomicSpecies
  series : SpectralSeries
  levelEnergy : HydrogenEnergyLevel → DimEnergy
  emittedPhotonWavelength : BalmerTransition → LengthQuantity
  figure : BalmerEnergyLevelFigure

/-- Categorical facts explicitly stated in the prose. -/
structure MatchesHydrogenBalmerScenario (setup : HydrogenBalmerSetup) : Prop where
  atomIsHydrogen : setup.atom = .hydrogen
  seriesIsBalmer : setup.series = .balmer
  everyDepictedTransitionTerminatesAtN2 :
    ∀ transition : BalmerTransition, transition.finalLevel = .n2

/-!
Numerical labels and qualitative facts read from the primary figure.  This
contains no emitted-wavelength value, longest-transition assertion, or answer
choice.
-/
structure MatchesSuppliedBalmerFigure (setup : HydrogenBalmerSetup) : Prop where
  everyPrintedTextLabelShown :
    ∀ label, setup.figure.showsTextLabel label = true
  energyAxisUpward : setup.figure.energyAxisPointsUpward = true
  everyModelledLevelLineShown :
    ∀ level, setup.figure.showsHorizontalLevelLine level = true
  n2Label : setup.figure.displayedPrincipalQuantumNumber .n2 = some 2
  n3Label : setup.figure.displayedPrincipalQuantumNumber .n3 = some 3
  n4Label : setup.figure.displayedPrincipalQuantumNumber .n4 = some 4
  n5Label : setup.figure.displayedPrincipalQuantumNumber .n5 = some 5
  n6NumberUnlabelled :
    setup.figure.displayedPrincipalQuantumNumber .n6 = none
  continuumNumberUnlabelled :
    setup.figure.displayedPrincipalQuantumNumber .continuum = none
  infinityLabelAtContinuum :
    setup.figure.displaysInfinityAtContinuum = true
  n2EnergyLabel :
    setup.figure.displayedEnergyElectronVolts .n2 = some (-3.401)
  n3EnergyLabel :
    setup.figure.displayedEnergyElectronVolts .n3 = some (-1.512)
  n4EnergyLabel :
    setup.figure.displayedEnergyElectronVolts .n4 = some (-0.850)
  n5EnergyLabel :
    setup.figure.displayedEnergyElectronVolts .n5 = some (-0.544)
  n6EnergyUnlabelled :
    setup.figure.displayedEnergyElectronVolts .n6 = none
  continuumEnergyLabel :
    setup.figure.displayedEnergyElectronVolts .continuum = some 0.00
  physicalN2EnergyMatchesLabel :
    energyInElectronVolts (setup.levelEnergy .n2) = -3.401
  physicalN3EnergyMatchesLabel :
    energyInElectronVolts (setup.levelEnergy .n3) = -1.512
  physicalN4EnergyMatchesLabel :
    energyInElectronVolts (setup.levelEnergy .n4) = -0.850
  physicalN5EnergyMatchesLabel :
    energyInElectronVolts (setup.levelEnergy .n5) = -0.544
  physicalContinuumEnergyMatchesLabel :
    energyInElectronVolts (setup.levelEnergy .continuum) = 0.00
  everyTransitionArrowShown :
    ∀ transition, setup.figure.showsTransitionArrow transition = true
  everyTransitionArrowPointsDownward :
    ∀ transition,
      setup.figure.transitionArrowPointsDownward transition = true
  everyArrowStartsAtItsTransitionLevel :
    ∀ transition,
      setup.figure.transitionArrowInitialLevel transition =
        transition.initialLevel
  everyArrowEndsAtN2 :
    ∀ transition,
      setup.figure.transitionArrowFinalLevel transition =
        transition.finalLevel
  everyArrowHasItsVisibleColor :
    ∀ transition,
      setup.figure.transitionArrowColor transition = transition.figureColor
  threeAdditionalUpperLinesVisible :
    setup.figure.additionalUnlabelledUpperLevelLineCount = 3

/-!
Positivity and level ordering for the physical hydrogen branch.  These are
generic physical-domain conditions and contain no requested wavelength.
-/
structure HasPhysicalBalmerParameters (setup : HydrogenBalmerSetup) : Prop where
  emittedWavelengthsPositive :
    ∀ transition,
      0 < lengthInMeters (setup.emittedPhotonWavelength transition)
  n2BelowN3 :
    energyInJoules (setup.levelEnergy .n2) <
      energyInJoules (setup.levelEnergy .n3)
  n3BelowN4 :
    energyInJoules (setup.levelEnergy .n3) <
      energyInJoules (setup.levelEnergy .n4)
  n4BelowN5 :
    energyInJoules (setup.levelEnergy .n4) <
      energyInJoules (setup.levelEnergy .n5)
  n5BelowN6 :
    energyInJoules (setup.levelEnergy .n5) <
      energyInJoules (setup.levelEnergy .n6)
  n6BelowContinuum :
    energyInJoules (setup.levelEnergy .n6) <
      energyInJoules (setup.levelEnergy .continuum)

/-- Energy released by a depicted transition, read in joules. -/
def emissionEnergyGapInJoules
    (setup : HydrogenBalmerSetup) (transition : BalmerTransition) : ℝ :=
  energyInJoules (setup.levelEnergy transition.initialLevel) -
    energyInJoules (setup.levelEnergy transition.finalLevel)

/-!
Photon energy--wavelength law `ΔE λ = h c` for every depicted emission.
This governing law relates independent physical quantities uniformly; it does
not assign any transition the requested wavelength or an answer-choice value.
-/
structure SatisfiesPhotonEnergyWavelengthLaw
    (setup : HydrogenBalmerSetup) : Prop where
  gapTimesWavelengthEqualsPlanckTimesLightSpeed :
    ∀ transition : BalmerTransition,
      emissionEnergyGapInJoules setup transition *
          lengthInMeters (setup.emittedPhotonWavelength transition) =
        fullPlanckConstantInJouleSeconds *
          vacuumSpeedOfLightInMetersPerSecond

/-! ## Derived relations and multiple-choice semantics -/

/-- A transition has strictly less released energy than every other depicted arrow. -/
def IsUniqueSmallestEnergyGap
    (setup : HydrogenBalmerSetup) (transition : BalmerTransition) : Prop :=
  ∀ other, other ≠ transition →
    emissionEnergyGapInJoules setup transition <
      emissionEnergyGapInJoules setup other

/-- A transition has strictly greater wavelength than every other depicted arrow. -/
def IsUniqueLongestWavelength
    (setup : HydrogenBalmerSetup) (transition : BalmerTransition) : Prop :=
  ∀ other, other ≠ transition →
    lengthInNanometers (setup.emittedPhotonWavelength other) <
      lengthInNanometers (setup.emittedPhotonWavelength transition)

/-- The `n = 3 → n = 2` arrow has the unique smallest depicted energy drop. -/
lemma threeToTwo_has_unique_smallest_energyGap
    (setup : HydrogenBalmerSetup)
    (_figure : MatchesSuppliedBalmerFigure setup)
    (_physical : HasPhysicalBalmerParameters setup) :
    IsUniqueSmallestEnergyGap setup .threeToTwo := by
  unfold IsUniqueSmallestEnergyGap
  intro other hne
  cases other <;>
    simp_all [emissionEnergyGapInJoules, BalmerTransition.initialLevel,
      BalmerTransition.finalLevel]
  all_goals
    linarith [_physical.n3BelowN4, _physical.n4BelowN5,
      _physical.n5BelowN6]

/-- The photon law solved for the wavelength of any depicted transition. -/
lemma photonWavelengthInMeters_eq_planckTimesLightSpeed_div_energyGap
    (setup : HydrogenBalmerSetup)
    (_physical : HasPhysicalBalmerParameters setup)
    (_law : SatisfiesPhotonEnergyWavelengthLaw setup)
    (transition : BalmerTransition) :
    lengthInMeters (setup.emittedPhotonWavelength transition) =
      fullPlanckConstantInJouleSeconds *
          vacuumSpeedOfLightInMetersPerSecond /
        emissionEnergyGapInJoules setup transition := by
  have hgap : 0 < emissionEnergyGapInJoules setup transition := by
    cases transition <;>
      simp [emissionEnergyGapInJoules, BalmerTransition.initialLevel,
        BalmerTransition.finalLevel]
    · exact _physical.n2BelowN3
    · linarith [_physical.n2BelowN3, _physical.n3BelowN4]
    · linarith [_physical.n2BelowN3, _physical.n3BelowN4,
        _physical.n4BelowN5]
    · linarith [_physical.n2BelowN3, _physical.n3BelowN4,
        _physical.n4BelowN5, _physical.n5BelowN6]
  apply (eq_div_iff (ne_of_gt hgap)).2
  rw [mul_comm]
  exact _law.gapTimesWavelengthEqualsPlanckTimesLightSpeed transition

/-- The smallest depicted energy drop therefore emits the longest-wavelength photon. -/
lemma threeToTwo_is_unique_longest_depicted_wavelength
    (setup : HydrogenBalmerSetup)
    (_figure : MatchesSuppliedBalmerFigure setup)
    (_physical : HasPhysicalBalmerParameters setup)
    (_law : SatisfiesPhotonEnergyWavelengthLaw setup) :
    IsUniqueLongestWavelength setup .threeToTwo := by
  have hnano_scale (length : LengthQuantity) :
      lengthInNanometers length =
        1000000000 * lengthInMeters length := by
    have h := length.property
      UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
    have hv :=
      congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    simp only [lengthInNanometers, lengthInMeters, lengthReadout] at hv ⊢
    rw [hv]
    change
      ((UnitChoices.SI.dimScale
        ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
        L𝓭 : NNReal) : ℝ) * _ = _
    congr 1
    norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.toReal]
  unfold IsUniqueLongestWavelength
  intro other hne
  have hgap_three :
      0 < emissionEnergyGapInJoules setup .threeToTwo := by
    simpa [emissionEnergyGapInJoules, BalmerTransition.initialLevel,
      BalmerTransition.finalLevel] using _physical.n2BelowN3
  have hsmall := threeToTwo_has_unique_smallest_energyGap
    setup _figure _physical other hne
  have hother_pos := _physical.emittedWavelengthsPositive other
  have hlaw_three :=
    _law.gapTimesWavelengthEqualsPlanckTimesLightSpeed .threeToTwo
  have hlaw_other :=
    _law.gapTimesWavelengthEqualsPlanckTimesLightSpeed other
  have hproduct :
      0 < (emissionEnergyGapInJoules setup other -
        emissionEnergyGapInJoules setup .threeToTwo) *
        lengthInMeters (setup.emittedPhotonWavelength other) :=
    mul_pos (sub_pos.mpr hsmall) hother_pos
  have hmeters :
      lengthInMeters (setup.emittedPhotonWavelength other) <
        lengthInMeters
          (setup.emittedPhotonWavelength .threeToTwo) := by
    nlinarith
  rw [hnano_scale, hnano_scale]
  nlinarith

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Wavelength printed beside each answer label, in nanometres. -/
def AnswerChoice.wavelengthNanometers : AnswerChoice → ℝ
  | .A => 338
  | .B => 197
  | .C => 274
  | .D => 365

/-- Dataset metadata records answer D; this inconsistent value is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A depicted photon has exactly the whole-nanometre wavelength printed by a choice. -/
def MatchesDisplayedWavelength
    (setup : HydrogenBalmerSetup)
    (transition : BalmerTransition)
    (choice : AnswerChoice) : Prop :=
  lengthInNanometers (setup.emittedPhotonWavelength transition) =
    choice.wavelengthNanometers

/-!
Among the depicted Balmer transitions, the `n = 3 → n = 2` photon has the
longest wavelength.  Its wavelength lies strictly between `656 nm` and
`657 nm`, so none of the supplied choices matches.  The inconsistent recorded
choice D is retained only by `recordedDatasetAnswer` as source metadata.

Blueprint: `thm:physics:phyx_mini_0536:target`.
-/
theorem longestDepictedBalmerWavelength_is_between_656_and_657_nanometers
    (setup : HydrogenBalmerSetup)
    (_scenario : MatchesHydrogenBalmerScenario setup)
    (_figure : MatchesSuppliedBalmerFigure setup)
    (_physical : HasPhysicalBalmerParameters setup)
    (_law : SatisfiesPhotonEnergyWavelengthLaw setup) :
    IsUniqueLongestWavelength setup .threeToTwo ∧
      656 < lengthInNanometers
          (setup.emittedPhotonWavelength .threeToTwo) ∧
      lengthInNanometers
          (setup.emittedPhotonWavelength .threeToTwo) < 657 ∧
      ∀ choice : AnswerChoice,
        ¬ MatchesDisplayedWavelength setup .threeToTwo choice := by
  have hev :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hn2 := _figure.physicalN2EnergyMatchesLabel
  have hn3 := _figure.physicalN3EnergyMatchesLabel
  rw [energyInElectronVolts, hev] at hn2 hn3
  have hgap :
      emissionEnergyGapInJoules setup .threeToTwo =
        1.889 * 1.602176634e-19 := by
    simp only [emissionEnergyGapInJoules,
      BalmerTransition.initialLevel, BalmerTransition.finalLevel]
    field_simp at hn2 hn3
    nlinarith
  have hc :
      fullPlanckConstantInJouleSeconds *
          vacuumSpeedOfLightInMetersPerSecond =
        (2 * Real.pi * 1.054571817e-34) * 299792458 := by
    norm_num [fullPlanckConstantInJouleSeconds,
      vacuumSpeedOfLightInMetersPerSecond, Constants.ℏ,
      DimSpeed.speedOfLight_in_SI]
  have hnano_scale (length : LengthQuantity) :
      lengthInNanometers length =
        1000000000 * lengthInMeters length := by
    have h := length.property
      UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
    have hv :=
      congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    simp only [lengthInNanometers, lengthInMeters, lengthReadout] at hv ⊢
    rw [hv]
    change
      ((UnitChoices.SI.dimScale
        ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
        L𝓭 : NNReal) : ℝ) * _ = _
    congr 1
    norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.toReal]
  have hlaw :=
    _law.gapTimesWavelengthEqualsPlanckTimesLightSpeed .threeToTwo
  rw [hgap, hc] at hlaw
  have hnano :=
    hnano_scale (setup.emittedPhotonWavelength .threeToTwo)
  have hlower :
      656 < lengthInNanometers
        (setup.emittedPhotonWavelength .threeToTwo) := by
    nlinarith [Real.pi_gt_d20]
  have hupper :
      lengthInNanometers
        (setup.emittedPhotonWavelength .threeToTwo) < 657 := by
    nlinarith [Real.pi_lt_d20]
  refine ⟨threeToTwo_is_unique_longest_depicted_wavelength
    setup _figure _physical _law, hlower, hupper, ?_⟩
  intro choice hmatch
  cases choice <;>
    simp [MatchesDisplayedWavelength,
      AnswerChoice.wavelengthNanometers] at hmatch <;>
    linarith

end PhyXMiniProblems.ProblemPhyXMini0536
