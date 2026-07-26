import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0518

/-!
# Searsium transition photons and the maximum metal work function

The primary figure gives four potential-energy levels for the hypothetical
one-electron element Searsium.  Energies and the metal work function remain
dimensionful `DimEnergy` quantities.  Real numbers below are used only for
explicit readouts in electron volts and for the printed answer choices.
-/

/-! ## Dimensionful energies and electron-volt readouts -/

/-- Read a dimensionful energy as a signed number of electron volts. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.electronVolt UnitChoices.SI).val

/-! ## Atomic levels, transitions, photons, and the test metal -/

/-- The four Searsium levels labelled in the supplied energy-level diagram. -/
inductive SearsiumEnergyLevel where
  | n1
  | n2
  | n3
  | n4
  deriving DecidableEq, Fintype, Repr

/-- The principal quantum number printed beside a Searsium level. -/
def principalQuantumNumber : SearsiumEnergyLevel → ℕ
  | .n1 => 1
  | .n2 => 2
  | .n3 => 3
  | .n4 => 4

/-- The three downward transitions discussed in the question. -/
inductive SearsiumTransition where
  | n4ToN3
  | n3ToN2
  | n3ToN1
  deriving DecidableEq, Fintype, Repr

/-- Initial level of a transition named in the question. -/
def transitionInitialLevel : SearsiumTransition → SearsiumEnergyLevel
  | .n4ToN3 => .n4
  | .n3ToN2 => .n3
  | .n3ToN1 => .n3

/-- Final level of a transition named in the question. -/
def transitionFinalLevel : SearsiumTransition → SearsiumEnergyLevel
  | .n4ToN3 => .n3
  | .n3ToN2 => .n2
  | .n3ToN1 => .n1

/-- A photon emitted by one of the named Searsium transitions. -/
structure SearsiumPhoton where
  sourceTransition : SearsiumTransition
  energy : DimEnergy

/-- Electron-volt readout of an emitted photon's energy. -/
def photonEnergyInElectronVolts (photon : SearsiumPhoton) : ℝ :=
  energyInElectronVolts photon.energy

/-- The unknown metal sample, carrying its independent physical work function. -/
structure MetalSample where
  workFunction : DimEnergy

/-- Electron-volt readout of a metal sample's work function. -/
def workFunctionInElectronVolts (metal : MetalSample) : ℝ :=
  energyInElectronVolts metal.workFunction

/-! ## Figure geometry and physical setup -/

/-- Orientation of an energy-level line in the primary figure. -/
inductive FigureLineOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Color of the electron marker drawn on the ground-state level. -/
inductive FigureMarkerColor where
  | red
  | other
  deriving DecidableEq, Repr

/-- The physical element represented by the level scheme. -/
inductive ElementIdentity where
  | searsium
  | other
  deriving DecidableEq, Repr

/-- Literal labels and geometry transcribed from the supplied raster. -/
structure SearsiumEnergyLevelFigure where
  printedPrincipalQuantumNumber : SearsiumEnergyLevel → ℕ
  printedEnergyInElectronVolts : SearsiumEnergyLevel → ℝ
  lineOrientation : SearsiumEnergyLevel → FigureLineOrientation
  verticalOrderBottomToTop : List SearsiumEnergyLevel
  energyLevelLinesAreParallel : Bool
  markedElectronLevel : SearsiumEnergyLevel
  electronMarkerColor : FigureMarkerColor

/-!
The Searsium/metal experiment.  The level energies, emitted photons, and
metal work function are independent physical data; their relations are
imposed only by the governing laws below.
-/
structure SearsiumPhotoelectricSetup where
  element : ElementIdentity
  boundElectronCount : ℕ
  potentialEnergyAtInfiniteSeparation : DimEnergy
  levelPotentialEnergy : SearsiumEnergyLevel → DimEnergy
  emittedPhotonFrom : SearsiumTransition → SearsiumPhoton
  testMetal : MetalSample
  photoelectronsEjectedBy : SearsiumPhoton → Prop
  figure : SearsiumEnergyLevelFigure

/-! ## Scenario, figure evidence, observations, and governing laws -/

/-- The prose identifies Searsium as a hypothetical one-electron element. -/
structure MatchesSearsiumScenario
    (setup : SearsiumPhotoelectricSetup) : Prop where
  elementIsSearsium : setup.element = .searsium
  exactlyOneBoundElectron : setup.boundElectronCount = 1

/-!
Data read directly from the prose and primary figure: the zero of potential
energy, four quantum-number and energy labels, horizontal parallel lines,
their vertical order, and the red electron marker on `n = 1`.

No work-function maximum or answer choice occurs in this structure.
-/
structure MatchesProblemAndFigureReadouts
    (setup : SearsiumPhotoelectricSetup) : Prop where
  zeroPotentialEnergyAtInfinity :
    energyInElectronVolts setup.potentialEnergyAtInfiniteSeparation = 0
  n1Label : setup.figure.printedPrincipalQuantumNumber .n1 = 1
  n2Label : setup.figure.printedPrincipalQuantumNumber .n2 = 2
  n3Label : setup.figure.printedPrincipalQuantumNumber .n3 = 3
  n4Label : setup.figure.printedPrincipalQuantumNumber .n4 = 4
  n1EnergyLabel : setup.figure.printedEnergyInElectronVolts .n1 = -20
  n2EnergyLabel : setup.figure.printedEnergyInElectronVolts .n2 = -10
  n3EnergyLabel : setup.figure.printedEnergyInElectronVolts .n3 = -5
  n4EnergyLabel : setup.figure.printedEnergyInElectronVolts .n4 = -2
  diagramRepresentsLevelPotentialEnergies : ∀ level,
    energyInElectronVolts (setup.levelPotentialEnergy level) =
      setup.figure.printedEnergyInElectronVolts level
  everyLevelLineIsHorizontal : ∀ level,
    setup.figure.lineOrientation level = .horizontal
  levelLinesAreParallel : setup.figure.energyLevelLinesAreParallel = true
  displayedVerticalOrder :
    setup.figure.verticalOrderBottomToTop = [.n1, .n2, .n3, .n4]
  electronMarkerIsOnGroundState : setup.figure.markedElectronLevel = .n1
  electronMarkerIsRed : setup.figure.electronMarkerColor = .red

/-- The three emission/non-emission observations stated in the question. -/
structure MatchesPhotoelectronEjectionObservations
    (setup : SearsiumPhotoelectricSetup) : Prop where
  n3ToN2EjectsPhotoelectrons :
    setup.photoelectronsEjectedBy (setup.emittedPhotonFrom .n3ToN2)
  n3ToN1EjectsPhotoelectrons :
    setup.photoelectronsEjectedBy (setup.emittedPhotonFrom .n3ToN1)
  n4ToN3DoesNotEjectPhotoelectrons :
    ¬ setup.photoelectronsEjectedBy (setup.emittedPhotonFrom .n4ToN3)

/-- A physical work function is nonnegative. -/
structure HasPhysicalMetalParameters
    (setup : SearsiumPhotoelectricSetup) : Prop where
  workFunctionNonnegative :
    0 ≤ workFunctionInElectronVolts setup.testMetal

/-!
The two governing laws used by the problem:

* an emitted photon's energy is the initial level energy minus the final
  level energy;
* a photon ejects photoelectrons exactly when its energy reaches or exceeds
  the metal's work function.

Both are uniform over the named transitions and contain no numerical maximum.
-/
structure SatisfiesTransitionAndPhotoelectricLaws
    (setup : SearsiumPhotoelectricSetup) : Prop where
  emittedPhotonHasNamedSource : ∀ transition,
    (setup.emittedPhotonFrom transition).sourceTransition = transition
  photonEnergyIsLevelEnergyDifference : ∀ transition,
    photonEnergyInElectronVolts (setup.emittedPhotonFrom transition) =
      energyInElectronVolts
          (setup.levelPotentialEnergy (transitionInitialLevel transition)) -
        energyInElectronVolts
          (setup.levelPotentialEnergy (transitionFinalLevel transition))
  photoelectricThresholdLaw : ∀ transition,
    setup.photoelectronsEjectedBy (setup.emittedPhotonFrom transition) ↔
      workFunctionInElectronVolts setup.testMetal ≤
        photonEnergyInElectronVolts (setup.emittedPhotonFrom transition)

/-! ## Consistent work functions and displayed choices -/

/-!
The set of nonnegative work-function readouts whose threshold behavior agrees
with all three observed photons.  This definition encodes no numerical answer;
its greatest element must be derived from the level diagram and transition law.
-/
def consistentWorkFunctionReadoutsInElectronVolts
    (setup : SearsiumPhotoelectricSetup) : Set ℝ :=
  {candidate | 0 ≤ candidate ∧
    ∀ transition,
      setup.photoelectronsEjectedBy (setup.emittedPhotonFrom transition) ↔
        candidate ≤
          photonEnergyInElectronVolts (setup.emittedPhotonFrom transition)}

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Work-function readout printed beside each answer label, in electron volts. -/
def displayedWorkFunctionInElectronVolts : AnswerChoice → ℝ
  | .A => 7
  | .B => 4
  | .C => 3
  | .D => 5

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A choice displays the greatest work-function readout consistent with the data. -/
def MatchesMaximumConsistentWorkFunctionChoice
    (setup : SearsiumPhotoelectricSetup) (choice : AnswerChoice) : Prop :=
  IsGreatest (consistentWorkFunctionReadoutsInElectronVolts setup)
    (displayedWorkFunctionInElectronVolts choice)

/-- A choice is the unique displayed maximum consistent with the experiment. -/
def IsUniqueMatchingMaximumWorkFunctionChoice
    (setup : SearsiumPhotoelectricSetup) (choice : AnswerChoice) : Prop :=
  MatchesMaximumConsistentWorkFunctionChoice setup choice ∧
    ∀ other : AnswerChoice,
      MatchesMaximumConsistentWorkFunctionChoice setup other → other = choice

/-!
The actual metal work function is one of the candidates consistent with the
observed threshold pattern.  This is a consequence of the general
photoelectric law, not a premise identifying the maximum.
-/
lemma actual_workFunctionReadout_is_consistent
    (setup : SearsiumPhotoelectricSetup)
    (hPhysical : HasPhysicalMetalParameters setup)
    (hLaws : SatisfiesTransitionAndPhotoelectricLaws setup) :
    workFunctionInElectronVolts setup.testMetal ∈
      consistentWorkFunctionReadoutsInElectronVolts setup := by
  refine ⟨hPhysical.workFunctionNonnegative, ?_⟩
  intro transition
  exact hLaws.photoelectricThresholdLaw transition

/-!
The transition energies are `3 eV`, `5 eV`, and `15 eV`.  The observed
threshold pattern therefore permits work functions above `3 eV` and at most
`5 eV`, so `5 eV` is the greatest consistent readout.
-/
lemma five_is_greatest_consistent_workFunctionReadout
    (setup : SearsiumPhotoelectricSetup)
    (hFigure : MatchesProblemAndFigureReadouts setup)
    (hObservations : MatchesPhotoelectronEjectionObservations setup)
    (hLaws : SatisfiesTransitionAndPhotoelectricLaws setup) :
    IsGreatest (consistentWorkFunctionReadoutsInElectronVolts setup) 5 := by
  have hPhotonN4ToN3 :
      photonEnergyInElectronVolts
          (setup.emittedPhotonFrom .n4ToN3) = 3 := by
    calc
      photonEnergyInElectronVolts
          (setup.emittedPhotonFrom .n4ToN3) =
          energyInElectronVolts (setup.levelPotentialEnergy .n4) -
            energyInElectronVolts (setup.levelPotentialEnergy .n3) := by
              simpa [transitionInitialLevel, transitionFinalLevel] using
                hLaws.photonEnergyIsLevelEnergyDifference .n4ToN3
      _ = setup.figure.printedEnergyInElectronVolts .n4 -
            setup.figure.printedEnergyInElectronVolts .n3 := by
              rw [hFigure.diagramRepresentsLevelPotentialEnergies .n4,
                hFigure.diagramRepresentsLevelPotentialEnergies .n3]
      _ = 3 := by
              rw [hFigure.n4EnergyLabel, hFigure.n3EnergyLabel]
              norm_num
  have hPhotonN3ToN2 :
      photonEnergyInElectronVolts
          (setup.emittedPhotonFrom .n3ToN2) = 5 := by
    calc
      photonEnergyInElectronVolts
          (setup.emittedPhotonFrom .n3ToN2) =
          energyInElectronVolts (setup.levelPotentialEnergy .n3) -
            energyInElectronVolts (setup.levelPotentialEnergy .n2) := by
              simpa [transitionInitialLevel, transitionFinalLevel] using
                hLaws.photonEnergyIsLevelEnergyDifference .n3ToN2
      _ = setup.figure.printedEnergyInElectronVolts .n3 -
            setup.figure.printedEnergyInElectronVolts .n2 := by
              rw [hFigure.diagramRepresentsLevelPotentialEnergies .n3,
                hFigure.diagramRepresentsLevelPotentialEnergies .n2]
      _ = 5 := by
              rw [hFigure.n3EnergyLabel, hFigure.n2EnergyLabel]
              norm_num
  have hPhotonN3ToN1 :
      photonEnergyInElectronVolts
          (setup.emittedPhotonFrom .n3ToN1) = 15 := by
    calc
      photonEnergyInElectronVolts
          (setup.emittedPhotonFrom .n3ToN1) =
          energyInElectronVolts (setup.levelPotentialEnergy .n3) -
            energyInElectronVolts (setup.levelPotentialEnergy .n1) := by
              simpa [transitionInitialLevel, transitionFinalLevel] using
                hLaws.photonEnergyIsLevelEnergyDifference .n3ToN1
      _ = setup.figure.printedEnergyInElectronVolts .n3 -
            setup.figure.printedEnergyInElectronVolts .n1 := by
              rw [hFigure.diagramRepresentsLevelPotentialEnergies .n3,
                hFigure.diagramRepresentsLevelPotentialEnergies .n1]
      _ = 15 := by
              rw [hFigure.n3EnergyLabel, hFigure.n1EnergyLabel]
              norm_num
  constructor
  · refine ⟨by norm_num, ?_⟩
    intro transition
    cases transition with
    | n4ToN3 =>
        constructor
        · intro hEjects
          exact (hObservations.n4ToN3DoesNotEjectPhotoelectrons hEjects).elim
        · intro hFiveLe
          rw [hPhotonN4ToN3] at hFiveLe
          norm_num at hFiveLe
    | n3ToN2 =>
        rw [hPhotonN3ToN2]
        simp only [hObservations.n3ToN2EjectsPhotoelectrons]
        norm_num
    | n3ToN1 =>
        rw [hPhotonN3ToN1]
        simp only [hObservations.n3ToN1EjectsPhotoelectrons]
        norm_num
  · intro candidate hCandidate
    have hCandidateLe :=
      (hCandidate.2 .n3ToN2).mp
        hObservations.n3ToN2EjectsPhotoelectrons
    rwa [hPhotonN3ToN2] at hCandidateLe

/-!
The unknown metal's actual work function is at most `5 eV`, and `5 eV` is the
greatest work function compatible with all three transition observations.
It uniquely selects displayed answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0518:target`.
-/
theorem problem_phyx_mini_0518
    (setup : SearsiumPhotoelectricSetup)
    (hScenario : MatchesSearsiumScenario setup)
    (hFigure : MatchesProblemAndFigureReadouts setup)
    (hObservations : MatchesPhotoelectronEjectionObservations setup)
    (hPhysical : HasPhysicalMetalParameters setup)
    (hLaws : SatisfiesTransitionAndPhotoelectricLaws setup) :
    workFunctionInElectronVolts setup.testMetal ≤ 5 ∧
      IsGreatest (consistentWorkFunctionReadoutsInElectronVolts setup) 5 ∧
      IsUniqueMatchingMaximumWorkFunctionChoice setup recordedDatasetAnswer := by
  have hGreatest :=
    five_is_greatest_consistent_workFunctionReadout
      setup hFigure hObservations hLaws
  refine ⟨hGreatest.2 (actual_workFunctionReadout_is_consistent
    setup hPhysical hLaws), hGreatest, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [MatchesMaximumConsistentWorkFunctionChoice,
      recordedDatasetAnswer, displayedWorkFunctionInElectronVolts] using
        hGreatest
  · intro other hOther
    cases other with
    | A =>
        change IsGreatest
          (consistentWorkFunctionReadoutsInElectronVolts setup) 7 at hOther
        have hImpossible : (7 : ℝ) ≤ 5 := hGreatest.2 hOther.1
        norm_num at hImpossible
    | B =>
        change IsGreatest
          (consistentWorkFunctionReadoutsInElectronVolts setup) 4 at hOther
        have hImpossible : (5 : ℝ) ≤ 4 := hOther.2 hGreatest.1
        norm_num at hImpossible
    | C =>
        change IsGreatest
          (consistentWorkFunctionReadoutsInElectronVolts setup) 3 at hOther
        have hImpossible : (5 : ℝ) ≤ 3 := hOther.2 hGreatest.1
        norm_num at hImpossible
    | D =>
        rfl

end PhyXMiniProblems.ProblemPhyXMini0518
