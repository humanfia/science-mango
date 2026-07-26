import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0585

open Dimension

/-!
# Minimum photon energy for capture in a finite potential trap

An electron approaches a finite electrostatic trap through a thin tube.  It
starts in the `V₁ = -9 V` region with kinetic energy `2 eV` and enters the
`V₂ = 0 V` trap.  The trap has bound levels `E₁ = 1 eV`, `E₂ = 2 eV`, and
`E₃ = 4 eV`; its nonquantized continuum begins at the `E₄ = 9 eV` marker.
Capture at a bound level occurs by emission of one photon.

Physical energies and electric potentials below are unit-independent
dimensionful quantities.  Real numbers occur only at named joule,
electron-volt, and volt readout boundaries and in the printed answer choices.

Assumption/target split:

* `MatchesFinitePotentialTrapScenario` records the thin finite tube, electron,
  rightward motion, region ordering, and one-photon capture mechanism;
* `MatchesProblemReadouts` records `V₁`, `V₂`, the incident kinetic energy,
  the three bound energies, and the continuum threshold;
* `MatchesSuppliedEnergyLevelFigure` records the literal features visible in
  image 585, without asserting a photon energy;
* `SatisfiesElectronEntryAndCaptureLaws` states the electron's energy gain
  from the potential difference and single-photon energy conservation; and
* leastness, the value `7 eV`, and agreement with answer C occur only in lemma
  or theorem conclusions.
-/

/-! ## Dimensionful quantities and calibrated scalar readouts -/

/-- Electric potential has dimension energy divided by electric charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent physical electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- Read a physical energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Read a physical energy in electron volts.  The calibration is Physlib's
dimensionful constant `DimEnergy.electronVolt`, not a scalar alias for energy.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a physical electric potential in coherent-SI volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Apparatus, states, and labels -/

/-- The two constant-potential regions named in the prose. -/
inductive TubeRegion where
  | incidentRegion
  | trapRegion
  deriving DecidableEq, Fintype, Repr

/-- Particle species relevant to the incident-beam description. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Fintype, Repr

/-- Direction of motion along the thin tube. -/
inductive TubeDirection where
  | rightward
  | leftward
  deriving DecidableEq, Fintype, Repr

/-- Physical mechanism by which the electron loses energy and is captured. -/
inductive CaptureMechanism where
  | singlePhotonEmission
  | other
  deriving DecidableEq, Fintype, Repr

/-!
The four labels printed beside the horizontal lines in the supplied diagram.
`E₄` is the continuum boundary marker rather than an additional bound state.
-/
inductive TrapEnergyMarker where
  | E1
  | E2
  | E3
  | E4
  deriving DecidableEq, Fintype, Repr

/-- The three final levels at which the electron is genuinely trapped. -/
inductive BoundTrapLevel where
  | E1
  | E2
  | E3
  deriving DecidableEq, Fintype, Repr

/-- Regard a bound-state label as its marker in the four-line diagram. -/
def BoundTrapLevel.toEnergyMarker : BoundTrapLevel → TrapEnergyMarker
  | .E1 => .E1
  | .E2 => .E2
  | .E3 => .E3

/-- Spectral character of an energy range in the finite trap. -/
inductive SpectrumKind where
  | discreteBound
  | nonquantizedContinuum
  deriving DecidableEq, Fintype, Repr

/-! ## Primary-figure vocabulary -/

/-!
Literal visual information transcribed from `phyx_data/test_image/585.png`.
The image itself displays labels and geometry, while the numerical level
readouts are supplied by the prose and live in `MatchesProblemReadouts`.
-/
structure TrapEnergyLevelFigure where
  energyAxisVisible : Bool
  zeroPointVisible : Bool
  levelLineVisible : TrapEnergyMarker → Bool
  levelLineHorizontal : TrapEnergyMarker → Bool
  levelLineLightBlue : TrapEnergyMarker → Bool
  levelLabelVisible : TrapEnergyMarker → Bool
  nonquantizedRegionVisible : Bool
  nonquantizedRegionShaded : Bool
  nonquantizedLabelVisible : Bool
  continuumBoundaryMarker : TrapEnergyMarker
  continuumShadingFadesUpward : Bool

/-!
Independent physical observables in the potential-trap experiment.  In
particular, neither `electronEnergyUponEnteringTrap` nor any emitted photon
energy is defined from a numerical answer; both are constrained only by the
governing laws below.
-/
structure ElectronFiniteTrapSetup where
  tubeIsThin : Bool
  trapIsFinite : Bool
  incidentParticle : ParticleSpecies
  incidentDirection : TubeDirection
  initialRegion : TubeRegion
  destinationRegion : TubeRegion
  captureMechanism : CaptureMechanism
  electricPotentialAt : TubeRegion → ElectricPotentialQuantity
  incidentKineticEnergy : DimEnergy
  electronEnergyUponEnteringTrap : DimEnergy
  energyAtMarker : TrapEnergyMarker → DimEnergy
  spectrumKindAtMarker : TrapEnergyMarker → SpectrumKind
  emittedPhotonEnergyForCaptureAt : BoundTrapLevel → DimEnergy
  figure : TrapEnergyLevelFigure

/-! ## Scenario, data, and governing laws -/

/-- Qualitative apparatus and particle roles stated in the problem. -/
structure MatchesFinitePotentialTrapScenario
    (setup : ElectronFiniteTrapSetup) : Prop where
  tubeIsThin : setup.tubeIsThin = true
  potentialTrapIsFinite : setup.trapIsFinite = true
  incidentParticleIsElectron : setup.incidentParticle = .electron
  electronMovesRightward : setup.incidentDirection = .rightward
  electronStartsInIncidentRegion : setup.initialRegion = .incidentRegion
  electronEntersTrapRegion : setup.destinationRegion = .trapRegion
  captureOccursByOnePhotonEmission :
    setup.captureMechanism = .singlePhotonEmission
  threeLowerLevelsAreDiscreteAndBound : ∀ level : BoundTrapLevel,
    setup.spectrumKindAtMarker
        (BoundTrapLevel.toEnergyMarker level) = .discreteBound
  E4MarksTheNonquantizedContinuum :
    setup.spectrumKindAtMarker .E4 = .nonquantizedContinuum

/-!
Numerical readouts supplied in the prose.  These are calibrated measurements
of physical quantities and contain no emitted-photon energy or minimizer.
-/
structure MatchesProblemReadouts
    (setup : ElectronFiniteTrapSetup) : Prop where
  incidentRegionPotentialIsMinusNineVolts :
    electricPotentialInVolts
        (setup.electricPotentialAt .incidentRegion) = -9
  trapRegionPotentialIsZeroVolts :
    electricPotentialInVolts
        (setup.electricPotentialAt .trapRegion) = 0
  incidentKineticEnergyIsTwoElectronVolts :
    energyInElectronVolts setup.incidentKineticEnergy = 2
  levelE1IsOneElectronVolt :
    energyInElectronVolts (setup.energyAtMarker .E1) = 1
  levelE2IsTwoElectronVolts :
    energyInElectronVolts (setup.energyAtMarker .E2) = 2
  levelE3IsFourElectronVolts :
    energyInElectronVolts (setup.energyAtMarker .E3) = 4
  continuumThresholdE4IsNineElectronVolts :
    energyInElectronVolts (setup.energyAtMarker .E4) = 9

/-!
All unambiguous primary-image evidence: an energy axis and zero, four labeled
horizontal light-blue lines, and a shaded nonquantized region beginning at
the `E₄` marker and fading upward.
-/
structure MatchesSuppliedEnergyLevelFigure
    (setup : ElectronFiniteTrapSetup) : Prop where
  energyAxisShown : setup.figure.energyAxisVisible = true
  zeroPointShown : setup.figure.zeroPointVisible = true
  everyLevelLineShown :
    ∀ marker, setup.figure.levelLineVisible marker = true
  everyLevelLineHorizontal :
    ∀ marker, setup.figure.levelLineHorizontal marker = true
  everyLevelLineLightBlue :
    ∀ marker, setup.figure.levelLineLightBlue marker = true
  everyLevelLabelShown :
    ∀ marker, setup.figure.levelLabelVisible marker = true
  nonquantizedRegionShown :
    setup.figure.nonquantizedRegionVisible = true
  nonquantizedRegionIsShaded :
    setup.figure.nonquantizedRegionShaded = true
  nonquantizedLabelShown :
    setup.figure.nonquantizedLabelVisible = true
  continuumBeginsAtE4 :
    setup.figure.continuumBoundaryMarker = .E4
  continuumShadingFadesUpward :
    setup.figure.continuumShadingFadesUpward = true

/-!
Sign and ordering conditions for a physical finite trap.  These conditions
exclude negative photon energies but do not select a minimizing level or give
the requested `7 eV` value.
-/
structure HasPhysicalFiniteTrapParameters
    (setup : ElectronFiniteTrapSetup) : Prop where
  incidentKineticEnergyPositive :
    0 < energyInElectronVolts setup.incidentKineticEnergy
  entryEnergyPositive :
    0 < energyInElectronVolts setup.electronEnergyUponEnteringTrap
  everyCapturePhotonEnergyPositive :
    ∀ level,
      0 < energyInElectronVolts
        (setup.emittedPhotonEnergyForCaptureAt level)
  E1BelowE2 :
    energyInElectronVolts (setup.energyAtMarker .E1) <
      energyInElectronVolts (setup.energyAtMarker .E2)
  E2BelowE3 :
    energyInElectronVolts (setup.energyAtMarker .E2) <
      energyInElectronVolts (setup.energyAtMarker .E3)
  everyBoundLevelBelowContinuum :
    ∀ level : BoundTrapLevel,
      energyInElectronVolts
          (setup.energyAtMarker
            (BoundTrapLevel.toEnergyMarker level)) <
        energyInElectronVolts (setup.energyAtMarker .E4)

/-!
The governing laws used by the calculation.

For an electron, a rise of `ΔV` volts in electrostatic potential lowers its
potential energy by `ΔV` electron volts, so the same amount is added to its
energy upon entering the trap.  Single-photon capture then conserves energy:
the entry energy is the sum of the final bound energy and emitted photon
energy.  Neither law specializes the result to `11 eV`, `7 eV`, or `E₃`.
-/
structure SatisfiesElectronEntryAndCaptureLaws
    (setup : ElectronFiniteTrapSetup) : Prop where
  electronEntryEnergyFromPotentialDifference :
    energyInElectronVolts setup.electronEnergyUponEnteringTrap =
      energyInElectronVolts setup.incidentKineticEnergy +
        (electricPotentialInVolts
            (setup.electricPotentialAt .trapRegion) -
          electricPotentialInVolts
            (setup.electricPotentialAt .incidentRegion))
  singlePhotonCaptureEnergyConservation : ∀ level : BoundTrapLevel,
    energyInElectronVolts setup.electronEnergyUponEnteringTrap =
      energyInElectronVolts
          (setup.energyAtMarker
            (BoundTrapLevel.toEnergyMarker level)) +
        energyInElectronVolts
          (setup.emittedPhotonEnergyForCaptureAt level)

/-! ## Minimum-energy semantics and derived physical relations -/

/-!
An energy is realizable and no larger than the photon emitted for capture at
any of the three bound levels.  This predicate does not define an energy by a
closed-form answer; it compares the independent photon observables in the
setup.
-/
def IsLeastCapturePhotonEnergy
    (setup : ElectronFiniteTrapSetup) (photonEnergy : DimEnergy) : Prop :=
  (∃ level,
      photonEnergy = setup.emittedPhotonEnergyForCaptureAt level) ∧
    ∀ level,
      energyInElectronVolts photonEnergy ≤
        energyInElectronVolts
          (setup.emittedPhotonEnergyForCaptureAt level)

/-- The electron reaches the trap with `11 eV` available for capture. -/
lemma electronEnergyUponEnteringTrap_is_eleven_electronVolts
    (setup : ElectronFiniteTrapSetup)
    (_scenario : MatchesFinitePotentialTrapScenario setup)
    (data : MatchesProblemReadouts setup)
    (laws : SatisfiesElectronEntryAndCaptureLaws setup) :
    energyInElectronVolts setup.electronEnergyUponEnteringTrap = 11 := by
  rw [laws.electronEntryEnergyFromPotentialDifference,
    data.incidentKineticEnergyIsTwoElectronVolts,
    data.trapRegionPotentialIsZeroVolts,
    data.incidentRegionPotentialIsMinusNineVolts]
  norm_num

/-- Capture into the highest bound state `E₃` emits a `7 eV` photon. -/
lemma photonEnergyForCaptureAtE3_is_seven_electronVolts
    (setup : ElectronFiniteTrapSetup)
    (scenario : MatchesFinitePotentialTrapScenario setup)
    (data : MatchesProblemReadouts setup)
    (laws : SatisfiesElectronEntryAndCaptureLaws setup) :
    energyInElectronVolts
        (setup.emittedPhotonEnergyForCaptureAt .E3) = 7 := by
  have entryEnergy :=
    electronEnergyUponEnteringTrap_is_eleven_electronVolts
      setup scenario data laws
  have captureEnergy :=
    laws.singlePhotonCaptureEnergyConservation .E3
  simp only [BoundTrapLevel.toEnergyMarker] at captureEnergy
  rw [data.levelE3IsFourElectronVolts, entryEnergy] at captureEnergy
  linarith

/-!
Since `E₃` is the highest bound level, capture there removes less energy than
capture at `E₁` or `E₂`; its emitted photon therefore realizes the least
possible single-photon capture energy.
-/
lemma captureAtE3_has_least_photonEnergy
    (setup : ElectronFiniteTrapSetup)
    (_scenario : MatchesFinitePotentialTrapScenario setup)
    (data : MatchesProblemReadouts setup)
    (_physical : HasPhysicalFiniteTrapParameters setup)
    (laws : SatisfiesElectronEntryAndCaptureLaws setup) :
    IsLeastCapturePhotonEnergy setup
      (setup.emittedPhotonEnergyForCaptureAt .E3) := by
  refine ⟨⟨.E3, rfl⟩, ?_⟩
  intro level
  have captureAtE3 :=
    laws.singlePhotonCaptureEnergyConservation .E3
  cases level with
  | E1 =>
      have captureAtE1 :=
        laws.singlePhotonCaptureEnergyConservation .E1
      simp only [BoundTrapLevel.toEnergyMarker] at captureAtE1 captureAtE3
      rw [data.levelE1IsOneElectronVolt] at captureAtE1
      rw [data.levelE3IsFourElectronVolts] at captureAtE3
      linarith
  | E2 =>
      have captureAtE2 :=
        laws.singlePhotonCaptureEnergyConservation .E2
      simp only [BoundTrapLevel.toEnergyMarker] at captureAtE2 captureAtE3
      rw [data.levelE2IsTwoElectronVolts] at captureAtE2
      rw [data.levelE3IsFourElectronVolts] at captureAtE3
      linarith
  | E3 =>
      exact le_rfl

/-! ## Printed answer choices -/

/-- Labels printed beside the four energy choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed scalar energy for each choice, in electron volts. -/
def AnswerChoice.energyInElectronVolts : AnswerChoice → ℝ
  | .A => 2
  | .B => 4
  | .C => 7
  | .D => 5

/-!
An answer choice is physically correct when its displayed value is realized
by a least-energy capture photon.  This remains a substantive proposition:
the least photon observable is not defined from the choice table.
-/
def AnswerChoice.IsCorrectFor
    (choice : AnswerChoice) (setup : ElectronFiniteTrapSetup) : Prop :=
  ∃ photonEnergy : DimEnergy,
    IsLeastCapturePhotonEnergy setup photonEnergy ∧
      PhyXMiniProblems.ProblemPhyXMini0585.energyInElectronVolts
          photonEnergy = choice.energyInElectronVolts

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The smallest photon capable of leaving the electron trapped is emitted on
capture into `E₃`; it has energy `7 eV`, so printed answer C is correct.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0585:target`.
-/
theorem smallestPhotonEnergy_is_seven_electronVolts
    (setup : ElectronFiniteTrapSetup)
    (scenario : MatchesFinitePotentialTrapScenario setup)
    (data : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedEnergyLevelFigure setup)
    (physical : HasPhysicalFiniteTrapParameters setup)
    (laws : SatisfiesElectronEntryAndCaptureLaws setup) :
    IsLeastCapturePhotonEnergy setup
        (setup.emittedPhotonEnergyForCaptureAt .E3) ∧
      energyInElectronVolts
          (setup.emittedPhotonEnergyForCaptureAt .E3) = 7 ∧
      AnswerChoice.IsCorrectFor .C setup := by
  have least :=
    captureAtE3_has_least_photonEnergy setup scenario data physical laws
  have energy :=
    photonEnergyForCaptureAtE3_is_seven_electronVolts
      setup scenario data laws
  refine ⟨least, energy, ?_⟩
  exact ⟨setup.emittedPhotonEnergyForCaptureAt .E3, least, energy⟩

end PhyXMiniProblems.ProblemPhyXMini0585
