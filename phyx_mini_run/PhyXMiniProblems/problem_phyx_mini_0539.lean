import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0539

open Dimension

/-!
# Energy delivered by a seven-dynode photomultiplier

The supplied figure shows a scintillation crystal, a photocathode at `0 V`,
seven dynodes at `100 V`, ..., `700 V`, a vacuum enclosure, secondary-electron
trajectories, and an output to a counter. One photoelectron reaches the first
dynode. An electron gains `100 eV` in each gap, and the average energy needed
to free one secondary electron is `10 eV`.

Physical energies and electrode potentials remain unit-independent
dimensionful quantities. Real numbers are used only at explicitly named
electron-volt and volt readout boundaries and for displayed answer data. The
energy available to the counter is an independent physical field constrained
by a governing aggregation law; it is not defined to equal an answer choice.
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

/-- Read a physical energy in electron volts. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a physical electric potential in coherent-SI volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Apparatus, stage indexing, and primary-figure data -/

/-- The material filling the photomultiplier enclosure. -/
inductive TubeInteriorMedium where
  | vacuum
  | other
  deriving DecidableEq, Fintype, Repr

/-!
Literal information carried by image 539. Electrode position `0` is the
photocathode, and positions `1`, ..., `7` are the seven dynodes in increasing
potential order. The potential labels are scalar volt readouts.
-/
structure PhotomultiplierFigure where
  displayedElectrodePotentialInVolts : Fin 8 → ℝ
  dynodeSurfaceVisible : Fin 7 → Bool
  secondaryEmissionPathVisible : Fin 7 → Bool
  scintillationCrystalVisible : Bool
  photocathodeVisible : Bool
  vacuumLabelVisible : Bool
  outputToCounterVisible : Bool

/-!
Independent physical quantities in the idealized tube. Dynode index `0` is
the `+100 V` dynode, and index `6` is the last, `+700 V`, dynode. Electron
counts and secondary yields are discrete; energy and potential retain their
physical dimensions.
-/
structure SevenDynodePhotomultiplierSetup where
  interiorMedium : TubeInteriorMedium
  electrodePotential : Fin 8 → ElectricPotentialQuantity
  initialPhotoelectronCount : ℕ
  averageEnergyToFreeElectron : DimEnergy
  overallEfficiency : NNReal
  impactEnergyPerElectronAtDynode : Fin 7 → DimEnergy
  secondaryElectronYieldAtDynode : Fin 7 → ℕ
  arrivingElectronCountAtDynode : Fin 7 → ℕ
  energyAvailableToCounter : DimEnergy
  figure : PhotomultiplierFigure

/-! ## Prose assumptions and primary-image readouts -/

/-!
Problem data stated in the prose: one initial photoelectron, `10.0 eV` average
liberation energy, a vacuum interior, and `100%` efficiency. The first-arrival
field is an initial condition, not a conclusion about later multiplication.
-/
structure MatchesPhotomultiplierProblemData
    (setup : SevenDynodePhotomultiplierSetup) : Prop where
  tubeInteriorIsVacuum : setup.interiorMedium = .vacuum
  oneInitialPhotoelectron : setup.initialPhotoelectronCount = 1
  firstDynodeReceivesInitialPhotoelectron :
    setup.arrivingElectronCountAtDynode 0 = setup.initialPhotoelectronCount
  averageLiberationEnergyTenElectronVolts :
    energyInElectronVolts setup.averageEnergyToFreeElectron = 10
  perfectEfficiency : setup.overallEfficiency = 1

/-!
All unambiguous data read from the supplied image: voltage labels
`0, 100, ..., 700 V`, their calibration to the physical electrodes, the
scintillator and photocathode, seven dynode surfaces, multiplication tracks,
the vacuum label, and the counter output.
-/
structure MatchesSuppliedPhotomultiplierFigure
    (setup : SevenDynodePhotomultiplierSetup) : Prop where
  displayedPotentialSequence : ∀ position : Fin 8,
    setup.figure.displayedElectrodePotentialInVolts position =
      (100 : ℝ) * ((position : ℕ) : ℝ)
  displayedPotentialsMeasureElectrodes : ∀ position : Fin 8,
    electricPotentialInVolts (setup.electrodePotential position) =
      setup.figure.displayedElectrodePotentialInVolts position
  allSevenDynodesVisible : ∀ dynode : Fin 7,
    setup.figure.dynodeSurfaceVisible dynode = true
  multiplyingPathsVisible : ∀ dynode : Fin 7,
    setup.figure.secondaryEmissionPathVisible dynode = true
  scintillationCrystalShown :
    setup.figure.scintillationCrystalVisible = true
  photocathodeShown : setup.figure.photocathodeVisible = true
  vacuumLabelShown : setup.figure.vacuumLabelVisible = true
  counterOutputShown : setup.figure.outputToCounterVisible = true

/-- Physical sign and range conditions, independent of the requested answer. -/
structure HasPhysicalPhotomultiplierParameters
    (setup : SevenDynodePhotomultiplierSetup) : Prop where
  averageLiberationEnergyPositive :
    0 < energyInElectronVolts setup.averageEnergyToFreeElectron
  impactEnergiesPositive : ∀ dynode : Fin 7,
    0 < energyInElectronVolts (setup.impactEnergyPerElectronAtDynode dynode)
  electrodePotentialsIncrease : ∀ dynode : Fin 7,
    electricPotentialInVolts
        (setup.electrodePotential dynode.castSucc) <
      electricPotentialInVolts
        (setup.electrodePotential dynode.succ)
  efficiencyAtMostOne : setup.overallEfficiency ≤ 1
  counterEnergyNonnegative :
    0 ≤ energyInElectronVolts setup.energyAvailableToCounter

/-! ## Governing photomultiplier laws -/

/-!
The idealized laws used by the calculation are uniform across the seven
dynodes:

* one electron accelerated through `ΔV` volts gains numerically `ΔV` electron
  volts of impact energy;
* the efficient part of that impact energy is the energy budget for freeing an
  integral number of secondary electrons;
* all emitted electrons propagate to the next dynode; and
* the counter receives the aggregate impact energy of the electrons arriving
  at the last dynode.

No field states a yield of `10`, a last-stage arrival count of `10^6`, or the
requested total energy of `10^8 eV`.
-/
structure SatisfiesIdealPhotomultiplierLaws
    (setup : SevenDynodePhotomultiplierSetup) : Prop where
  electronImpactEnergyFromVoltageGap : ∀ dynode : Fin 7,
    energyInElectronVolts
        (setup.impactEnergyPerElectronAtDynode dynode) =
      electricPotentialInVolts
          (setup.electrodePotential dynode.succ) -
        electricPotentialInVolts
          (setup.electrodePotential dynode.castSucc)
  secondaryEmissionEnergyBudget : ∀ dynode : Fin 7,
    (setup.secondaryElectronYieldAtDynode dynode : ℝ) *
        energyInElectronVolts setup.averageEnergyToFreeElectron =
      (setup.overallEfficiency : ℝ) *
        energyInElectronVolts
          (setup.impactEnergyPerElectronAtDynode dynode)
  arrivingElectronPropagation : ∀ dynode : Fin 6,
    setup.arrivingElectronCountAtDynode dynode.succ =
      setup.arrivingElectronCountAtDynode dynode.castSucc *
        setup.secondaryElectronYieldAtDynode dynode.castSucc
  counterReceivesTotalLastDynodeImpactEnergy :
    energyInElectronVolts setup.energyAvailableToCounter =
      (setup.arrivingElectronCountAtDynode 6 : ℝ) *
        energyInElectronVolts
          (setup.impactEnergyPerElectronAtDynode 6)

/-! ## Derived stage values and final energy -/

/-!
Every adjacent electrode gap is `100 V`; perfect conversion of a `100 eV`
impact with a `10 eV` liberation cost produces ten secondary electrons per
incident electron at each dynode.
-/
lemma secondaryElectronYieldAtEveryDynode_eq_ten
    (setup : SevenDynodePhotomultiplierSetup)
    (h_data : MatchesPhotomultiplierProblemData setup)
    (h_figure : MatchesSuppliedPhotomultiplierFigure setup)
    (h_physical : HasPhysicalPhotomultiplierParameters setup)
    (h_laws : SatisfiesIdealPhotomultiplierLaws setup) :
    ∀ dynode : Fin 7,
      setup.secondaryElectronYieldAtDynode dynode = 10 := by
  intro dynode
  have h_impact := h_laws.electronImpactEnergyFromVoltageGap dynode
  simp [h_figure.displayedPotentialsMeasureElectrodes,
    h_figure.displayedPotentialSequence] at h_impact
  have h_budget := h_laws.secondaryEmissionEnergyBudget dynode
  norm_num [h_data.averageLiberationEnergyTenElectronVolts,
    h_data.perfectEfficiency, h_impact] at h_budget
  have hyield_real :
      (setup.secondaryElectronYieldAtDynode dynode : ℝ) = (10 : ℝ) := by
    nlinarith [h_budget]
  exact_mod_cast hyield_real

/-!
Starting from one electron at the first dynode and multiplying by ten at the
first six dynodes, `10^6` electrons arrive at the seventh dynode.
-/
lemma arrivingElectronCountAtLastDynode_eq_ten_pow_six
    (setup : SevenDynodePhotomultiplierSetup)
    (h_data : MatchesPhotomultiplierProblemData setup)
    (h_figure : MatchesSuppliedPhotomultiplierFigure setup)
    (h_physical : HasPhysicalPhotomultiplierParameters setup)
    (h_laws : SatisfiesIdealPhotomultiplierLaws setup) :
    setup.arrivingElectronCountAtDynode 6 = 10 ^ 6 := by
  have hyield := secondaryElectronYieldAtEveryDynode_eq_ten
    setup h_data h_figure h_physical h_laws
  have h0 := h_laws.arrivingElectronPropagation (0 : Fin 6)
  have h1 := h_laws.arrivingElectronPropagation (1 : Fin 6)
  have h2 := h_laws.arrivingElectronPropagation (2 : Fin 6)
  have h3 := h_laws.arrivingElectronPropagation (3 : Fin 6)
  have h4 := h_laws.arrivingElectronPropagation (4 : Fin 6)
  have h5 := h_laws.arrivingElectronPropagation (5 : Fin 6)
  change setup.arrivingElectronCountAtDynode (3 : Fin 7) =
    setup.arrivingElectronCountAtDynode (2 : Fin 7) *
      setup.secondaryElectronYieldAtDynode (2 : Fin 7) at h2
  change setup.arrivingElectronCountAtDynode (4 : Fin 7) =
    setup.arrivingElectronCountAtDynode (3 : Fin 7) *
      setup.secondaryElectronYieldAtDynode (3 : Fin 7) at h3
  change setup.arrivingElectronCountAtDynode (5 : Fin 7) =
    setup.arrivingElectronCountAtDynode (4 : Fin 7) *
      setup.secondaryElectronYieldAtDynode (4 : Fin 7) at h4
  change setup.arrivingElectronCountAtDynode (6 : Fin 7) =
    setup.arrivingElectronCountAtDynode (5 : Fin 7) *
      setup.secondaryElectronYieldAtDynode (5 : Fin 7) at h5
  norm_num [hyield, h_data.firstDynodeReceivesInitialPhotoelectron,
    h_data.oneInitialPhotoelectron] at h0
  norm_num [hyield, h0] at h1
  norm_num [hyield, h1] at h2
  norm_num [hyield, h2] at h3
  norm_num [hyield, h3] at h4
  norm_num [hyield, h4] at h5
  norm_num [h5]

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
  | .A => (10 : ℝ) ^ 10
  | .B => (10 : ℝ) ^ 6
  | .C => (10 : ℝ) ^ 12
  | .D => (10 : ℝ) ^ 8

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The `10^6` electrons arriving at the last dynode each carry `100 eV`, so the
energy available to the counter is `10^8 eV`, the value displayed as answer D.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0539:target`.
-/
theorem problem_phyx_mini_0539
    (setup : SevenDynodePhotomultiplierSetup)
    (h_data : MatchesPhotomultiplierProblemData setup)
    (h_figure : MatchesSuppliedPhotomultiplierFigure setup)
    (h_physical : HasPhysicalPhotomultiplierParameters setup)
    (h_laws : SatisfiesIdealPhotomultiplierLaws setup) :
    energyInElectronVolts setup.energyAvailableToCounter =
      (10 : ℝ) ^ 8 := by
  have harrive := arrivingElectronCountAtLastDynode_eq_ten_pow_six
    setup h_data h_figure h_physical h_laws
  have himpact := h_laws.electronImpactEnergyFromVoltageGap (6 : Fin 7)
  norm_num [h_figure.displayedPotentialsMeasureElectrodes,
    h_figure.displayedPotentialSequence] at himpact
  rw [h_laws.counterReceivesTotalLastDynodeImpactEnergy, harrive, himpact]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0539
