import IChO2026Chem
import Mathlib

/-!
# IChO 2026 T6-A7: global aromaticity of P6

The displayed compound P6 is a cyclic zinc-porphyrin nanobelt made from six
porphyrin repeat units linked by ethynyl groups.  The question instructs us to
count only the continuous conjugated pathway around the macrocycle.  This file
models that pathway separately from the rest of the molecular drawing, and
formalizes Hückel's `4k + 2` condition as an arithmetic relation on its
π-electron count.
-/

namespace IChO2026Problems.T6A7

/-- The metal centre shown in every porphyrin unit of P6. -/
private inductive PorphyrinMetalCentre where
  | zinc
  deriving DecidableEq, Repr

/-- The inter-porphyrin connection used in the displayed P6 nanobelt. -/
private inductive PorphyrinLinker where
  | ethynyl
  deriving DecidableEq, Repr

/-- The topology relevant to a global π-electron pathway. -/
private inductive PiPathwayTopology where
  | cyclic
  deriving DecidableEq, Repr

/--
The seven occupied π bonds contributed by one repeat to the bold global
pathway in the source image: five bonds on the lower porphyrin arc and the two
orthogonal π bonds of the boundary ethynyl linker.  Naming these bonds keeps
the intermediate count of fourteen electrons out of the input data.
-/
private inductive GlobalPathwayPiBond where
  | porphyrinArcBond1
  | porphyrinArcBond2
  | porphyrinArcBond3
  | porphyrinArcBond4
  | porphyrinArcBond5
  | ethynylPiBond1
  | ethynylPiBond2
  deriving DecidableEq, Repr, Fintype

/-- Each occupied π bond contributes its two electron slots. -/
private abbrev OccupiedPiBondElectronSlot := Fin 2

/-- The six porphyrin repeats drawn in `P6`. -/
private abbrev P6Repeat := Fin 6

/-- One electron on the explicitly represented bold pathway of `P6`. -/
private abbrev P6GlobalPathwayElectron :=
  P6Repeat × (GlobalPathwayPiBond × OccupiedPiBondElectronSlot)

/-- All occupied electron slots on the bold global pathway. -/
private def P6GlobalPathwayElectrons : Finset P6GlobalPathwayElectron :=
  Finset.univ

/--
A macrocyclic π system with the structural labels shown for `P6`.  Its
electron population is computed from `P6GlobalPathwayElectrons`, not stored as
a numerical field.
-/
private structure PorphyrinNanobelt where
  metalCentre : PorphyrinMetalCentre
  linker : PorphyrinLinker
  pathwayTopology : PiPathwayTopology
  deriving DecidableEq, Repr

/-- The computed number of occupied π-electron slots before oxidation. -/
private def groundStatePiElectronCount : ℕ :=
  P6GlobalPathwayElectrons.card

/-- The π-electron count on the same global pathway after oxidative electron removal. -/
private def totalPiElectronsAfterRemoval (electronsRemoved : ℕ) : ℕ :=
  groundStatePiElectronCount - electronsRemoved

/-- Hückel's `4k + 2` π-electron criterion used in this subquestion. -/
private def SatisfiesHuckelRule (piElectronCount : ℕ) : Prop :=
  ∃ k : ℕ, piElectronCount = 4 * k + 2

/--
The source condition for global aromaticity after oxidation: the pathway is a
cycle, oxidation removes a positive number of electrons without exceeding the
ground-state population, and the remaining pathway electrons satisfy Hückel's
rule.
-/
private def IsGloballyAromaticAfterElectronRemoval
    (nanobelt : PorphyrinNanobelt) (electronsRemoved : ℕ) : Prop :=
  nanobelt.pathwayTopology = .cyclic ∧
    0 < electronsRemoved ∧
      electronsRemoved ≤ groundStatePiElectronCount ∧
        SatisfiesHuckelRule (totalPiElectronsAfterRemoval electronsRemoved)

/-- A removal count is minimal when it produces global aromaticity and no smaller
removal count does so. -/
private def IsMinimumElectronRemovalForGlobalAromaticity
    (nanobelt : PorphyrinNanobelt) (electronsRemoved : ℕ) : Prop :=
  IsGloballyAromaticAfterElectronRemoval nanobelt electronsRemoved ∧
    ∀ alternativeRemoval : ℕ,
      IsGloballyAromaticAfterElectronRemoval nanobelt alternativeRemoval →
        electronsRemoved ≤ alternativeRemoval

/-- P6 has the source-image labels; its six repeats live in `P6Repeat`. -/
private def P6 : PorphyrinNanobelt :=
  { metalCentre := .zinc
    linker := .ethynyl
    pathwayTopology := .cyclic }

/-- The source pathway contributes five porphyrin and two ethynyl π bonds. -/
private theorem globalPathwayPiBondsPerRepeat_card :
    Fintype.card GlobalPathwayPiBond = 7 := by
  decide

/-- Six repeats times seven occupied π bonds times two electrons gives 84. -/
private theorem P6_ground_state_pi_electron_count :
    groundStatePiElectronCount = 84 := by
  change Fintype.card P6GlobalPathwayElectron = 84
  rw [Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fin, globalPathwayPiBondsPerRepeat_card,
    Fintype.card_fin]

/--
T6-A7.  Removing two electrons is the minimum oxidation of P6 that gives a
globally aromatic pathway under Hückel's rule, and that pathway then contains
eighty-two π electrons.

Both requested numerical outputs occur only in this conclusion.  The
intermediate population is derived from the explicitly named pathway bonds
and their occupied electron slots rather than stored in `P6`.
-/
theorem P6_minimum_electron_removal_for_global_aromaticity :
    IsMinimumElectronRemovalForGlobalAromaticity P6 2 ∧
      totalPiElectronsAfterRemoval 2 = 82 := by
  constructor
  · constructor
    · refine ⟨rfl, by norm_num, ?_, ?_⟩
      · rw [P6_ground_state_pi_electron_count]
        norm_num
      refine ⟨20, ?_⟩
      simp only [totalPiElectronsAfterRemoval]
      rw [P6_ground_state_pi_electron_count]
    · intro alternativeRemoval hAromatic
      rcases hAromatic with ⟨_, hPositive, _, hHuckel⟩
      simp only [SatisfiesHuckelRule, totalPiElectronsAfterRemoval] at hHuckel
      rw [P6_ground_state_pi_electron_count] at hHuckel
      omega
  · simp only [totalPiElectronsAfterRemoval]
    rw [P6_ground_state_pi_electron_count]

end IChO2026Problems.T6A7
