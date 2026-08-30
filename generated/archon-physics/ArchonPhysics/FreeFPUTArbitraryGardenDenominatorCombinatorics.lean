import ArchonPhysics.RandomBranchingSmallDenominatorUnion
import ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection

/-!
# Arbitrary finite FPUT gardens: cumulative denominators and sector unions

A higher joint moment contains a finite forest (often called a garden) of
rooted Duhamel trees.  This file performs the finite bookkeeping needed
before any high-order decoherence estimate:

* a dependent phase assignment is aligned with every root shape;
* every cumulative mismatch denominator of every branching linear extension
  is flattened into one list;
* total internal-node count, exact denominator-occurrence count, and the
  deterministic factorial/exponential capacity are sums over the roots;
* padded random coordinates turn the garden into one fixed finite family;
* ordinary nonresonant, identically-zero, resonant-connected, and recollision
  occurrences remain four disjoint sectors;
* a one-denominator small-ball estimate is union-bounded only over the
  ordinary sector.

The retained sectors are not errors.  In particular an identically-zero
denominator is resonant for every sample and cannot satisfy an ordinary
small-ball estimate with a vanishing budget.  Resonant connected clusters
and recollision/repeated-index histories likewise require separate algebra or
cancellation.  No RPA, independence, Markov approximation, or decay is used.
-/

namespace ArchonPhysics.FreeFPUTArbitraryGardenDenominatorCombinatorics

open scoped BigOperators ENNReal

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomBranchingSmallDenominatorUnion

noncomputable section

/-! ## A dependent assignment for every root in a finite garden -/

/-- One branching phase assignment for every tree in a finite ordered
garden.  The recursion keeps the dependent tree type visible. -/
def BranchingGardenPhaseAssignment :
    List BinaryInteractionTree → Type
  | [] => PUnit
  | tree :: trees =>
      BinaryInteractionTreePhaseAssignment tree ×
        BranchingGardenPhaseAssignment trees

/-- Flatten every cumulative denominator of every root.  Root order and all
within-root linear-extension/IBP multiplicities are retained. -/
def branchingGardenDenominators :
    (trees : List BinaryInteractionTree) →
      BranchingGardenPhaseAssignment trees → List Real
  | [], _assignment => []
  | tree :: trees, assignment =>
      branchingHistoryDenominators tree assignment.1 ++
        branchingGardenDenominators trees assignment.2

/-- Total number of interaction vertices in the garden. -/
def branchingGardenNodeCount (trees : List BinaryInteractionTree) : Nat :=
  (trees.map BinaryInteractionTree.order).sum

/-- Exact number of denominator occurrences, summed root by root. -/
def branchingGardenDenominatorOccurrenceCount :
    (trees : List BinaryInteractionTree) →
      BranchingGardenPhaseAssignment trees → Nat
  | [], _assignment => 0
  | tree :: trees, assignment =>
      (branchingPhaseLinearExtensions tree assignment.1).length *
          (2 ^ tree.order - 1) +
        branchingGardenDenominatorOccurrenceCount trees assignment.2

/-- Deterministic capacity obtained by summing the existing per-root
factorial/exponential capacities. -/
def branchingGardenDenominatorCapacity
    (trees : List BinaryInteractionTree) : Nat :=
  (trees.map branchingDenominatorCapacity).sum

@[simp] theorem branchingGardenNodeCount_nil :
    branchingGardenNodeCount [] = 0 := rfl

@[simp] theorem branchingGardenNodeCount_cons
    (tree : BinaryInteractionTree) (trees : List BinaryInteractionTree) :
    branchingGardenNodeCount (tree :: trees) =
      tree.order + branchingGardenNodeCount trees := by
  simp [branchingGardenNodeCount]

@[simp] theorem branchingGardenDenominatorOccurrenceCount_nil
    (assignment : BranchingGardenPhaseAssignment []) :
    branchingGardenDenominatorOccurrenceCount [] assignment = 0 := rfl

@[simp] theorem branchingGardenDenominatorOccurrenceCount_cons
    (tree : BinaryInteractionTree) (trees : List BinaryInteractionTree)
    (assignment : BranchingGardenPhaseAssignment (tree :: trees)) :
    branchingGardenDenominatorOccurrenceCount (tree :: trees) assignment =
      (branchingPhaseLinearExtensions tree assignment.1).length *
          (2 ^ tree.order - 1) +
        branchingGardenDenominatorOccurrenceCount trees assignment.2 := rfl

/-- The flattened garden list has exactly the sum of the exact root
occurrence counts. -/
theorem length_branchingGardenDenominators :
    ∀ (trees : List BinaryInteractionTree)
      (assignment : BranchingGardenPhaseAssignment trees),
      (branchingGardenDenominators trees assignment).length =
        branchingGardenDenominatorOccurrenceCount trees assignment
  | [], _assignment => rfl
  | tree :: trees, assignment => by
      simp only [branchingGardenDenominators, List.length_append,
        branchingGardenDenominatorOccurrenceCount]
      rw [length_branchingHistoryDenominators,
        length_branchingGardenDenominators trees assignment.2]

@[simp] theorem branchingGardenDenominatorCapacity_nil :
    branchingGardenDenominatorCapacity [] = 0 := rfl

@[simp] theorem branchingGardenDenominatorCapacity_cons
    (tree : BinaryInteractionTree) (trees : List BinaryInteractionTree) :
    branchingGardenDenominatorCapacity (tree :: trees) =
      branchingDenominatorCapacity tree +
        branchingGardenDenominatorCapacity trees := by
  simp [branchingGardenDenominatorCapacity]

/-- The exact garden denominator list fits in the deterministic sum of the
per-root capacities. -/
theorem length_branchingGardenDenominators_le_capacity :
    ∀ (trees : List BinaryInteractionTree)
      (assignment : BranchingGardenPhaseAssignment trees),
      (branchingGardenDenominators trees assignment).length ≤
        branchingGardenDenominatorCapacity trees
  | [], assignment => by
      cases assignment
      rfl
  | tree :: trees, assignment => by
      simp only [branchingGardenDenominators, List.length_append,
        branchingGardenDenominatorCapacity_cons]
      exact Nat.add_le_add
        (length_branchingHistoryDenominators_le_capacity tree assignment.1)
        (length_branchingGardenDenominators_le_capacity trees assignment.2)

/-! ## Actual fixed-root raw-history gardens -/

/-- One existing arbitrary-order fixed-root raw FPUT history, packaged with
its actual tree and a phase label at every internal node.  Different garden
roots may have different perturbative orders and output momenta. -/
structure FixedRootRawBranchingGardenEntry (N : Nat) [NeZero N] where
  order : Nat
  rootMomentum : Site N
  history : FixedRootRawHistoryIndex N order rootMomentum
  phaseAssignment : BinaryInteractionTreePhaseAssignment history.1.1

/-- Cumulative denominators of one packaged actual raw history. -/
def fixedRootRawBranchingGardenEntryDenominators
    {N : Nat} [NeZero N]
    (entry : FixedRootRawBranchingGardenEntry N) : List Real :=
  branchingHistoryDenominators entry.history.1.1 entry.phaseAssignment

/-- Flattened cumulative denominators of an arbitrary finite garden of the
existing `FixedRootRawHistoryIndex` objects. -/
def fixedRootRawBranchingGardenDenominators
    {N : Nat} [NeZero N]
    (garden : List (FixedRootRawBranchingGardenEntry N)) : List Real :=
  garden.flatMap fixedRootRawBranchingGardenEntryDenominators

/-- The actual raw-history garden has the sum of its declared perturbative
orders as its total internal-node count. -/
def fixedRootRawBranchingGardenNodeCount
    {N : Nat} [NeZero N]
    (garden : List (FixedRootRawBranchingGardenEntry N)) : Nat :=
  (garden.map FixedRootRawBranchingGardenEntry.order).sum

/-- Exact per-entry denominator occurrence count. -/
def fixedRootRawBranchingGardenEntryDenominatorCount
    {N : Nat} [NeZero N]
    (entry : FixedRootRawBranchingGardenEntry N) : Nat :=
  (branchingPhaseLinearExtensions
      entry.history.1.1 entry.phaseAssignment).length *
    (2 ^ entry.order - 1)

/-- Exact denominator count of an actual raw-history garden. -/
def fixedRootRawBranchingGardenDenominatorCount
    {N : Nat} [NeZero N]
    (garden : List (FixedRootRawBranchingGardenEntry N)) : Nat :=
  (garden.map fixedRootRawBranchingGardenEntryDenominatorCount).sum

/-- The shape carried by a packaged raw history has exactly its declared
number of internal nodes. -/
theorem fixedRootRawBranchingGardenEntry_tree_order
    {N : Nat} [NeZero N]
    (entry : FixedRootRawBranchingGardenEntry N) :
    entry.history.1.1.order = entry.order :=
  entry.history.1.2

/-- Actual fixed-root adapter for the exact per-entry occurrence count. -/
theorem length_fixedRootRawBranchingGardenEntryDenominators
    {N : Nat} [NeZero N]
    (entry : FixedRootRawBranchingGardenEntry N) :
    (fixedRootRawBranchingGardenEntryDenominators entry).length =
      fixedRootRawBranchingGardenEntryDenominatorCount entry := by
  rw [fixedRootRawBranchingGardenEntryDenominators,
    length_branchingHistoryDenominators,
    fixedRootRawBranchingGardenEntryDenominatorCount,
    fixedRootRawBranchingGardenEntry_tree_order]

/-- The flattened actual raw-history garden denominator count is the sum of
the counts of all roots. -/
theorem length_fixedRootRawBranchingGardenDenominators
    {N : Nat} [NeZero N]
    (garden : List (FixedRootRawBranchingGardenEntry N)) :
    (fixedRootRawBranchingGardenDenominators garden).length =
      fixedRootRawBranchingGardenDenominatorCount garden := by
  induction garden with
  | nil => rfl
  | cons entry garden ih =>
      have htail := ih
      simp only [fixedRootRawBranchingGardenDenominators,
        fixedRootRawBranchingGardenDenominatorCount] at htail
      simp only [fixedRootRawBranchingGardenDenominators,
        List.flatMap_cons, List.length_append,
        fixedRootRawBranchingGardenDenominatorCount,
        List.map_cons, List.sum_cons]
      rw [length_fixedRootRawBranchingGardenEntryDenominators, htail]

/-! ## Four disjoint denominator sectors -/

/-- Sector bookkeeping for high-order decoherence.  Only the first
constructor is eligible for the ordinary nonresonant small-ball union. -/
inductive GardenDenominatorSector where
  | ordinaryNonresonant
  | identicallyZero
  | resonantConnected
  | recollision
  deriving DecidableEq, Repr

/-- Fixed padded coordinates belonging to one chosen sector. -/
abbrev GardenSectorIndex
    (capacity : Nat)
    (sector : Fin capacity → GardenDenominatorSector)
    (target : GardenDenominatorSector) :=
  {i : Fin capacity // sector i = target}

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Small-gap event restricted to one explicitly chosen sector. -/
def gardenSectorSmallDenominatorEvent
    (capacity : Nat)
    (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (target : GardenDenominatorSector) (gamma : Real) : Set Omega :=
  finiteSmallDenominatorEvent
    (fun i : GardenSectorIndex capacity sector target => coordinate i.1)
    gamma

omit [MeasurableSpace Omega] in
theorem mem_gardenSectorSmallDenominatorEvent_iff
    (capacity : Nat)
    (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (target : GardenDenominatorSector) (gamma : Real) (omega : Omega) :
    omega ∈ gardenSectorSmallDenominatorEvent
        capacity coordinate sector target gamma ↔
      ∃ i : Fin capacity,
        sector i = target ∧ |coordinate i omega| < gamma := by
  rw [gardenSectorSmallDenominatorEvent,
    mem_finiteSmallDenominatorEvent_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.1, i.2, hi⟩
  · rintro ⟨i, hsector, hi⟩
    exact ⟨⟨i, hsector⟩, hi⟩

/-- The complete padded small-gap event is exactly the union of the four
sectors.  Thus resonant and recollision occurrences are retained rather than
silently fed into the ordinary estimate. -/
theorem finiteSmallDenominatorEvent_eq_sector_union
    (capacity : Nat)
    (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (gamma : Real) :
    finiteSmallDenominatorEvent coordinate gamma =
      gardenSectorSmallDenominatorEvent capacity coordinate sector
          .ordinaryNonresonant gamma ∪
        gardenSectorSmallDenominatorEvent capacity coordinate sector
          .identicallyZero gamma ∪
        gardenSectorSmallDenominatorEvent capacity coordinate sector
          .resonantConnected gamma ∪
        gardenSectorSmallDenominatorEvent capacity coordinate sector
          .recollision gamma := by
  ext omega
  rw [mem_finiteSmallDenominatorEvent_iff]
  simp only [Set.mem_union,
    mem_gardenSectorSmallDenominatorEvent_iff]
  constructor
  · rintro ⟨i, hi⟩
    cases hsector : sector i with
    | ordinaryNonresonant =>
        exact Or.inl (Or.inl (Or.inl ⟨i, hsector, hi⟩))
    | identicallyZero =>
        exact Or.inl (Or.inl (Or.inr ⟨i, hsector, hi⟩))
    | resonantConnected =>
        exact Or.inl (Or.inr ⟨i, hsector, hi⟩)
    | recollision =>
        exact Or.inr ⟨i, hsector, hi⟩
  · rintro (((hordinary | hzero) | hresonant) | hrecollision)
    · rcases hordinary with ⟨i, _hsector, hi⟩
      exact ⟨i, hi⟩
    · rcases hzero with ⟨i, _hsector, hi⟩
      exact ⟨i, hi⟩
    · rcases hresonant with ⟨i, _hsector, hi⟩
      exact ⟨i, hi⟩
    · rcases hrecollision with ⟨i, _hsector, hi⟩
      exact ⟨i, hi⟩

/-- Finite union bound within one sector.  No independence is used. -/
theorem measure_gardenSectorSmallDenominatorEvent_le_card_mul
    (mu : Measure Omega) (capacity : Nat)
    (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (target : GardenDenominatorSector) (gamma : Real) (budget : ENNReal)
    (hone : ∀ i : GardenSectorIndex capacity sector target,
      mu {omega | |coordinate i.1 omega| < gamma} ≤ budget) :
    mu (gardenSectorSmallDenominatorEvent
      capacity coordinate sector target gamma) ≤
      (Fintype.card (GardenSectorIndex capacity sector target) : ENNReal) *
        budget := by
  exact measure_finiteSmallDenominatorEvent_le_card_mul
    mu (fun i : GardenSectorIndex capacity sector target => coordinate i.1)
      gamma budget hone

/-- Capacity-only ordinary-sector bound.  Retained sectors do not contribute
to its cardinality or hypotheses. -/
theorem measure_ordinaryGardenSmallDenominatorEvent_le_capacity_mul
    (mu : Measure Omega) (capacity : Nat)
    (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (gamma : Real) (budget : ENNReal)
    (hone : ∀ i : GardenSectorIndex capacity sector .ordinaryNonresonant,
      mu {omega | |coordinate i.1 omega| < gamma} ≤ budget) :
    mu (gardenSectorSmallDenominatorEvent capacity coordinate sector
        .ordinaryNonresonant gamma) ≤
      (capacity : ENNReal) * budget := by
  calc
    mu (gardenSectorSmallDenominatorEvent capacity coordinate sector
        .ordinaryNonresonant gamma) ≤
        (Fintype.card
          (GardenSectorIndex capacity sector .ordinaryNonresonant) : ENNReal) *
          budget :=
      measure_gardenSectorSmallDenominatorEvent_le_card_mul
        mu capacity coordinate sector .ordinaryNonresonant gamma budget hone
    _ ≤ (capacity : ENNReal) * budget := by
      gcongr
      simpa using Fintype.card_subtype_le
        (fun i : Fin capacity => sector i = .ordinaryNonresonant)

/-- If an explicitly retained zero-sector coordinate exists and is
identically zero, its positive-gap event is the whole sample space.  This
formally prevents treating it as an ordinary vanishing small-ball event. -/
theorem gardenIdenticallyZeroSectorSmallEvent_eq_univ
    (capacity : Nat) (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (i : Fin capacity) (hi : sector i = .identicallyZero)
    (hzero : ∀ omega, coordinate i omega = 0)
    {gamma : Real} (hgamma : 0 < gamma) :
    gardenSectorSmallDenominatorEvent capacity coordinate sector
      .identicallyZero gamma = Set.univ := by
  apply Set.eq_univ_of_forall
  intro omega
  rw [mem_gardenSectorSmallDenominatorEvent_iff]
  exact ⟨i, hi, by simp [hzero omega, hgamma]⟩

/-! ## Random fixed-shape branching gardens -/

/-- Padded coordinate of the flattened denominator list of a random phase
assignment on one fixed finite garden of tree shapes. -/
def randomBranchingGardenDenominatorCoordinate
    (trees : List BinaryInteractionTree)
    (assignment : Omega → BranchingGardenPhaseAssignment trees)
    (defaultValue : Real)
    (i : Fin (branchingGardenDenominatorCapacity trees))
    (omega : Omega) : Real :=
  paddedRandomListCoordinate
    (fun sample => branchingGardenDenominators trees (assignment sample))
    (branchingGardenDenominatorCapacity trees) defaultValue i omega

/-- Exact event decomposition for a random fixed-shape garden.  A safe
padding value contributes no false small occurrence. -/
theorem randomBranchingGardenSmallEvent_eq_sector_union
    (trees : List BinaryInteractionTree)
    (assignment : Omega → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real) (hdefault : gamma ≤ |defaultValue|)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector) :
    {omega | ∃ delta ∈ branchingGardenDenominators trees (assignment omega),
        |delta| < gamma} =
      gardenSectorSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector .ordinaryNonresonant gamma ∪
        gardenSectorSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector .identicallyZero gamma ∪
        gardenSectorSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector .resonantConnected gamma ∪
        gardenSectorSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector .recollision gamma := by
  have hpadded :
      {omega | ∃ delta ∈ branchingGardenDenominators trees (assignment omega),
          |delta| < gamma} =
        finiteSmallDenominatorEvent
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue) gamma := by
    ext omega
    rw [mem_finiteSmallDenominatorEvent_iff]
    exact exists_mem_small_iff_exists_paddedRandomListCoordinate_small
      (fun sample => branchingGardenDenominators trees (assignment sample))
      (branchingGardenDenominatorCapacity trees) defaultValue gamma
      (fun sample =>
        length_branchingGardenDenominators_le_capacity
          trees (assignment sample)) hdefault omega
  rw [hpadded]
  exact finiteSmallDenominatorEvent_eq_sector_union
    (branchingGardenDenominatorCapacity trees)
    (randomBranchingGardenDenominatorCoordinate
      trees assignment defaultValue) sector gamma

/-- Actual all-root ordinary-sector union bound.  The one-gap premise is
required only for coordinates explicitly classified as ordinary. -/
theorem measure_randomBranchingGardenOrdinarySmallEvent_le_capacity_mul
    (mu : Measure Omega) (trees : List BinaryInteractionTree)
    (assignment : Omega → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector)
    (budget : ENNReal)
    (hone : ∀ i : GardenSectorIndex
        (branchingGardenDenominatorCapacity trees) sector
        .ordinaryNonresonant,
      mu {omega |
        |randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue i.1 omega| < gamma} ≤ budget) :
    mu (gardenSectorSmallDenominatorEvent
        (branchingGardenDenominatorCapacity trees)
        (randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue)
        sector .ordinaryNonresonant gamma) ≤
      (branchingGardenDenominatorCapacity trees : ENNReal) * budget := by
  exact measure_ordinaryGardenSmallDenominatorEvent_le_capacity_mul
    mu (branchingGardenDenominatorCapacity trees)
      (randomBranchingGardenDenominatorCoordinate
        trees assignment defaultValue)
      sector gamma budget hone

end

end ArchonPhysics.FreeFPUTArbitraryGardenDenominatorCombinatorics
