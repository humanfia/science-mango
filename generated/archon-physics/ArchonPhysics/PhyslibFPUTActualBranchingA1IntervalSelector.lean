import ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound

/-!
# Actual branching A1 interval selector

A decorated random-eigenmode FPUT tree carries more information than the
scalar `BinaryInteractionTreePhaseAssignment`: every internal node has an
output mode, two child modes, and two phase signs.  This file packages that
node as a genuine `QuadraticPhaseTerm`, enumerates metadata-preserving linear
extensions, and proves that every denominator occurrence in
`branchingHistoryDenominators` is a contiguous interval sum of these actual
local A1 mismatches.

The resulting selector is finite.  Its coordinate type is a linear-extension
position paired with a distinct interval endpoint pair, and its cardinality
is bounded by `order! * order^2`.  Each occurrence may choose its own
retained mass pair; at the original frozen iid mass realization, reinserting
that pair reconstructs the same full mass configuration exactly.

There is a precise boundary with
`RandomBranchingA1IntervalFiberSelector`.  That earlier interface represents
an interval by a list of terms with one common `observed` mode.  A genuine
branching linear extension generally contains vertices with different output
modes.  We give the exact homogeneous-output adapter and a two-vertex
obstruction to applying it automatically.  The heterogeneous selector below
is exact algebraically, but compact-atlas transversality for its Jacobian sum
still requires an occurrence-dependent noncancellation argument.  No
independence, re-Haar, Markov/RPA closure, or recollision decay is asserted.
-/

namespace ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomEnsemble
open Set

noncomputable section

/-- Genuine local A1 data at one decorated branching vertex. -/
structure ActualA1Vertex (N : Nat) where
  observed : Lattice.Site N
  term : QuadraticPhaseTerm N

/-- The inverse finite index of a tree edge's phase sign. -/
def phaseSignQuadraticIndex : PhaseSign → Fin 2
  | .phase => 0
  | .conjugate => 1

@[simp] theorem binaryPhaseSign_phaseSignQuadraticIndex
    (sign : PhaseSign) :
    binaryPhaseSign (phaseSignQuadraticIndex sign) = sign := by
  cases sign <;> rfl

/-- Convert one decorated internal node to its genuine quadratic A1 vertex. -/
def randomEigenmodeBinaryNodeA1Vertex
    {N : Nat} [NeZero N]
    (output : Lattice.Site N) (leftSign rightSign : PhaseSign)
    (left right : RandomEigenmodeBinaryTree (Lattice.Site N)) :
    ActualA1Vertex N where
  observed := output
  term :=
    (Fin.cases left.rootMode (fun _ => right.rootMode),
      (phaseSignQuadraticIndex leftSign,
        phaseSignQuadraticIndex rightSign))

/-- Actual local mismatch of one packaged branching vertex. -/
def ActualA1Vertex.mismatch
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (vertex : ActualA1Vertex N) : Real :=
  quadraticPhaseMismatch (modeFrequency mass)
    vertex.observed vertex.term

/-- A packaged node mismatch is the existing local binary-vertex mismatch. -/
theorem mismatch_randomEigenmodeBinaryNodeA1Vertex
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (output : Lattice.Site N) (leftSign rightSign : PhaseSign)
    (left right : RandomEigenmodeBinaryTree (Lattice.Site N)) :
    (randomEigenmodeBinaryNodeA1Vertex
      output leftSign rightSign left right).mismatch mass =
      binaryVertexMismatch (modeFrequency mass) output leftSign rightSign
        left.rootMode right.rootMode := by
  simp only [randomEigenmodeBinaryNodeA1Vertex, ActualA1Vertex.mismatch,
    quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    quadraticPhaseCharge, chargeFrequency_add,
    chargeFrequency_binarySignedMode, binaryVertexMismatch]
  rw [binaryPhaseSign_phaseSignQuadraticIndex,
    binaryPhaseSign_phaseSignQuadraticIndex]
  rw [show Fin.cases left.rootMode (fun _ => right.rootMode) (0 : Fin 2) =
    left.rootMode by rfl]
  rw [show Fin.cases left.rootMode (fun _ => right.rootMode) (1 : Fin 2) =
    right.rootMode by rfl]
  ring

/-! ## Metadata-preserving shuffles -/

/-- Polymorphic order-preserving shuffles, retaining multiplicity. -/
def orderedListShuffles {α : Type*} : List α → List α → List (List α)
  | [], [] => [[]]
  | [], rightHead :: rightTail => [rightHead :: rightTail]
  | leftHead :: leftTail, [] => [leftHead :: leftTail]
  | leftHead :: leftTail, rightHead :: rightTail =>
      (orderedListShuffles leftTail (rightHead :: rightTail)).map
          (List.cons leftHead) ++
        (orderedListShuffles (leftHead :: leftTail) rightTail).map
          (List.cons rightHead)

/-- Mapping vertex metadata to scalar phases commutes exactly with shuffling. -/
theorem map_orderedListShuffles
    {α : Type*} (phase : α → Real) :
    ∀ (left right : List α),
      (orderedListShuffles left right).map (List.map phase) =
        orderedPhaseShuffles (left.map phase) (right.map phase)
  | [], [] => by simp [orderedListShuffles]
  | [], rightHead :: rightTail => by
      simp [orderedListShuffles]
  | leftHead :: leftTail, [] => by
      simp [orderedListShuffles]
  | leftHead :: leftTail, rightHead :: rightTail => by
      have hleft := congrArg
        (List.map (List.cons (phase leftHead)))
        (map_orderedListShuffles phase
          leftTail (rightHead :: rightTail))
      have hright := congrArg
        (List.map (List.cons (phase rightHead)))
        (map_orderedListShuffles phase
          (leftHead :: leftTail) rightTail)
      simpa [orderedListShuffles, orderedPhaseShuffles,
        List.map_map, Function.comp_def] using
          congrArg₂ (fun left right => left ++ right) hleft hright
termination_by left right => left.length + right.length
decreasing_by all_goals simp

/-- Pairwise shuffling of two finite metadata-history families. -/
def shuffleListFamilies {α : Type*}
    (left right : List (List α)) : List (List α) :=
  left.flatMap fun leftHistory =>
    right.flatMap fun rightHistory =>
      orderedListShuffles leftHistory rightHistory

/-- Scalar phase mapping also commutes with family shuffling. -/
theorem map_shuffleListFamilies
    {α : Type*} (phase : α → Real)
    (left right : List (List α)) :
    (shuffleListFamilies left right).map (List.map phase) =
      shufflePhaseFamilies
        (left.map (List.map phase)) (right.map (List.map phase)) := by
  simp [shuffleListFamilies, shufflePhaseFamilies, List.map_flatMap,
    List.flatMap_map, map_orderedListShuffles]

/-- Metadata-preserving linear extensions of a decorated actual FPUT tree. -/
def randomEigenmodeBinaryTreeA1VertexLinearExtensions
    {N : Nat} [NeZero N] :
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) →
      List (List (ActualA1Vertex N))
  | .leaf _ => [[]]
  | .node output leftSign rightSign left right =>
      (shuffleListFamilies
        (randomEigenmodeBinaryTreeA1VertexLinearExtensions left)
        (randomEigenmodeBinaryTreeA1VertexLinearExtensions right)).map
          (List.cons
            (randomEigenmodeBinaryNodeA1Vertex
              output leftSign rightSign left right))

/-- The genuine scalar phase assignment obtained from all decorated nodes. -/
def randomEigenmodeBinaryTreeA1PhaseAssignment
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N) :
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) →
      BinaryInteractionTreePhaseAssignment tree.shape
  | .leaf _ => PUnit.unit
  | .node output leftSign rightSign left right =>
      ((randomEigenmodeBinaryNodeA1Vertex
          output leftSign rightSign left right).mismatch mass,
        (randomEigenmodeBinaryTreeA1PhaseAssignment mass left,
          randomEigenmodeBinaryTreeA1PhaseAssignment mass right))

/-- Forgetting metadata from the actual linear extensions gives exactly the
existing scalar branching linear extensions. -/
theorem map_randomEigenmodeBinaryTreeA1VertexLinearExtensions
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) :
    (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).map
        (List.map (ActualA1Vertex.mismatch mass)) =
      branchingPhaseLinearExtensions tree.shape
        (randomEigenmodeBinaryTreeA1PhaseAssignment mass tree) := by
  induction tree with
  | leaf mode =>
      rfl
  | node output leftSign rightSign left right hleft hright =>
      let vertex := randomEigenmodeBinaryNodeA1Vertex
        output leftSign rightSign left right
      have hshuffle := map_shuffleListFamilies
        (ActualA1Vertex.mismatch mass)
        (randomEigenmodeBinaryTreeA1VertexLinearExtensions left)
        (randomEigenmodeBinaryTreeA1VertexLinearExtensions right)
      rw [hleft, hright] at hshuffle
      have hcons := congrArg
        (List.map (List.cons (vertex.mismatch mass))) hshuffle
      simpa [randomEigenmodeBinaryTreeA1VertexLinearExtensions,
        randomEigenmodeBinaryTreeA1PhaseAssignment,
        branchingPhaseLinearExtensions, RandomEigenmodeBinaryTree.shape,
        vertex, List.map_map, Function.comp_def] using hcons

/-- Every actual metadata linear extension has exactly one vertex per tree
order. -/
theorem length_eq_order_of_mem_randomEigenmodeBinaryTreeA1VertexLinearExtensions
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    {history : List (ActualA1Vertex N)}
    (hhistory :
      history ∈ randomEigenmodeBinaryTreeA1VertexLinearExtensions tree) :
    history.length = tree.shape.order := by
  have hmapped :
      history.map (ActualA1Vertex.mismatch mass) ∈
        (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).map
          (List.map (ActualA1Vertex.mismatch mass)) :=
    List.mem_map.mpr ⟨history, hhistory, rfl⟩
  rw [map_randomEigenmodeBinaryTreeA1VertexLinearExtensions] at hmapped
  simpa using
    length_eq_order_of_mem_branchingPhaseLinearExtensions
      tree.shape (randomEigenmodeBinaryTreeA1PhaseAssignment mass tree) hmapped

/-- The actual metadata extension count inherits the established factorial
shape bound. -/
theorem length_randomEigenmodeBinaryTreeA1VertexLinearExtensions_le_factorial
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) :
    (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).length ≤
      tree.shape.order.factorial := by
  have hlength :
      (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).length =
        (branchingPhaseLinearExtensions tree.shape
          (randomEigenmodeBinaryTreeA1PhaseAssignment mass tree)).length := by
    simpa using congrArg List.length
      (map_randomEigenmodeBinaryTreeA1VertexLinearExtensions mass tree)
  rw [hlength]
  exact length_branchingPhaseLinearExtensions_le_factorial
    tree.shape (randomEigenmodeBinaryTreeA1PhaseAssignment mass tree)

/-! ## Exact heterogeneous interval charts -/

/-- Sum of the genuine, possibly different-output A1 vertices in an interval. -/
def actualA1VertexIntervalMismatch
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length) : Real :=
  ((interval.block history).map
    (ActualA1Vertex.mismatch mass)).sum

/-- The same heterogeneous interval as a genuine two-mass A1 chart. -/
def actualA1VertexIntervalPairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    (pair : Real × Real) : Real :=
  ((interval.block history).map fun vertex =>
    physlibA1PairMismatchChart fixed site₁ site₂
      vertex.observed vertex.term pair).sum

/-- Reindex an interval along an equality of displayed history lengths. -/
def reindexOrderedHistoryInterval
    {left right : Nat} (h : left = right)
    (interval : OrderedHistoryInterval left) :
    OrderedHistoryInterval right where
  start := interval.start
  stop := interval.stop
  start_lt_stop := interval.start_lt_stop
  stop_le := h ▸ interval.stop_le

/-- Every branching denominator occurrence has an exact metadata history and
a genuine heterogeneous contiguous interval. -/
theorem exists_actualA1VertexInterval_eq_branchingHistoryDenominator
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    {delta : Real}
    (hdelta : delta ∈ branchingHistoryDenominators tree.shape
      (randomEigenmodeBinaryTreeA1PhaseAssignment mass tree)) :
    ∃ history ∈ randomEigenmodeBinaryTreeA1VertexLinearExtensions tree,
      ∃ interval : OrderedHistoryInterval history.length,
        delta = actualA1VertexIntervalMismatch mass history interval := by
  rw [branchingHistoryDenominators, List.mem_flatMap] at hdelta
  rcases hdelta with ⟨phases, hphases, hdelta⟩
  have hphases' : phases ∈
      (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).map
        (List.map (ActualA1Vertex.mismatch mass)) := by
    rw [map_randomEigenmodeBinaryTreeA1VertexLinearExtensions]
    exact hphases
  rcases List.mem_map.mp hphases' with ⟨history, hhistory, hmap⟩
  obtain ⟨interval, hinterval⟩ :=
    exists_interval_eq_orderedHistoryDenominator phases hdelta
  have hlength : phases.length = history.length := by
    rw [← hmap]
    simp
  let interval' :=
    reindexOrderedHistoryInterval hlength interval
  refine ⟨history, hhistory, interval', ?_⟩
  rw [hinterval]
  simp [actualA1VertexIntervalMismatch, interval',
    reindexOrderedHistoryInterval, OrderedHistoryInterval.block, ← hmap]

/-- Finite selector: a linear-extension position and one distinct nonempty
interval endpoint pair in that extension. -/
abbrev ActualA1BranchingIntervalIndex
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) :=
  Σ extension : Fin
      (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).length,
    OrderedHistoryFiniteInterval
      ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get extension).length

/-- Direct actual mismatch coordinate selected by one finite index. -/
def actualA1BranchingIntervalMismatchCoordinate
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (index : ActualA1BranchingIntervalIndex tree) : Real :=
  actualA1VertexIntervalMismatch mass
    ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get index.1)
    index.2.toInterval

/-- The finite selector covers every occurrence of the complete branching
denominator list. -/
theorem exists_actualA1BranchingIntervalIndex_eq_denominator
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    {delta : Real}
    (hdelta : delta ∈ branchingHistoryDenominators tree.shape
      (randomEigenmodeBinaryTreeA1PhaseAssignment mass tree)) :
    ∃ index : ActualA1BranchingIntervalIndex tree,
      delta = actualA1BranchingIntervalMismatchCoordinate mass tree index := by
  obtain ⟨history, hhistory, interval, hinterval⟩ :=
    exists_actualA1VertexInterval_eq_branchingHistoryDenominator
      mass tree hdelta
  obtain ⟨extension, hextension⟩ := List.get_of_mem hhistory
  subst history
  refine ⟨⟨extension,
    orderedHistoryIntervalToFiniteInterval interval⟩, ?_⟩
  simpa [actualA1BranchingIntervalMismatchCoordinate,
    orderedHistoryIntervalToFiniteInterval_toInterval] using hinterval

/-- The selector has the advertised factorial-times-quadratic capacity. -/
theorem card_actualA1BranchingIntervalIndex_le
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) :
    Fintype.card (ActualA1BranchingIntervalIndex tree) ≤
      tree.shape.order.factorial *
        (tree.shape.order * tree.shape.order) := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ extension : Fin
        (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).length,
        Fintype.card (OrderedHistoryFiniteInterval
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            extension).length) ≤
      ∑ _extension : Fin
        (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).length,
        tree.shape.order * tree.shape.order := by
      gcongr with extension
      rw [length_eq_order_of_mem_randomEigenmodeBinaryTreeA1VertexLinearExtensions
        mass tree (List.get_mem _ extension)]
      exact card_orderedHistoryFiniteInterval_le_sq tree.shape.order
    _ = (randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).length *
        (tree.shape.order * tree.shape.order) := by simp
    _ ≤ tree.shape.order.factorial *
        (tree.shape.order * tree.shape.order) := by
      exact Nat.mul_le_mul_right _
        (length_randomEigenmodeBinaryTreeA1VertexLinearExtensions_le_factorial
          mass tree)

/-! ## Occurrence-dependent retained fibers -/

/-- Reinsert the masses already present at two distinct supported sites. -/
theorem twoSiteMassConfig_self
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (hsupport : ∀ site, mass.mass site ∈ massSupport) :
    twoSiteMassConfig mass site₁ site₂
        (mass.mass site₁, mass.mass site₂) = mass := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  by_cases hfirst : site = site₁
  · subst site
    simp [twoSiteMassConfig,
      clippedMass_eq_self (hsupport site₁)]
  · by_cases hsecond : site = site₂
    · subst site
      simp [twoSiteMassConfig, hsite.symm,
        clippedMass_eq_self (hsupport site₂)]
    · simp [twoSiteMassConfig, hfirst, hsecond]

/-- At the original realization, the pair chart equals the same actual local
mismatch for every occurrence-specific retained pair. -/
theorem actualA1Vertex_pairMismatchChart_self
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (hsupport : ∀ site, mass.mass site ∈ massSupport)
    (vertex : ActualA1Vertex N) :
    physlibA1PairMismatchChart mass site₁ site₂
        vertex.observed vertex.term
        (mass.mass site₁, mass.mass site₂) =
      vertex.mismatch mass := by
  rw [physlibA1PairMismatchChart, ActualA1Vertex.mismatch,
    twoSiteMassConfig_self mass hsite hsupport]

/-- A finite choice of retained mass pair for every denominator coordinate. -/
structure ActualA1BranchingOccurrenceFiberChoice
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) where
  site₁ : ActualA1BranchingIntervalIndex tree → Lattice.Site N
  site₂ : ActualA1BranchingIntervalIndex tree → Lattice.Site N
  sites_ne : ∀ index, site₁ index ≠ site₂ index

/-- Heterogeneous interval chart evaluated at its occurrence-specific pair in
the original mass realization. -/
def actualA1BranchingOccurrenceFiberValue
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberChoice tree)
    (index : ActualA1BranchingIntervalIndex tree) : Real :=
  actualA1VertexIntervalPairMismatchChart mass
    (fiber.site₁ index) (fiber.site₂ index)
    ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get index.1)
    index.2.toInterval
    (mass.mass (fiber.site₁ index), mass.mass (fiber.site₂ index))

/-- Every complete branching denominator occurrence is covered by the finite
selector even when the retained pair depends on the occurrence. -/
theorem exists_actualA1BranchingOccurrenceFiberValue_eq_denominator
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (hsupport : ∀ site, mass.mass site ∈ massSupport)
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberChoice tree)
    {delta : Real}
    (hdelta : delta ∈ branchingHistoryDenominators tree.shape
      (randomEigenmodeBinaryTreeA1PhaseAssignment mass tree)) :
    ∃ index : ActualA1BranchingIntervalIndex tree,
      delta = actualA1BranchingOccurrenceFiberValue mass tree fiber index := by
  obtain ⟨index, hindex⟩ :=
    exists_actualA1BranchingIntervalIndex_eq_denominator mass tree hdelta
  refine ⟨index, hindex.trans ?_⟩
  unfold actualA1BranchingIntervalMismatchCoordinate
    actualA1BranchingOccurrenceFiberValue
    actualA1VertexIntervalMismatch
    actualA1VertexIntervalPairMismatchChart
  apply congrArg List.sum
  apply List.map_congr_left
  intro vertex hvertex
  exact (actualA1Vertex_pairMismatchChart_self mass
    (fiber.sites_ne index) hsupport vertex).symm

/-! ### A literal covers interface for varying mass families -/

/-- Occurrence-dependent two-site charts can still cover one common scalar
mass path when every selected chart explicitly reconstructs that same path.
The retained sites, the frozen background, and the first coordinate may all
depend on the denominator occurrence.  The realizes field is the exact
compatibility condition required by the old single-parameter covers
signature; it is not inferred from the branching tree. -/
structure ActualA1BranchingOccurrenceFiberFamily
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N)) where
  massFamily : Real → Lattice.PositiveMassConfig N
  fixed :
    ActualA1BranchingIntervalIndex tree → Lattice.PositiveMassConfig N
  site₁ : ActualA1BranchingIntervalIndex tree → Lattice.Site N
  site₂ : ActualA1BranchingIntervalIndex tree → Lattice.Site N
  sites_ne : ∀ index, site₁ index ≠ site₂ index
  first : ActualA1BranchingIntervalIndex tree → Real
  realizes : ∀ index second,
    twoSiteMassConfig (fixed index) (site₁ index) (site₂ index)
        (first index, second) =
      massFamily second

/-- A common two-site mass path gives a nonvacuous constant instance of the
occurrence-dependent family interface. -/
def constantActualA1BranchingOccurrenceFiberFamily
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (first : Real) :
    ActualA1BranchingOccurrenceFiberFamily tree where
  massFamily := fun second =>
    twoSiteMassConfig fixed site₁ site₂ (first, second)
  fixed := fun _ => fixed
  site₁ := fun _ => site₁
  site₂ := fun _ => site₂
  sites_ne := fun _ => hsite
  first := fun _ => first
  realizes := by intros; rfl

/-- Heterogeneous actual interval chart on the occurrence's retained pair. -/
def actualA1BranchingOccurrenceFiberCoordinate
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (index : ActualA1BranchingIntervalIndex tree)
    (second : Real) : Real :=
  actualA1VertexIntervalPairMismatchChart
    (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
    ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get index.1)
    index.2.toInterval (fiber.first index, second)

/-- The occurrence chart is exactly the direct interval mismatch along the
common reconstructed mass path. -/
theorem actualA1BranchingOccurrenceFiberCoordinate_eq_actual
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (index : ActualA1BranchingIntervalIndex tree)
    (second : Real) :
    actualA1BranchingOccurrenceFiberCoordinate tree fiber index second =
      actualA1BranchingIntervalMismatchCoordinate
        (fiber.massFamily second) tree index := by
  unfold actualA1BranchingOccurrenceFiberCoordinate
    actualA1BranchingIntervalMismatchCoordinate
    actualA1VertexIntervalPairMismatchChart
    actualA1VertexIntervalMismatch
  apply congrArg List.sum
  apply List.map_congr_left
  intro vertex hvertex
  simp only [physlibA1PairMismatchChart, ActualA1Vertex.mismatch]
  rw [fiber.realizes index second]

/-- Literal covers statement for every scalar parameter.  Unlike the old
fixed-observed selector, these coordinates retain the genuine output mode of
each vertex. -/
theorem actualA1BranchingOccurrenceFiberCoordinate_covers
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (second delta : Real)
    (hdelta : delta ∈ branchingHistoryDenominators tree.shape
      (randomEigenmodeBinaryTreeA1PhaseAssignment
        (fiber.massFamily second) tree)) :
    ∃ index : ActualA1BranchingIntervalIndex tree,
      delta =
        actualA1BranchingOccurrenceFiberCoordinate
          tree fiber index second := by
  obtain ⟨index, hindex⟩ :=
    exists_actualA1BranchingIntervalIndex_eq_denominator
      (fiber.massFamily second) tree hdelta
  exact ⟨index, hindex.trans
    (actualA1BranchingOccurrenceFiberCoordinate_eq_actual
      tree fiber index second).symm⟩

/-! ### Explicit analytic obstruction after algebraic coverage -/

/-- Sum of actual vertical Jacobians for a heterogeneous-output interval.
Establishing a positive lower bound for this sum is the remaining spectral
noncancellation problem; individual one-vertex bounds do not imply it. -/
def actualA1VertexIntervalVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    (pair : Real × Real) : Real :=
  ((interval.block history).map fun vertex =>
    physlibA1PairMismatchVerticalJacobian fixed site₁ site₂
      vertex.observed vertex.term pair).sum

/-- Honest fixed-order missing input: every selected heterogeneous denominator
has an occurrence-dependent compact set and a positive lower bound on its
total actual vertical Jacobian.  This definition makes the possible
co-degeneration set explicit; no such bound is proved globally here. -/
def ActualA1BranchingOccurrenceJacobianNoncancellation
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (compact : ActualA1BranchingIntervalIndex tree → Set (Real × Real))
    (j0 : ActualA1BranchingIntervalIndex tree → Real) : Prop :=
  ∀ index, 0 < j0 index ∧
    ∀ pair ∈ compact index,
      j0 index ≤
        |actualA1VertexIntervalVerticalJacobian
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval pair|

/-! ## Exact boundary of the fixed-observed selector -/

/-- A history can use the old interval chart without changing its vertices
when all selected vertices have the same output mode. -/
def ObservedHomogeneous
    {N : Nat} (observed : Lattice.Site N)
    (history : List (ActualA1Vertex N)) : Prop :=
  ∀ vertex ∈ history, vertex.observed = observed

/-- Two distinct output modes already obstruct faithful fixed-observed
encoding of the corresponding two-vertex history. -/
theorem not_observedHomogeneous_pair
    {N : Nat} [NeZero N]
    {first second : ActualA1Vertex N}
    (hne : first.observed ≠ second.observed) :
    ¬ ∃ observed, ObservedHomogeneous observed [first, second] := by
  rintro ⟨observed, hhomogeneous⟩
  apply hne
  exact (hhomogeneous first (by simp)).trans
    (hhomogeneous second (by simp)).symm

/-- On a homogeneous-output block, the heterogeneous chart reduces exactly to
the prior fixed-observed interval chart. -/
theorem actualA1VertexIntervalPairMismatchChart_eq_fixedObserved
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    (hhomogeneous :
      ObservedHomogeneous observed (interval.block history))
    (pair : Real × Real) :
    actualA1VertexIntervalPairMismatchChart
        fixed site₁ site₂ history interval pair =
      physlibA1OrderedHistoryIntervalPairMismatchChart
        fixed site₁ site₂ observed (history.map ActualA1Vertex.term)
          (reindexOrderedHistoryInterval (by simp) interval) pair := by
  rw [physlibA1OrderedHistoryIntervalPairMismatchChart_eq_block_sum]
  simp only [actualA1VertexIntervalPairMismatchChart,
    physlibA1OrderedHistoryListLocalPhaseList,
    OrderedHistoryInterval.block, reindexOrderedHistoryInterval,
    List.map_map]
  simp only [← List.map_take, ← List.map_drop]
  apply congrArg List.sum
  apply List.map_congr_left
  intro vertex hvertex
  rw [hhomogeneous vertex]
  · rfl
  · exact hvertex

end

end ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector
