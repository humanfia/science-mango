import ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall
import ArchonPhysics.RandomBranchingSmallDenominatorUnion

/-!
# Deduplicated compact-atlas bounds for complete ordered histories

Every denominator occurrence in a linear ordered history is a contiguous
interval sum.  Since repeating the same interval does not change a union of
bad events, this file indexes the full event by distinct endpoint pairs rather
than by the `2^r - 1` recursive occurrences.  At order `r` the finite interval
index has cardinality at most `r^2` (in fact `r(r+1)/2`), so the uniform
compact-atlas coefficient has a transparent quadratic bound.

The principal estimate charges the union of compact complements once:

`P(any recursive denominator is small)`
`  ≤ (sum over intervals of atlas coefficients) * ofReal(2 gamma)`
`      + P(union over intervals of K_intervalᶜ)`.

For a branching tree, an explicit selector interface records actual A1
interval charts and proves that they cover every branching denominator.  No
such selector is constructed here: in particular, a common retained fiber
across branches is not inferred from the scalar phase assignment.  Once a
selector and per-coordinate atlases are supplied, the same finite-union bound
applies with its displayed selector capacity.  No independence, re-Haar,
Markov closure, RPA, or recollision decay is used.
-/

namespace ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomBranchingSmallDenominatorUnion
open MeasureTheory Set

noncomputable section

/-- Finite index of nonempty inclusive endpoint pairs `left ≤ right`. -/
abbrev OrderedHistoryFiniteInterval (order : Nat) :=
  { endpoints : Fin order × Fin order // endpoints.1 ≤ endpoints.2 }

/-- Convert finite inclusive endpoints to the concrete half-open interval
`[left, right + 1)`. -/
def OrderedHistoryFiniteInterval.toInterval
    {order : Nat} (interval : OrderedHistoryFiniteInterval order) :
    OrderedHistoryInterval order :=
  { start := interval.1.1.1
    stop := interval.1.2.1 + 1
    start_lt_stop := Nat.lt_succ_of_le interval.2
    stop_le := interval.1.2.2 }

/-- Every concrete interval has a finite inclusive-endpoint representative. -/
def orderedHistoryIntervalToFiniteInterval
    {order : Nat} (interval : OrderedHistoryInterval order) :
    OrderedHistoryFiniteInterval order :=
  ⟨(⟨interval.start, by
        exact lt_of_lt_of_le interval.start_lt_stop interval.stop_le⟩,
      ⟨interval.stop - 1, by
        have hstopPos : 0 < interval.stop :=
          lt_of_le_of_lt (Nat.zero_le interval.start) interval.start_lt_stop
        exact lt_of_lt_of_le (Nat.sub_lt hstopPos (by decide)) interval.stop_le⟩), by
    simp only [Fin.mk_le_mk]
    exact Nat.le_sub_one_of_lt interval.start_lt_stop⟩

/-- Endpoint conversion loses no concrete interval. -/
theorem orderedHistoryIntervalToFiniteInterval_toInterval
    {order : Nat} (interval : OrderedHistoryInterval order) :
    (orderedHistoryIntervalToFiniteInterval interval).toInterval = interval := by
  cases interval with
  | mk start stop start_lt_stop stop_le =>
      have hstopPos : 0 < stop :=
        lt_of_le_of_lt (Nat.zero_le start) start_lt_stop
      simp [orderedHistoryIntervalToFiniteInterval,
        OrderedHistoryFiniteInterval.toInterval,
        Nat.sub_add_cancel (Nat.succ_le_iff.mpr hstopPos)]

/-- The number of distinct interval locations is at most the number of all
ordered endpoint pairs. -/
theorem card_orderedHistoryFiniteInterval_le_sq (order : Nat) :
    Fintype.card (OrderedHistoryFiniteInterval order) ≤ order * order := by
  simpa [OrderedHistoryFiniteInterval] using
    Fintype.card_subtype_le
      (fun endpoints : Fin order × Fin order => endpoints.1 ≤ endpoints.2)

/-! ## Generic finite compact-atlas union -/

/-- Compact exceptional union for an arbitrary finite coordinate family. -/
def finiteCoordinateCompactAtlasBadEvent
    {Index : Type*} [Fintype Index]
    (coordinate : Index → Real → Real)
    (certificate : ∀ i : Index,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i)) : Set Real :=
  ⋃ i, (certificate i).compactSetᶜ

/-- Sum of the actual finite-atlas density coefficients. -/
def finiteCoordinateCompactAtlasRegularCoefficient
    {Index : Type*} [Fintype Index]
    (coordinate : Index → Real → Real)
    (certificate : ∀ i : Index,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i)) : ENNReal :=
  ∑ i, (certificate i).regularCoefficient

/-- Any event covered by a finite coordinate small-gap union inherits the
compact-atlas bound, with the compact exceptional union charged once. -/
theorem measure_event_le_finiteCoordinateCompactAtlas
    {Index : Type*} [Fintype Index]
    (event : Set Real) (coordinate : Index → Real → Real)
    (certificate : ∀ i : Index,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i))
    (gamma : Real)
    (hcover : event ⊆ finiteSmallDenominatorEvent coordinate gamma) :
    massCoordinateLaw event ≤
      finiteCoordinateCompactAtlasRegularCoefficient coordinate certificate *
          ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent coordinate certificate) := by
  classical
  let bad := finiteCoordinateCompactAtlasBadEvent coordinate certificate
  let goodNear : Index → Set Real := fun i =>
    coordinate i ⁻¹' Ioo (-gamma) gamma ∩ (certificate i).compactSet
  have hsubset : event ⊆ bad ∪ ⋃ i, goodNear i := by
    intro second hsecond
    have hfinite := hcover hsecond
    rw [mem_finiteSmallDenominatorEvent_iff] at hfinite
    rcases hfinite with ⟨i, hsmall⟩
    by_cases hbad : second ∈ bad
    · exact Or.inl hbad
    · apply Or.inr
      rw [mem_iUnion]
      refine ⟨i, abs_lt.mp hsmall, ?_⟩
      by_contra hnotK
      exact hbad (mem_iUnion.mpr ⟨i, hnotK⟩)
  have hgood : ∀ i,
      massCoordinateLaw (goodNear i) ≤
        (certificate i).regularCoefficient *
          ENNReal.ofReal (2 * gamma) := by
    intro i
    exact measure_coordinateCompactAtlasGoodNear_le
      (certificate i) gamma
  calc
    massCoordinateLaw event ≤ massCoordinateLaw (bad ∪ ⋃ i, goodNear i) :=
      measure_mono hsubset
    _ ≤ massCoordinateLaw bad + massCoordinateLaw (⋃ i, goodNear i) :=
      measure_union_le _ _
    _ ≤ massCoordinateLaw bad + ∑' i, massCoordinateLaw (goodNear i) := by
      gcongr
      exact measure_iUnion_le _
    _ ≤ massCoordinateLaw bad +
        ∑ i, (certificate i).regularCoefficient *
          ENNReal.ofReal (2 * gamma) := by
      simp only [tsum_fintype]
      gcongr with i
      exact hgood i
    _ = finiteCoordinateCompactAtlasRegularCoefficient
          coordinate certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw bad := by
      unfold finiteCoordinateCompactAtlasRegularCoefficient
      rw [Finset.sum_mul]
      ac_rfl

/-! ## One complete linear ordered history, deduplicated by intervals -/

/-- Actual coordinate of one finite interval in a fixed linear A1 history. -/
def physlibA1OrderedHistoryFiniteIntervalCoordinate
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first : Real)
    (interval : OrderedHistoryFiniteInterval term.length)
    (second : Real) : Real :=
  physlibA1OrderedHistoryIntervalPairMismatchChart
    fixed site₁ site₂ observed term interval.toInterval (first, second)

/-- The full recursive small-denominator event for one actual ordered
history.  Occurrence repetitions are retained in this definition. -/
def physlibA1OrderedHistoryRecursiveSmallDenominatorEvent
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first gamma : Real) : Set Real :=
  {second | ∃ delta ∈ orderedHistoryDenominators
      (physlibA1OrderedHistoryListLocalPhaseList
        fixed site₁ site₂ observed term (first, second)),
      |delta| < gamma}

/-- Every recursive occurrence event is covered by the deduplicated finite
interval family. -/
theorem physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_subset_intervals
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first gamma : Real) :
    physlibA1OrderedHistoryRecursiveSmallDenominatorEvent
        fixed site₁ site₂ observed term first gamma ⊆
      finiteSmallDenominatorEvent
        (physlibA1OrderedHistoryFiniteIntervalCoordinate
          fixed site₁ site₂ observed term first) gamma := by
  intro second hsecond
  rcases hsecond with ⟨delta, hdelta, hsmall⟩
  obtain ⟨interval, hinterval⟩ :=
    exists_intervalChart_eq_physlibA1OrderedHistoryDenominator
      fixed site₁ site₂ observed term (first, second) hdelta
  rw [mem_finiteSmallDenominatorEvent_iff]
  refine ⟨orderedHistoryIntervalToFiniteInterval interval, ?_⟩
  simpa [physlibA1OrderedHistoryFiniteIntervalCoordinate,
    orderedHistoryIntervalToFiniteInterval_toInterval,
    ← hinterval] using hsmall

/-- Restrict an all-concrete-interval certificate family to the finite
deduplicated endpoint index. -/
def physlibA1OrderedHistoryFiniteIntervalCertificate
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first : Real)
    (certificate : ∀ interval : OrderedHistoryInterval term.length,
      OrdinaryGardenCoordinateCompactAtlas
        (fun second =>
          physlibA1OrderedHistoryIntervalPairMismatchChart
            fixed site₁ site₂ observed term interval (first, second)))
    (interval : OrderedHistoryFiniteInterval term.length) :
    OrdinaryGardenCoordinateCompactAtlas
      (physlibA1OrderedHistoryFiniteIntervalCoordinate
        fixed site₁ site₂ observed term first interval) :=
  certificate interval.toInterval

/-- Explicit full ordered-history bad-set bound after deduplicating all
recursive occurrences to distinct interval locations. -/
theorem measure_physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first gamma : Real)
    (certificate : ∀ interval : OrderedHistoryInterval term.length,
      OrdinaryGardenCoordinateCompactAtlas
        (fun second =>
          physlibA1OrderedHistoryIntervalPairMismatchChart
            fixed site₁ site₂ observed term interval (first, second))) :
    massCoordinateLaw
        (physlibA1OrderedHistoryRecursiveSmallDenominatorEvent
          fixed site₁ site₂ observed term first gamma) ≤
      finiteCoordinateCompactAtlasRegularCoefficient
          (physlibA1OrderedHistoryFiniteIntervalCoordinate
            fixed site₁ site₂ observed term first)
          (physlibA1OrderedHistoryFiniteIntervalCertificate
            fixed site₁ site₂ observed term first certificate) *
            ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            (physlibA1OrderedHistoryFiniteIntervalCoordinate
              fixed site₁ site₂ observed term first)
            (physlibA1OrderedHistoryFiniteIntervalCertificate
              fixed site₁ site₂ observed term first certificate)) := by
  exact measure_event_le_finiteCoordinateCompactAtlas
    (physlibA1OrderedHistoryRecursiveSmallDenominatorEvent
      fixed site₁ site₂ observed term first gamma)
    (physlibA1OrderedHistoryFiniteIntervalCoordinate
      fixed site₁ site₂ observed term first)
    (physlibA1OrderedHistoryFiniteIntervalCertificate
      fixed site₁ site₂ observed term first certificate)
    gamma
    (physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_subset_intervals
      fixed site₁ site₂ observed term first gamma)

/-- The summed regular coefficient has the explicit quadratic fixed-order
bound when every interval certificate has coefficient at most `budget`. -/
theorem physlibA1OrderedHistoryFiniteIntervalRegularCoefficient_le_sq_mul
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first : Real)
    (certificate : ∀ interval : OrderedHistoryInterval term.length,
      OrdinaryGardenCoordinateCompactAtlas
        (fun second =>
          physlibA1OrderedHistoryIntervalPairMismatchChart
            fixed site₁ site₂ observed term interval (first, second)))
    (budget : ENNReal)
    (hbudget : ∀ interval : OrderedHistoryFiniteInterval term.length,
      (certificate interval.toInterval).regularCoefficient ≤ budget) :
    finiteCoordinateCompactAtlasRegularCoefficient
        (physlibA1OrderedHistoryFiniteIntervalCoordinate
          fixed site₁ site₂ observed term first)
        (physlibA1OrderedHistoryFiniteIntervalCertificate
          fixed site₁ site₂ observed term first certificate) ≤
      (term.length * term.length : Nat) * budget := by
  calc
    finiteCoordinateCompactAtlasRegularCoefficient
        (physlibA1OrderedHistoryFiniteIntervalCoordinate
          fixed site₁ site₂ observed term first)
        (physlibA1OrderedHistoryFiniteIntervalCertificate
          fixed site₁ site₂ observed term first certificate) ≤
      ∑ _interval : OrderedHistoryFiniteInterval term.length, budget := by
        unfold finiteCoordinateCompactAtlasRegularCoefficient
        gcongr with interval
        exact hbudget interval
    _ = (Fintype.card (OrderedHistoryFiniteInterval term.length) : ENNReal) *
        budget := by simp
    _ ≤ (term.length * term.length : Nat) * budget := by
      gcongr
      exact_mod_cast card_orderedHistoryFiniteInterval_le_sq term.length

/-- Uniform quadratic specialization of the full bad-set estimate. -/
theorem measure_physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_le_sq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first gamma : Real)
    (certificate : ∀ interval : OrderedHistoryInterval term.length,
      OrdinaryGardenCoordinateCompactAtlas
        (fun second =>
          physlibA1OrderedHistoryIntervalPairMismatchChart
            fixed site₁ site₂ observed term interval (first, second)))
    (budget : ENNReal)
    (hbudget : ∀ interval : OrderedHistoryFiniteInterval term.length,
      (certificate interval.toInterval).regularCoefficient ≤ budget) :
    massCoordinateLaw
        (physlibA1OrderedHistoryRecursiveSmallDenominatorEvent
          fixed site₁ site₂ observed term first gamma) ≤
      ((term.length * term.length : Nat) * budget) *
          ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            (physlibA1OrderedHistoryFiniteIntervalCoordinate
              fixed site₁ site₂ observed term first)
            (physlibA1OrderedHistoryFiniteIntervalCertificate
              fixed site₁ site₂ observed term first certificate)) := by
  calc
    massCoordinateLaw
        (physlibA1OrderedHistoryRecursiveSmallDenominatorEvent
          fixed site₁ site₂ observed term first gamma) ≤
      finiteCoordinateCompactAtlasRegularCoefficient
          (physlibA1OrderedHistoryFiniteIntervalCoordinate
            fixed site₁ site₂ observed term first)
          (physlibA1OrderedHistoryFiniteIntervalCertificate
            fixed site₁ site₂ observed term first certificate) *
            ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            (physlibA1OrderedHistoryFiniteIntervalCoordinate
              fixed site₁ site₂ observed term first)
            (physlibA1OrderedHistoryFiniteIntervalCertificate
              fixed site₁ site₂ observed term first certificate)) :=
      measure_physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_le
        fixed site₁ site₂ observed term first gamma certificate
    _ ≤ ((term.length * term.length : Nat) * budget) *
          ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            (physlibA1OrderedHistoryFiniteIntervalCoordinate
              fixed site₁ site₂ observed term first)
            (physlibA1OrderedHistoryFiniteIntervalCertificate
              fixed site₁ site₂ observed term first certificate)) := by
      gcongr
      exact physlibA1OrderedHistoryFiniteIntervalRegularCoefficient_le_sq_mul
        fixed site₁ site₂ observed term first certificate budget hbudget

/-! ## Explicit compatibility boundary for a random branching history -/

/-- Fixed-tree selector budget after deduplicating interval coordinates in
each linear extension.  Taking the minimum with the established occurrence
budget means that the quadratic endpoint estimate never worsens the original
`2 ^ order - 1` count. -/
def branchingDeduplicatedIntervalCapacity
    (tree :
      ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples.BinaryInteractionTree) :
    Nat :=
  min (branchingDenominatorCapacity tree)
    (tree.order.factorial * (tree.order * tree.order))

/-- Smallest actual-chart selector used here for a branching phase assignment.
Each selected coordinate records its own genuine A1 interval chart.  The
`covers` field is the nontrivial branching/fiber compatibility input; it is
not constructed from `BinaryInteractionTreePhaseAssignment`. -/
structure RandomBranchingA1IntervalFiberSelector
    {N : Nat} [NeZero N]
    (tree :
      ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples.BinaryInteractionTree)
    (assignment : Real → BinaryInteractionTreePhaseAssignment tree) where
  capacity : Nat
  fixed : Fin capacity → Lattice.PositiveMassConfig N
  site₁ : Fin capacity → Lattice.Site N
  site₂ : Fin capacity → Lattice.Site N
  observed : Fin capacity → Lattice.Site N
  first : Fin capacity → Real
  term : Fin capacity → List (QuadraticPhaseTerm N)
  interval : ∀ i, OrderedHistoryInterval (term i).length
  coordinate : Fin capacity → Real → Real
  coordinate_eq_actual : ∀ i second,
    coordinate i second =
      physlibA1OrderedHistoryIntervalPairMismatchChart
        (fixed i) (site₁ i) (site₂ i) (observed i)
          (term i) (interval i) (first i, second)
  covers : ∀ second delta,
    delta ∈ branchingHistoryDenominators tree (assignment second) →
      ∃ i, delta = coordinate i second

/-- A supplied actual branching selector and compact atlases control the full
branching bad event.  Its capacity is displayed rather than replaced by an
unproved Catalan/factorial compatibility count. -/
theorem measure_randomBranchingSmallEvent_le_selectedIntervalCompactAtlas
    {N : Nat} [NeZero N]
    (tree :
      ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples.BinaryInteractionTree)
    (assignment : Real → BinaryInteractionTreePhaseAssignment tree)
    (selector :
      RandomBranchingA1IntervalFiberSelector (N := N) tree assignment)
    (certificate : ∀ i : Fin selector.capacity,
      OrdinaryGardenCoordinateCompactAtlas (selector.coordinate i))
    (gamma : Real) :
    massCoordinateLaw {second | ∃ delta ∈
        branchingHistoryDenominators tree (assignment second),
          |delta| < gamma} ≤
      finiteCoordinateCompactAtlasRegularCoefficient
          selector.coordinate certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            selector.coordinate certificate) := by
  apply measure_event_le_finiteCoordinateCompactAtlas
  intro second hsecond
  rcases hsecond with ⟨delta, hdelta, hsmall⟩
  obtain ⟨i, hi⟩ := selector.covers second delta hdelta
  rw [mem_finiteSmallDenominatorEvent_iff]
  exact ⟨i, by simpa [← hi] using hsmall⟩

/-- If every selected actual interval chart has regular coefficient at most
`budget`, a selector whose size obeys the deduplicated fixed-tree budget has
the corresponding explicit summed coefficient bound.  The size hypothesis is
part of the branching/fiber compatibility input, not a constructed selector. -/
theorem randomBranchingSelectedIntervalRegularCoefficient_le_deduplicated
    {N : Nat} [NeZero N]
    (tree :
      ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples.BinaryInteractionTree)
    (assignment : Real → BinaryInteractionTreePhaseAssignment tree)
    (selector :
      RandomBranchingA1IntervalFiberSelector (N := N) tree assignment)
    (certificate : ∀ i : Fin selector.capacity,
      OrdinaryGardenCoordinateCompactAtlas (selector.coordinate i))
    (budget : ENNReal)
    (hcapacity : selector.capacity ≤
      branchingDeduplicatedIntervalCapacity tree)
    (hbudget : ∀ i, (certificate i).regularCoefficient ≤ budget) :
    finiteCoordinateCompactAtlasRegularCoefficient
        selector.coordinate certificate ≤
      (branchingDeduplicatedIntervalCapacity tree : ENNReal) * budget := by
  calc
    finiteCoordinateCompactAtlasRegularCoefficient
        selector.coordinate certificate ≤
      ∑ _i : Fin selector.capacity, budget := by
        unfold finiteCoordinateCompactAtlasRegularCoefficient
        gcongr with i
        exact hbudget i
    _ = (selector.capacity : ENNReal) * budget := by simp
    _ ≤ (branchingDeduplicatedIntervalCapacity tree : ENNReal) * budget := by
      gcongr

/-- Explicit fixed-order branching bad-set bound.  It requires both the
actual-chart coverage selector and its honest deduplicated-capacity proof;
neither common-fiber compatibility nor branching recollision control is
derived here. -/
theorem measure_randomBranchingSmallEvent_le_deduplicatedIntervalBudget
    {N : Nat} [NeZero N]
    (tree :
      ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples.BinaryInteractionTree)
    (assignment : Real → BinaryInteractionTreePhaseAssignment tree)
    (selector :
      RandomBranchingA1IntervalFiberSelector (N := N) tree assignment)
    (certificate : ∀ i : Fin selector.capacity,
      OrdinaryGardenCoordinateCompactAtlas (selector.coordinate i))
    (gamma : Real) (budget : ENNReal)
    (hcapacity : selector.capacity ≤
      branchingDeduplicatedIntervalCapacity tree)
    (hbudget : ∀ i, (certificate i).regularCoefficient ≤ budget) :
    massCoordinateLaw {second | ∃ delta ∈
        branchingHistoryDenominators tree (assignment second),
          |delta| < gamma} ≤
      ((branchingDeduplicatedIntervalCapacity tree : ENNReal) * budget) *
          ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            selector.coordinate certificate) := by
  calc
    massCoordinateLaw {second | ∃ delta ∈
        branchingHistoryDenominators tree (assignment second),
          |delta| < gamma} ≤
      finiteCoordinateCompactAtlasRegularCoefficient
          selector.coordinate certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            selector.coordinate certificate) :=
      measure_randomBranchingSmallEvent_le_selectedIntervalCompactAtlas
        tree assignment selector certificate gamma
    _ ≤ ((branchingDeduplicatedIntervalCapacity tree : ENNReal) * budget) *
          ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            selector.coordinate certificate) := by
      gcongr
      exact randomBranchingSelectedIntervalRegularCoefficient_le_deduplicated
        tree assignment selector certificate budget hcapacity hbudget

end

end ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound
