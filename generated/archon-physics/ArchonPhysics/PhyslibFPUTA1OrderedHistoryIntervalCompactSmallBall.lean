import ArchonPhysics.PhyslibFPUTA1OrderedHistoryPrefixCompactSmallBall

/-!
# Actual compact atlases for every linear ordered-history interval denominator

The complete ordered integration-by-parts recursion contains more than the
root-prefix cumulative phases.  This file proves the exact missing structural
fact: every entry of `orderedHistoryDenominators` is the sum of one nonempty
contiguous interval of the original linear phase list.  Repetitions remain;
the recursive list has `2^r - 1` occurrences while the set of interval
locations is only quadratic in `r`.

For a list of genuine `QuadraticPhaseTerm` vertices evaluated on one explicitly
shared retained mass pair, every contiguous interval is turned into an actual
cumulative A1 chart.  Its vertical derivative is the sum of the actual
vertical Jacobians in that interval.  Independent compact sets and honest
lower bounds on those total interval Jacobians then give a compact-atlas
certificate for every interval.

The common fiber is an input to these linear-history statements: all terms are
evaluated using the displayed `site₁`, `site₂`, and retained first coordinate.
No compatibility theorem for different branches is asserted.  A branching
garden still needs a selector proving that the terms assigned to each
denominator share a chosen fiber before this endpoint can be used.  There is
also no re-Haar, Markov, RPA, or recollision-decay conclusion here.
-/

namespace ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryPrefixCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open Function MeasureTheory Set

noncomputable section

/-- A nonempty prefix sum of an ordered phase list. -/
inductive OrderedHistoryNonemptyPrefixSum : List Real → Real → Prop
  | head (delta : Real) (tail : List Real) :
      OrderedHistoryNonemptyPrefixSum (delta :: tail) delta
  | extend (delta : Real) {tail : List Real} {prefixSum : Real}
      (hprefix : OrderedHistoryNonemptyPrefixSum tail prefixSum) :
      OrderedHistoryNonemptyPrefixSum (delta :: tail) (delta + prefixSum)

/-- A sum over a nonempty contiguous interval: either a prefix of the current
list or an interval shifted past its head. -/
inductive OrderedHistoryContiguousIntervalSum : List Real → Real → Prop
  | fromPrefix {phases : List Real} {delta : Real}
      (hprefix : OrderedHistoryNonemptyPrefixSum phases delta) :
      OrderedHistoryContiguousIntervalSum phases delta
  | shift (head : Real) {tail : List Real} {delta : Real}
      (hinterval : OrderedHistoryContiguousIntervalSum tail delta) :
      OrderedHistoryContiguousIntervalSum (head :: tail) delta

/-- Merging the first two phases preserves the interval interpretation: an
interval beginning at the merged head expands to the first two original
vertices, while a shifted interval is unchanged and shifted twice. -/
theorem orderedHistoryNonemptyPrefixSum_unmerge_head
    {deltaOne deltaTwo : Real} {tail : List Real} {delta : Real}
    (hprefix : OrderedHistoryNonemptyPrefixSum
      ((deltaOne + deltaTwo) :: tail) delta) :
    OrderedHistoryNonemptyPrefixSum
      (deltaOne :: deltaTwo :: tail) delta := by
  cases hprefix with
  | head =>
      exact OrderedHistoryNonemptyPrefixSum.extend deltaOne
        (OrderedHistoryNonemptyPrefixSum.head deltaTwo tail)
  | extend _ htail =>
      simpa [add_assoc] using
        (OrderedHistoryNonemptyPrefixSum.extend deltaOne
          (OrderedHistoryNonemptyPrefixSum.extend deltaTwo htail))

/-- Interval-level version of unmerging the first two phases. -/
theorem orderedHistoryContiguousIntervalSum_unmerge_head
    {deltaOne deltaTwo : Real} {tail : List Real} {delta : Real}
    (hinterval : OrderedHistoryContiguousIntervalSum
      ((deltaOne + deltaTwo) :: tail) delta) :
    OrderedHistoryContiguousIntervalSum
      (deltaOne :: deltaTwo :: tail) delta := by
  cases hinterval with
  | fromPrefix hprefix =>
      exact OrderedHistoryContiguousIntervalSum.fromPrefix
        (orderedHistoryNonemptyPrefixSum_unmerge_head hprefix)
  | shift _ htail =>
      exact OrderedHistoryContiguousIntervalSum.shift deltaOne
        (OrderedHistoryContiguousIntervalSum.shift deltaTwo htail)

/-- Every occurrence in the complete linear ordered-history recursion is a
sum over a nonempty contiguous interval of the original phase list. -/
theorem orderedHistoryDenominator_isContiguousIntervalSum :
    ∀ (phases : List Real) (delta : Real),
      delta ∈ orderedHistoryDenominators phases →
        OrderedHistoryContiguousIntervalSum phases delta
  | [], delta, hdelta => by
      simpa [orderedHistoryDenominators] using hdelta
  | [deltaOne], delta, hdelta => by
      have h : delta = deltaOne := by
        simpa [orderedHistoryDenominators] using hdelta
      subst delta
      exact OrderedHistoryContiguousIntervalSum.fromPrefix
        (OrderedHistoryNonemptyPrefixSum.head deltaOne [])
  | deltaOne :: deltaTwo :: tail, delta, hdelta => by
      simp only [orderedHistoryDenominators, List.mem_cons,
        List.mem_append] at hdelta
      rcases hdelta with hfirst | hdrop | hmerge
      · subst delta
        exact OrderedHistoryContiguousIntervalSum.fromPrefix
          (OrderedHistoryNonemptyPrefixSum.head deltaOne
            (deltaTwo :: tail))
      · exact OrderedHistoryContiguousIntervalSum.shift deltaOne
          (orderedHistoryDenominator_isContiguousIntervalSum
            (deltaTwo :: tail) delta hdrop)
      · exact orderedHistoryContiguousIntervalSum_unmerge_head
          (orderedHistoryDenominator_isContiguousIntervalSum
            ((deltaOne + deltaTwo) :: tail) delta hmerge)
termination_by phases => phases.length

/-- A concrete nonempty half-open interval `[start, stop)` in an ordered
history of the displayed length. -/
structure OrderedHistoryInterval (order : Nat) where
  start : Nat
  stop : Nat
  start_lt_stop : start < stop
  stop_le : stop ≤ order

/-- The contiguous block selected by an ordered-history interval. -/
def OrderedHistoryInterval.block
    {order : Nat} {alpha : Type*} (interval : OrderedHistoryInterval order)
    (history : List alpha) : List alpha :=
  (history.drop interval.start).take (interval.stop - interval.start)

/-- A nonempty prefix-sum proof has a concrete positive endpoint. -/
theorem OrderedHistoryNonemptyPrefixSum.exists_stop :
    ∀ {phases : List Real} {delta : Real},
      OrderedHistoryNonemptyPrefixSum phases delta →
        ∃ stop : Nat, 0 < stop ∧ stop ≤ phases.length ∧
          delta = (phases.take stop).sum
  | _, _, .head delta tail => by
      exact ⟨1, by omega, by simp, by simp⟩
  | _, _, .extend delta hprefix => by
      obtain ⟨stop, hstopPos, hstopLe, hsum⟩ := hprefix.exists_stop
      refine ⟨stop + 1, by omega, by simpa using Nat.succ_le_succ hstopLe,
        ?_⟩
      simpa [List.take_succ_cons, hsum, add_assoc]

/-- Every abstract contiguous-interval proof has explicit interval endpoints
and equals the sum of the selected block. -/
theorem OrderedHistoryContiguousIntervalSum.exists_interval :
    ∀ {phases : List Real} {delta : Real},
      OrderedHistoryContiguousIntervalSum phases delta →
        ∃ interval : OrderedHistoryInterval phases.length,
          delta = (interval.block phases).sum
  | _, _, .fromPrefix hprefix => by
      obtain ⟨stop, hstopPos, hstopLe, hsum⟩ := hprefix.exists_stop
      let interval : OrderedHistoryInterval _ :=
        { start := 0
          stop := stop
          start_lt_stop := hstopPos
          stop_le := hstopLe }
      exact ⟨interval, by simpa [interval, OrderedHistoryInterval.block]
        using hsum⟩
  | _, _, .shift head hinterval => by
      obtain ⟨interval, hsum⟩ := hinterval.exists_interval
      let shifted : OrderedHistoryInterval (head :: _).length :=
        { start := interval.start + 1
          stop := interval.stop + 1
          start_lt_stop := by
            exact Nat.add_lt_add_right interval.start_lt_stop 1
          stop_le := by simpa using Nat.succ_le_succ interval.stop_le }
      refine ⟨shifted, ?_⟩
      simpa [shifted, OrderedHistoryInterval.block,
        Nat.succ_eq_add_one] using hsum

/-- Concrete interval representation of every complete recursive denominator. -/
theorem exists_interval_eq_orderedHistoryDenominator
    (phases : List Real) {delta : Real}
    (hdelta : delta ∈ orderedHistoryDenominators phases) :
    ∃ interval : OrderedHistoryInterval phases.length,
      delta = (interval.block phases).sum :=
  (orderedHistoryDenominator_isContiguousIntervalSum
    phases delta hdelta).exists_interval

/-- Actual local A1 phase list associated with a list of ordered vertices. -/
def physlibA1OrderedHistoryListLocalPhaseList
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (pair : Real × Real) : List Real :=
  term.map fun localTerm =>
    physlibA1PairMismatchChart
      fixed site₁ site₂ observed localTerm pair

/-- Terms in one concrete contiguous interval. -/
def physlibA1OrderedHistoryIntervalTermList
    {N : Nat} [NeZero N] (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length) :
    List (QuadraticPhaseTerm N) :=
  interval.block term

/-- Finite term family carried by one contiguous interval. -/
def physlibA1OrderedHistoryIntervalTermFamily
    {N : Nat} [NeZero N] (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length) :
    Fin (physlibA1OrderedHistoryIntervalTermList term interval).length →
      QuadraticPhaseTerm N :=
  (physlibA1OrderedHistoryIntervalTermList term interval).get

/-- Actual cumulative A1 chart of one shifted contiguous interval. -/
def physlibA1OrderedHistoryIntervalPairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length)
    (pair : Real × Real) : Real :=
  physlibA1CumulativePairMismatchChart
    fixed site₁ site₂ observed
      (physlibA1OrderedHistoryIntervalTermFamily term interval)
      Finset.univ pair

/-- Total actual vertical Jacobian of one shifted interval. -/
def physlibA1OrderedHistoryIntervalVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length)
    (pair : Real × Real) : Real :=
  physlibA1CumulativePairMismatchVerticalJacobian
    fixed site₁ site₂ observed
      (physlibA1OrderedHistoryIntervalTermFamily term interval)
      Finset.univ pair

/-- Common differentiability source of all actual terms in one interval. -/
def physlibA1OrderedHistoryIntervalDifferentiabilitySource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length) : Set (Real × Real) :=
  physlibA1CumulativePairMismatchDifferentiabilitySource
    fixed site₁ site₂ observed
      (physlibA1OrderedHistoryIntervalTermFamily term interval)
      Finset.univ

/-- The actual interval chart is exactly the sum of the corresponding block
of the actual local A1 phase list. -/
theorem physlibA1OrderedHistoryIntervalPairMismatchChart_eq_block_sum
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length)
    (pair : Real × Real) :
    physlibA1OrderedHistoryIntervalPairMismatchChart
        fixed site₁ site₂ observed term interval pair =
      (interval.block
        (physlibA1OrderedHistoryListLocalPhaseList
          fixed site₁ site₂ observed term pair)).sum := by
  classical
  let block := physlibA1OrderedHistoryIntervalTermList term interval
  let phase : QuadraticPhaseTerm N → Real := fun localTerm =>
    physlibA1PairMismatchChart
      fixed site₁ site₂ observed localTerm pair
  calc
    physlibA1OrderedHistoryIntervalPairMismatchChart
        fixed site₁ site₂ observed term interval pair =
        ∑ i : Fin block.length, phase (block.get i) := by
          simp [physlibA1OrderedHistoryIntervalPairMismatchChart,
            physlibA1CumulativePairMismatchChart,
            physlibA1OrderedHistoryIntervalTermFamily, block, phase]
    _ = (block.map phase).sum := by
      rw [← List.sum_ofFn]
      simp [List.ofFn_comp']
    _ = (interval.block
        (physlibA1OrderedHistoryListLocalPhaseList
          fixed site₁ site₂ observed term pair)).sum := by
      simp [block, phase, physlibA1OrderedHistoryIntervalTermList,
        physlibA1OrderedHistoryListLocalPhaseList,
        OrderedHistoryInterval.block]

/-- Every complete recursive denominator of an actual linear A1 history is
exactly one actual shifted contiguous-interval chart on the displayed common
pair fiber. -/
theorem exists_intervalChart_eq_physlibA1OrderedHistoryDenominator
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (pair : Real × Real)
    {delta : Real}
    (hdelta : delta ∈ orderedHistoryDenominators
      (physlibA1OrderedHistoryListLocalPhaseList
        fixed site₁ site₂ observed term pair)) :
    ∃ interval : OrderedHistoryInterval term.length,
      delta = physlibA1OrderedHistoryIntervalPairMismatchChart
        fixed site₁ site₂ observed term interval pair := by
  let phases := physlibA1OrderedHistoryListLocalPhaseList
    fixed site₁ site₂ observed term pair
  obtain ⟨phaseInterval, hphase⟩ :=
    exists_interval_eq_orderedHistoryDenominator phases hdelta
  let interval : OrderedHistoryInterval term.length :=
    { start := phaseInterval.start
      stop := phaseInterval.stop
      start_lt_stop := phaseInterval.start_lt_stop
      stop_le := by
        simpa [phases, physlibA1OrderedHistoryListLocalPhaseList]
          using phaseInterval.stop_le }
  refine ⟨interval, ?_⟩
  rw [physlibA1OrderedHistoryIntervalPairMismatchChart_eq_block_sum]
  simpa [phases, interval, OrderedHistoryInterval.block] using hphase

/-- Ordinary derivative of one interval chart is the sum of the genuine
actual vertical Jacobians of exactly its terms. -/
theorem deriv_physlibA1OrderedHistoryIntervalPairMismatchFiber_eq_sum
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1OrderedHistoryIntervalDifferentiabilitySource
        fixed site₁ site₂ observed term interval) :
    deriv (fun second =>
        physlibA1OrderedHistoryIntervalPairMismatchChart
          fixed site₁ site₂ observed term interval (pair.1, second)) pair.2 =
      ∑ i : Fin
          (physlibA1OrderedHistoryIntervalTermList term interval).length,
        physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed
            (physlibA1OrderedHistoryIntervalTermFamily term interval i) pair := by
  simpa [physlibA1OrderedHistoryIntervalPairMismatchChart] using
    (deriv_physlibA1CumulativePairMismatchFiber_eq_sum
      fixed hsite observed
        (physlibA1OrderedHistoryIntervalTermFamily term interval)
        Finset.univ hregular)

/-- One independent compact-atlas certificate for every nonempty contiguous
interval.  The compact set and total-Jacobian threshold may depend on the
interval; no common lower bound is inferred. -/
theorem exists_physlibA1OrderedHistoryIntervalCompactAtlasCertificates
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first : Real)
    (K : OrderedHistoryInterval term.length → Set Real)
    (hK : ∀ interval, IsCompact (K interval))
    (hregular : ∀ interval second, second ∈ K interval →
      (first, second) ∈
        physlibA1OrderedHistoryIntervalDifferentiabilitySource
          fixed site₁ site₂ observed term interval)
    (j0 : OrderedHistoryInterval term.length → Real)
    (hj0 : ∀ interval, 0 < j0 interval)
    (hjac : ∀ interval second, second ∈ K interval →
      j0 interval ≤
        |physlibA1OrderedHistoryIntervalVerticalJacobian
          fixed site₁ site₂ observed term interval (first, second)|) :
    ∃ certificate : ∀ interval : OrderedHistoryInterval term.length,
        OrdinaryGardenCoordinateCompactAtlas
          (fun second =>
            physlibA1OrderedHistoryIntervalPairMismatchChart
              fixed site₁ site₂ observed term interval (first, second)),
      (∀ interval, (certificate interval).compactSet = K interval) ∧
      (∀ interval, (certificate interval).jacLower = j0 interval) := by
  have hcertificate : ∀ interval : OrderedHistoryInterval term.length,
      ∃ certificate : OrdinaryGardenCoordinateCompactAtlas
          (fun second =>
            physlibA1OrderedHistoryIntervalPairMismatchChart
              fixed site₁ site₂ observed term interval (first, second)),
        certificate.compactSet = K interval ∧
          certificate.jacLower = j0 interval := by
    intro interval
    exact exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1Cumulative
      fixed hsite observed
        (physlibA1OrderedHistoryIntervalTermFamily term interval)
        Finset.univ first (K interval) (hK interval)
        (hregular interval) (hj0 interval) (hjac interval)
  choose certificate hcompact hjacLower using hcertificate
  exact ⟨certificate, hcompact, hjacLower⟩

end

end ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall
