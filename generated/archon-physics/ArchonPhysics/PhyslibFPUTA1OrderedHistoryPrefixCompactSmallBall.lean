import ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall

/-!
# Actual A1 compact atlases along an arbitrary ordered-history prefix branch

Let a finite ordered history be a family of genuine `QuadraticPhaseTerm`
vertices, all evaluated on the same retained two-mass chart and the same
vertical mass fiber.  For every prefix this file forms the cumulative actual
A1 mismatch and proves that its vertical derivative is the corresponding sum
of actual A1 vertical Jacobians.  Independent compact sets `K_j`, positive
thresholds `j0_j`, and honest noncancellation bounds

`j0_j ≤ |sum of the prefix Jacobians|`

then produce an `OrdinaryGardenCoordinateCompactAtlas` for every prefix.

There is an important exact bookkeeping boundary.  The prefix-cumulative
list is a subfamily of `orderedHistoryDenominators`, but from order three on
it is not the entire recursive denominator list: the latter also contains
prefixes of shifted/merged subhistories and has `2^r - 1` occurrences.  The
theorems below prove exact equality with the prefix cumulative-phase list and
explicit membership in the complete enumeration; they never identify the
two lists.  Certifying the whole linear IBP tree requires the analogous
compact hypotheses for every shifted interval.  A branching garden may also
lack one common retained fiber, so branching fiber selection remains
a separate input.  Nothing here asserts re-Haar, RPA, Markov closure, or
recollision decay.
-/

namespace ArchonPhysics.PhyslibFPUTA1OrderedHistoryPrefixCompactSmallBall

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open Function MeasureTheory Set

noncomputable section

/-- Prefix cumulative phases, represented without discarding the order of the
original history.  The entry indexed by `j` is the sum of the first `j + 1`
local phases. -/
def orderedHistoryPrefixCumulativePhases (phases : List Real) : List Real :=
  List.ofFn fun j : Fin phases.length =>
    (phases.take (j.1 + 1)).sum

@[simp] theorem length_orderedHistoryPrefixCumulativePhases
    (phases : List Real) :
    (orderedHistoryPrefixCumulativePhases phases).length = phases.length := by
  simp [orderedHistoryPrefixCumulativePhases]

/-- Every prefix cumulative phase is one of the denominators exposed by the
complete ordered-history recursion. -/
theorem sum_take_succ_mem_orderedHistoryDenominators :
    ∀ (phases : List Real) (j : Fin phases.length),
      (phases.take (j.1 + 1)).sum ∈ orderedHistoryDenominators phases
  | [], j => Fin.elim0 j
  | [delta], j => by
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp [orderedHistoryDenominators]
  | deltaOne :: deltaTwo :: tail, j => by
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [orderedHistoryDenominators]
      · have hmerge :=
          sum_take_succ_mem_orderedHistoryDenominators
            ((deltaOne + deltaTwo) :: tail) k
        have heq :
            ((deltaOne :: deltaTwo :: tail).take
                ((Fin.succ k).1 + 1)).sum =
              (((deltaOne + deltaTwo) :: tail).take (k.1 + 1)).sum := by
          simp [List.take_succ_cons, add_assoc]
        rw [heq]
        simp only [orderedHistoryDenominators, List.mem_cons,
          List.mem_append]
        exact Or.inr (Or.inr hmerge)
termination_by phases => phases.length

/-- Hence the whole prefix cumulative-phase list embeds pointwise in the
complete recursive denominator enumeration. -/
theorem mem_orderedHistoryDenominators_of_mem_prefixCumulativePhases
    (phases : List Real) {delta : Real}
    (hdelta : delta ∈ orderedHistoryPrefixCumulativePhases phases) :
    delta ∈ orderedHistoryDenominators phases := by
  rw [orderedHistoryPrefixCumulativePhases, List.mem_ofFn] at hdelta
  rcases hdelta with ⟨j, rfl⟩
  exact sum_take_succ_mem_orderedHistoryDenominators phases j

/-- Already at order three the prefix list is strictly shorter than the full
recursive ordered-history denominator list.  This prevents an accidental
replacement of all IBP denominators by only the root-prefix branch. -/
theorem orderedHistoryDenominators_three_ne_prefixCumulativePhases
    (deltaOne deltaTwo deltaThree : Real) :
    orderedHistoryDenominators [deltaOne, deltaTwo, deltaThree] ≠
      orderedHistoryPrefixCumulativePhases
        [deltaOne, deltaTwo, deltaThree] := by
  intro heq
  have hlength := congrArg List.length heq
  norm_num [orderedHistoryDenominators,
    orderedHistoryPrefixCumulativePhases] at hlength

/-- Indices in the inclusive prefix ending at `j`. -/
def physlibA1OrderedHistoryPrefixActive
    {order : Nat} (j : Fin order) : Finset (Fin order) :=
  Finset.univ.filter fun i => i.1 < j.1 + 1

/-- Local actual A1 phases of a finite ordered history on one retained pair. -/
def physlibA1OrderedHistoryLocalPhaseFamily
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N)
    (pair : Real × Real) : Fin order → Real := fun i =>
  physlibA1PairMismatchChart
    fixed site₁ site₂ observed (term i) pair

/-- Ordered list of the local actual A1 phases. -/
def physlibA1OrderedHistoryLocalPhaseList
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N)
    (pair : Real × Real) : List Real :=
  List.ofFn
    (physlibA1OrderedHistoryLocalPhaseFamily
      fixed site₁ site₂ observed term pair)

/-- Actual cumulative mismatch chart of the prefix ending at `j`. -/
def physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order)
    (pair : Real × Real) : Real :=
  physlibA1CumulativePairMismatchChart
    fixed site₁ site₂ observed term
      (physlibA1OrderedHistoryPrefixActive j) pair

/-- Actual vertical Jacobian sum of the prefix ending at `j`. -/
def physlibA1OrderedHistoryPrefixVerticalJacobian
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order)
    (pair : Real × Real) : Real :=
  physlibA1CumulativePairMismatchVerticalJacobian
    fixed site₁ site₂ observed term
      (physlibA1OrderedHistoryPrefixActive j) pair

/-- Common differentiability source of every local term in one prefix. -/
def physlibA1OrderedHistoryPrefixDifferentiabilitySource
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order) :
    Set (Real × Real) :=
  physlibA1CumulativePairMismatchDifferentiabilitySource
    fixed site₁ site₂ observed term
      (physlibA1OrderedHistoryPrefixActive j)

/-- Ordered list of all actual root-prefix cumulative charts. -/
def physlibA1OrderedHistoryPrefixCumulativeChartList
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N)
    (pair : Real × Real) : List Real :=
  List.ofFn fun j =>
    physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
      fixed site₁ site₂ observed term j pair

/-- One actual prefix chart is exactly the sum of the corresponding initial
segment of the local phase list. -/
theorem physlibA1OrderedHistoryPrefixCumulativePairMismatchChart_eq_sum_take
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order)
    (pair : Real × Real) :
    physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
        fixed site₁ site₂ observed term j pair =
      ((physlibA1OrderedHistoryLocalPhaseList
          fixed site₁ site₂ observed term pair).take (j.1 + 1)).sum := by
  rw [physlibA1OrderedHistoryLocalPhaseList, List.sum_take_ofFn]
  rfl

/-- Exact arbitrary-order list identity: the actual prefix charts coincide
with the prefix cumulative phases of the ordered local A1 phase list. -/
theorem physlibA1OrderedHistoryPrefixCumulativeChartList_eq_cumulativePhases
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N)
    (pair : Real × Real) :
    physlibA1OrderedHistoryPrefixCumulativeChartList
        fixed site₁ site₂ observed term pair =
      orderedHistoryPrefixCumulativePhases
        (physlibA1OrderedHistoryLocalPhaseList
          fixed site₁ site₂ observed term pair) := by
  apply List.ext_get
  · simp [physlibA1OrderedHistoryPrefixCumulativeChartList,
      physlibA1OrderedHistoryLocalPhaseList]
  · intro n hnLeft hnRight
    simp only [physlibA1OrderedHistoryPrefixCumulativeChartList,
      orderedHistoryPrefixCumulativePhases, List.get_ofFn]
    apply physlibA1OrderedHistoryPrefixCumulativePairMismatchChart_eq_sum_take

/-- Every actual prefix cumulative chart is therefore an actual member of
the full ordered-history denominator enumeration. -/
theorem physlibA1OrderedHistoryPrefixCumulativeChart_mem_denominators
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order)
    (pair : Real × Real) :
    physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
        fixed site₁ site₂ observed term j pair ∈
      orderedHistoryDenominators
        (physlibA1OrderedHistoryLocalPhaseList
          fixed site₁ site₂ observed term pair) := by
  rw [physlibA1OrderedHistoryPrefixCumulativePairMismatchChart_eq_sum_take]
  let phases := physlibA1OrderedHistoryLocalPhaseList
    fixed site₁ site₂ observed term pair
  let j' : Fin phases.length := Fin.cast (by
    simp [phases, physlibA1OrderedHistoryLocalPhaseList]) j
  simpa [phases, j'] using
    (sum_take_succ_mem_orderedHistoryDenominators phases j')

/-- Ordinary derivative of a prefix chart is exactly the corresponding
prefix sum of genuine actual vertical Jacobians. -/
theorem deriv_physlibA1OrderedHistoryPrefixCumulativePairMismatchFiber_eq_sum
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1OrderedHistoryPrefixDifferentiabilitySource
        fixed site₁ site₂ observed term j) :
    deriv (fun second =>
        physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
          fixed site₁ site₂ observed term j (pair.1, second)) pair.2 =
      ∑ i ∈ physlibA1OrderedHistoryPrefixActive j,
        physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed (term i) pair := by
  exact deriv_physlibA1CumulativePairMismatchFiber_eq_sum
    fixed hsite observed term
      (physlibA1OrderedHistoryPrefixActive j) hregular

/-- Independent compact-atlas certificates for every prefix.  Each prefix
has its own compact set and its own positive lower bound on the total prefix
Jacobian; no uniform or full-support lower bound is inferred. -/
theorem exists_physlibA1OrderedHistoryPrefixCompactAtlasCertificates
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (first : Real)
    (K : Fin order → Set Real) (hK : ∀ j, IsCompact (K j))
    (hregular : ∀ j second, second ∈ K j →
      (first, second) ∈
        physlibA1OrderedHistoryPrefixDifferentiabilitySource
          fixed site₁ site₂ observed term j)
    (j0 : Fin order → Real) (hj0 : ∀ j, 0 < j0 j)
    (hjac : ∀ j second, second ∈ K j → j0 j ≤
      |physlibA1OrderedHistoryPrefixVerticalJacobian
        fixed site₁ site₂ observed term j (first, second)|) :
    ∃ certificate : ∀ j : Fin order,
        OrdinaryGardenCoordinateCompactAtlas
          (fun second =>
            physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
              fixed site₁ site₂ observed term j (first, second)),
      (∀ j, (certificate j).compactSet = K j) ∧
      (∀ j, (certificate j).jacLower = j0 j) := by
  have hcertificate : ∀ j : Fin order,
      ∃ certificate : OrdinaryGardenCoordinateCompactAtlas
          (fun second =>
            physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
              fixed site₁ site₂ observed term j (first, second)),
        certificate.compactSet = K j ∧
          certificate.jacLower = j0 j := by
    intro j
    exact exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1Cumulative
      fixed hsite observed term
        (physlibA1OrderedHistoryPrefixActive j)
        first (K j) (hK j) (hregular j) (hj0 j) (hjac j)
  choose certificate hcompact hjacLower using hcertificate
  exact ⟨certificate, hcompact, hjacLower⟩

end

end ArchonPhysics.PhyslibFPUTA1OrderedHistoryPrefixCompactSmallBall
