import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1
import FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7ActivePatternOccurrenceWeightV1

open Family8Family7NativeHighWeightedCriticalBallV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

/-!
# Pattern-first equal-share occurrence weights

The rectangle-first-hit partition need not keep the active pattern of its
label representative.  Here the literal source is partitioned by the exact
finite physical active pattern.  Every local active occurrence at the chosen
representative is consequently physically active at every point of the same
event.  Equal-share weights retain the exact source mass and can be fed to the
existing weighted critical-ball selector.
-/

def activePatternEvent
    {iota : Type u} [DecidableEq iota]
    (physical : FiniteProjectedShading (Real × Real) iota)
    (source : Set (Real × Real)) (pattern : Finset iota) :
    Set (Real × Real) :=
  source ∩ {x | physical.activeAtPoint x = pattern}

structure ActivePatternOccurrenceData
    {iota : Type u} [DecidableEq iota]
    (N : CanonicalNormNonconcentrationData iota)
    (physical localShading : FiniteProjectedShading (Real × Real) iota)
    (source : Set (Real × Real)) : Prop where
  source_measurable : MeasurableSet source
  local_active_nonempty : ∀ x, x ∈ source →
    (localShading.activeAtPoint x).Nonempty
  local_active_subset_physical : ∀ x,
    localShading.activeAtPoint x ⊆ physical.activeAtPoint x
  local_active_subset_family : ∀ x,
    localShading.activeAtPoint x ⊆ N.family

namespace ActivePatternOccurrenceData

variable {iota : Type u} [DecidableEq iota]
variable {N : CanonicalNormNonconcentrationData iota}
variable {physical localShading : FiniteProjectedShading (Real × Real) iota}
variable {source : Set (Real × Real)}

noncomputable def patterns
    (_P : ActivePatternOccurrenceData N physical localShading source) :
    Finset (Finset iota) := by
  classical
  exact physical.ambient.powerset.filter fun pattern =>
    (activePatternEvent physical source pattern).Nonempty

abbrev PatternIndex
    (P : ActivePatternOccurrenceData N physical localShading source) :=
  {pattern // pattern ∈ P.patterns}

theorem pattern_event_nonempty
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) :
    (activePatternEvent physical source p.1).Nonempty := by
  classical
  have hp := p.2
  change p.1 ∈ physical.ambient.powerset.filter (fun pattern =>
    (activePatternEvent physical source pattern).Nonempty) at hp
  exact (Finset.mem_filter.mp hp).2

noncomputable def representative
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) : Real × Real :=
  Classical.choose (P.pattern_event_nonempty p)

theorem representative_mem_event
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) :
    P.representative p ∈ activePatternEvent physical source p.1 :=
  Classical.choose_spec (P.pattern_event_nonempty p)

/-- Every local active occurrence in one occupied pattern. -/
noncomputable def occurrenceFiber
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) : Finset iota :=
  localShading.activeAtPoint (P.representative p)

theorem occurrenceFiber_nonempty
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) : (P.occurrenceFiber p).Nonempty :=
  P.local_active_nonempty (P.representative p)
    (P.representative_mem_event p).1

theorem occurrenceFiber_subset_family
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) : P.occurrenceFiber p ⊆ N.family :=
  P.local_active_subset_family (P.representative p)

/-- Every occurrence in a pattern fibre remains physically active throughout
the whole pattern event. -/
theorem occurrence_mem_physicalAt_of_mem_event
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) {i : iota} (hi : i ∈ P.occurrenceFiber p)
    {x : Real × Real} (hx : x ∈ activePatternEvent physical source p.1) :
    i ∈ physical.activeAtPoint x := by
  have hrep := P.local_active_subset_physical (P.representative p) hi
  have hrepPattern := (P.representative_mem_event p).2
  change physical.activeAtPoint (P.representative p) = p.1 at hrepPattern
  have hxPattern := hx.2
  change physical.activeAtPoint x = p.1 at hxPattern
  rw [hrepPattern] at hrep
  rw [hxPattern]
  exact hrep

theorem measurableSet_activePatternEvent
    (P : ActivePatternOccurrenceData N physical localShading source)
    (pattern : Finset iota) :
    MeasurableSet (activePatternEvent physical source pattern) := by
  unfold activePatternEvent
  apply P.source_measurable.inter
  exact measurableSet_finiteIncidencePatternPredicate physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (fun i hi => physical.measurable_carrier i hi)
    (fun active => active = pattern)

theorem patternEvents_pairwiseDisjoint
    (P : ActivePatternOccurrenceData N physical localShading source) :
    Set.PairwiseDisjoint (Set.univ : Set P.PatternIndex)
      (fun p => activePatternEvent physical source p.1) := by
  intro p _hp q _hq hpq
  refine Set.disjoint_left.2 ?_
  intro x hxp hxq
  apply hpq
  apply Subtype.ext
  exact hxp.2.symm.trans hxq.2

theorem biUnion_patternEvents_eq_source
    (P : ActivePatternOccurrenceData N physical localShading source) :
    (⋃ p : P.PatternIndex,
      activePatternEvent physical source p.1) = source := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hp⟩ := hx
    exact hp.1
  · intro hx
    let pattern := physical.activeAtPoint x
    have hsubset : pattern ⊆ physical.ambient :=
      finiteIncidenceActiveAtPoint_subset physical.ambient
        (fun i y => y ∈ physical.carrier i) x
    have hevent : (activePatternEvent physical source pattern).Nonempty :=
      ⟨x, hx, rfl⟩
    have hpattern : pattern ∈ P.patterns := by
      rw [patterns, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr hsubset, hevent⟩
    let p : P.PatternIndex := ⟨pattern, hpattern⟩
    simp only [Set.mem_iUnion]
    exact ⟨p, hx, rfl⟩

theorem sum_volume_patternEvents_eq_source
    (P : ActivePatternOccurrenceData N physical localShading source) :
    (∑ p : P.PatternIndex,
      volume (activePatternEvent physical source p.1)) = volume source := by
  have hmeasure :
      volume (⋃ p ∈ ((Finset.univ : Finset P.PatternIndex) :
          Set P.PatternIndex),
        activePatternEvent physical source p.1) =
      ∑ p ∈ (Finset.univ : Finset P.PatternIndex),
        volume (activePatternEvent physical source p.1) :=
    measure_biUnion_finset
      (by
        intro p _hp q _hq hpq
        exact P.patternEvents_pairwiseDisjoint (Set.mem_univ p)
          (Set.mem_univ q) hpq)
      (fun p _hp => P.measurableSet_activePatternEvent p.1)
  have hunion :
      (⋃ p ∈ ((Finset.univ : Finset P.PatternIndex) :
          Set P.PatternIndex),
        activePatternEvent physical source p.1) = source := by
    simpa using P.biUnion_patternEvents_eq_source
  rw [hunion] at hmeasure
  simpa using hmeasure.symm

/-- Equal share of one exact pattern-event volume across all genuine local
occurrences in that pattern. -/
noncomputable def occurrenceWeight
    (P : ActivePatternOccurrenceData N physical localShading source)
    (i : iota) : ENNReal :=
  ∑ p : P.PatternIndex,
    if i ∈ P.occurrenceFiber p then
      volume (activePatternEvent physical source p.1) /
        (P.occurrenceFiber p).card else 0

theorem occurrenceWeight_support
    (P : ActivePatternOccurrenceData N physical localShading source)
    {i : iota} (hi : P.occurrenceWeight i ≠ 0) : i ∈ N.family := by
  by_contra hiFamily
  apply hi
  unfold occurrenceWeight
  apply Finset.sum_eq_zero
  intro p _hp
  have hnot : i ∉ P.occurrenceFiber p := by
    intro hip
    exact hiFamily (P.occurrenceFiber_subset_family p hip)
  simp [hnot]

private theorem sum_equalShare_over_family
    (P : ActivePatternOccurrenceData N physical localShading source)
    (p : P.PatternIndex) :
    (∑ i ∈ N.family,
      if i ∈ P.occurrenceFiber p then
        volume (activePatternEvent physical source p.1) /
          ((P.occurrenceFiber p).card : ENNReal)
      else 0) = volume (activePatternEvent physical source p.1) := by
  classical
  let fiber := P.occurrenceFiber p
  have hfiberSubset : fiber ⊆ N.family :=
    P.occurrenceFiber_subset_family p
  have hfilter : N.family.filter (fun i => i ∈ fiber) = fiber := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi => hi.2
    · exact fun hi => ⟨hfiberSubset hi, hi⟩
  calc
    (∑ i ∈ N.family, if i ∈ fiber then
        volume (activePatternEvent physical source p.1) /
          (fiber.card : ENNReal) else 0) =
      ∑ i ∈ N.family.filter (fun i => i ∈ fiber),
        volume (activePatternEvent physical source p.1) /
          (fiber.card : ENNReal) := by
        rw [Finset.sum_filter]
    _ = ∑ i ∈ fiber,
        volume (activePatternEvent physical source p.1) /
          (fiber.card : ENNReal) := by rw [hfilter]
    _ = (fiber.card : ENNReal) *
        (volume (activePatternEvent physical source p.1) /
          (fiber.card : ENNReal)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = volume (activePatternEvent physical source p.1) := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel
        (by exact_mod_cast
          (Finset.card_ne_zero.mpr (P.occurrenceFiber_nonempty p)))
        (ENNReal.natCast_ne_top _)

theorem sum_occurrenceWeight_eq_source
    (P : ActivePatternOccurrenceData N physical localShading source) :
    (∑ i ∈ N.family, P.occurrenceWeight i) = volume source := by
  classical
  unfold occurrenceWeight
  rw [Finset.sum_comm]
  calc
    (∑ p : P.PatternIndex,
      ∑ i ∈ N.family,
        if i ∈ P.occurrenceFiber p then
          volume (activePatternEvent physical source p.1) /
            (P.occurrenceFiber p).card else 0) =
        ∑ p : P.PatternIndex,
          volume (activePatternEvent physical source p.1) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact sum_equalShare_over_family P p
    _ = volume source := P.sum_volume_patternEvents_eq_source

noncomputable def weightedNormData
    (P : ActivePatternOccurrenceData N physical localShading source) :
    WeightedCanonicalNormBallData iota where
  family := N.family
  distance := N.distance
  weight := P.occurrenceWeight
  delta := N.delta
  ceiling := N.ceiling
  exponent := N.exponent
  family_nonempty := N.family_nonempty
  self_le_delta := N.self_le_delta
  delta_pos := N.delta_pos
  delta_le_ceiling := N.delta_le_ceiling
  exponent_nonneg := N.exponent_nonneg

#print axioms activePatternEvent
#print axioms ActivePatternOccurrenceData.patterns
#print axioms ActivePatternOccurrenceData.occurrenceFiber
#print axioms ActivePatternOccurrenceData.occurrence_mem_physicalAt_of_mem_event
#print axioms ActivePatternOccurrenceData.patternEvents_pairwiseDisjoint
#print axioms ActivePatternOccurrenceData.biUnion_patternEvents_eq_source
#print axioms ActivePatternOccurrenceData.sum_volume_patternEvents_eq_source
#print axioms ActivePatternOccurrenceData.occurrenceWeight
#print axioms ActivePatternOccurrenceData.sum_occurrenceWeight_eq_source
#print axioms ActivePatternOccurrenceData.weightedNormData

end ActivePatternOccurrenceData

end

end Family8Family7ActivePatternOccurrenceWeightV1
