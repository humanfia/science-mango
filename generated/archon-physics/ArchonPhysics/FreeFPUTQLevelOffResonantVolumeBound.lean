import ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
import ArchonPhysics.RepeatedParentChildAcousticCumulativeBound

/-!
# Volume bounds for the q-level off-resonant FPUT corrections

This file keeps the frequency factors in the normalized cubic vertex until
after the harmonic actions are inserted.  In the observed-child sign-zero
sector this cancels one, but not both, powers of the exact gap
`omega_other`.  The irreducible deterministic object is therefore the
weighted acoustic moment

`sum_k d(observed, observed, k)^2 / omega_k`.

The repeated-away, observed-child all-plus, and all-equal sectors have no
such remaining soft denominator once the observed output frequency is kept
explicit.  Frame orthogonality and finite selector multiplicity make those
three sectors volume independent.  No acoustic gap, localization estimate,
or small-denominator density hypothesis is used.
-/

namespace ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
open scoped BigOperators Matrix

noncomputable section

/-! ## Frequency-aware repeated-vertex bounds -/

/-- An active normalized leg is bounded by half its own frequency. -/
theorem harmonicActiveNormalizedCoefficient_le_half_frequency
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    harmonicActiveNormalizedCoefficient m k ≤
      orderedModeFrequency (harmonicHermitian m) k / 2 := by
  have hnonneg := harmonicActiveNormalizedCoefficient_nonneg m k
  have hbound := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m k
  change |harmonicActiveNormalizedCoefficient m k| ≤
    orderedModeFrequency (harmonicHermitian m) k / 2 at hbound
  simpa [abs_of_nonneg hnonneg] using hbound

/-- Ordered tuple `[common, common, other]`, retaining the cubic frame
coefficient and every frequency factor. -/
theorem harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (common other : OrderedModeIndex N) :
    harmonicOrderedNormalizedInteractionWeight m ![common, common, other] ≤
      (orderedModeFrequency (harmonicHermitian m) common / 2) ^ 2 *
        (orderedModeFrequency (harmonicHermitian m) other / 2) *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) common other ^ 2 := by
  rw [harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_eq]
  have hc0 := harmonicActiveNormalizedCoefficient_nonneg m common
  have ho0 := harmonicActiveNormalizedCoefficient_nonneg m other
  have hcb := harmonicActiveNormalizedCoefficient_le_half_frequency m common
  have hob := harmonicActiveNormalizedCoefficient_le_half_frequency m other
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (pow_le_pow_left₀ hc0 hcb 2) hob ho0 (sq_nonneg _))
    (sq_nonneg _)

/-- Ordered tuple `[other, common, common]`. -/
theorem harmonicOrderedNormalizedInteractionWeight_repeated_one_two_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (common other : OrderedModeIndex N) :
    harmonicOrderedNormalizedInteractionWeight m ![other, common, common] ≤
      (orderedModeFrequency (harmonicHermitian m) common / 2) ^ 2 *
        (orderedModeFrequency (harmonicHermitian m) other / 2) *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) common other ^ 2 := by
  rw [harmonicOrderedNormalizedInteractionWeight_repeated_one_two_eq]
  exact harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_le_frame
    m common other

/-- Ordered tuple `[common, other, common]`. -/
theorem harmonicOrderedNormalizedInteractionWeight_repeated_zero_two_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (common other : OrderedModeIndex N) :
    harmonicOrderedNormalizedInteractionWeight m ![common, other, common] ≤
      (orderedModeFrequency (harmonicHermitian m) common / 2) ^ 2 *
        (orderedModeFrequency (harmonicHermitian m) other / 2) *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) common other ^ 2 := by
  rw [harmonicOrderedNormalizedInteractionWeight_repeated_zero_two_eq]
  exact harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_le_frame
    m common other

/-- Physical version for `[common, common, other]`. -/
theorem normalizedInteractionWeight_repeated_zero_one_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (common other : Lattice.Site N) :
    normalizedInteractionWeight m ![common, common, other] ≤
      (modeFrequency m common / 2) ^ 2 *
        (modeFrequency m other / 2) *
          repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
            (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other) ^ 2 := by
  have h :=
    harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_le_frame
      m (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other)
  rw [harmonicOrderedNormalizedInteractionWeight_eq m hsimple] at h
  have hmodes :
      (fun r ↦ orderedIndexEquiv
        (![orderedIndexEquiv.symm common, orderedIndexEquiv.symm common,
          orderedIndexEquiv.symm other] r)) =
        ![common, common, other] := by
    funext r
    fin_cases r <;> simp
  rw [hmodes] at h
  simpa [orderedModeFrequency_harmonicHermitian_eq] using h

/-- Physical version for `[other, common, common]`. -/
theorem normalizedInteractionWeight_repeated_one_two_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (common other : Lattice.Site N) :
    normalizedInteractionWeight m ![other, common, common] ≤
      (modeFrequency m common / 2) ^ 2 *
        (modeFrequency m other / 2) *
          repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
            (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other) ^ 2 := by
  have h :=
    harmonicOrderedNormalizedInteractionWeight_repeated_one_two_le_frame
      m (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other)
  rw [harmonicOrderedNormalizedInteractionWeight_eq m hsimple] at h
  have hmodes :
      (fun r ↦ orderedIndexEquiv
        (![orderedIndexEquiv.symm other, orderedIndexEquiv.symm common,
          orderedIndexEquiv.symm common] r)) =
        ![other, common, common] := by
    funext r
    fin_cases r <;> simp
  rw [hmodes] at h
  simpa [orderedModeFrequency_harmonicHermitian_eq] using h

/-- Physical version for `[common, other, common]`. -/
theorem normalizedInteractionWeight_repeated_zero_two_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (common other : Lattice.Site N) :
    normalizedInteractionWeight m ![common, other, common] ≤
      (modeFrequency m common / 2) ^ 2 *
        (modeFrequency m other / 2) *
          repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
            (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other) ^ 2 := by
  have h :=
    harmonicOrderedNormalizedInteractionWeight_repeated_zero_two_le_frame
      m (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other)
  rw [harmonicOrderedNormalizedInteractionWeight_eq m hsimple] at h
  have hmodes :
      (fun r ↦ orderedIndexEquiv
        (![orderedIndexEquiv.symm common, orderedIndexEquiv.symm other,
          orderedIndexEquiv.symm common] r)) =
        ![common, other, common] := by
    funext r
    fin_cases r <;> simp
  rw [hmodes] at h
  simpa [orderedModeFrequency_harmonicHermitian_eq] using h

/-! ## Exact selector multiplicities -/

/-- Coordinates consisting of the other mode, both binary signs, and the
selected observed slot.  These coordinates determine an observed-child
selector. -/
def observedChildSelectorCoordinates
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {observed : Lattice.Site N}
    (selector : PositiveObservedChildSelector N m observed) :
    Lattice.Site N × ((Fin 2 × Fin 2) × Fin 2) :=
  (selector.q.1 (otherQuadraticSlot selector.observedSlot),
    (selector.q.2, selector.observedSlot))

/-- The observed-child coordinate map is injective. -/
theorem observedChildSelectorCoordinates_injective
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    {observed : Lattice.Site N} :
    Function.Injective
      (observedChildSelectorCoordinates
        (m := m) (observed := observed)) := by
  intro left right h
  have hslot : left.observedSlot = right.observedSlot :=
    congrArg (fun x ↦ x.2.2) h
  have hsign : left.q.2 = right.q.2 :=
    congrArg (fun x ↦ x.2.1) h
  have hother :
      left.q.1 (otherQuadraticSlot left.observedSlot) =
        right.q.1 (otherQuadraticSlot right.observedSlot) :=
    congrArg Prod.fst h
  have hmodes : left.q.1 = right.q.1 := by
    funext r
    generalize hs : left.observedSlot = slot
    fin_cases slot
    · have hrs : right.observedSlot = 0 := hslot.symm.trans hs
      fin_cases r
      · have hl : left.q.1 0 = observed := by
          simpa [hs] using left.observed_only.1.symm
        have hr : observed = right.q.1 0 := by
          simpa [hrs] using right.observed_only.1
        exact hl.trans hr
      · simpa [hs, hrs, otherQuadraticSlot] using hother
    · have hrs : right.observedSlot = 1 := hslot.symm.trans hs
      fin_cases r
      · simpa [hs, hrs, otherQuadraticSlot] using hother
      · have hl : left.q.1 1 = observed := by
          simpa [hs] using left.observed_only.1.symm
        have hr : observed = right.q.1 1 := by
          simpa [hrs] using right.observed_only.1
        exact hl.trans hr
  have hq : left.q = right.q := Prod.ext hmodes hsign
  cases left with
  | mk lq ls lmem lobs =>
      cases right with
      | mk rq rs rmem robs =>
          dsimp at hq hslot
          subst rq
          subst rs
          rfl

/-- At most eight selectors lie over each other-mode label. -/
theorem sum_observedChildSelector_other_le_eight_mul
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (f : Lattice.Site N → Real)
    (hf : ∀ mode, 0 ≤ f mode) :
    (∑ selector : PositiveObservedChildSelector N m observed,
        f (selector.q.1 (otherQuadraticSlot selector.observedSlot))) ≤
      8 * ∑ mode : Lattice.Site N, f mode := by
  classical
  let coord := observedChildSelectorCoordinates
    (m := m) (observed := observed)
  have hinj : Function.Injective coord :=
    observedChildSelectorCoordinates_injective
  calc
    (∑ selector : PositiveObservedChildSelector N m observed,
        f (selector.q.1 (otherQuadraticSlot selector.observedSlot))) =
        ∑ selector : PositiveObservedChildSelector N m observed,
          f (coord selector).1 := rfl
    _ = ∑ entry ∈ Finset.univ.image coord, f entry.1 := by
      rw [Finset.sum_image]
      exact hinj.injOn
    _ ≤ ∑ entry : Lattice.Site N × ((Fin 2 × Fin 2) × Fin 2),
        f entry.1 := by
      exact Finset.sum_le_univ_sum_of_nonneg (fun entry ↦ hf entry.1)
    _ = 8 * ∑ mode : Lattice.Site N, f mode := by
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mode _
      ring

/-- Coordinates determining a repeated-away representative. -/
def repeatedAwayCoordinates {N : Nat} [NeZero N]
    (q : QuadraticPhaseTerm N) : Lattice.Site N × (Fin 2 × Fin 2) :=
  (q.1 0, q.2)

/-- On the repeated-away stratum, the coordinates are injective. -/
theorem repeatedAwayCoordinates_injOn
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Set.InjOn repeatedAwayCoordinates
      (↑(repeatedAwayCounterrotatingSameSignRepresentatives N m observed) :
        Set (QuadraticPhaseTerm N)) := by
  intro left hleft right hright h
  have hlbase := Finset.mem_filter.mp hleft
  have hrbase := Finset.mem_filter.mp hright
  have hlparts :=
    (mem_positiveRepeatedChildSameSignRepresentatives_iff
      m observed left).1 hlbase.1
  have hrparts :=
    (mem_positiveRepeatedChildSameSignRepresentatives_iff
      m observed right).1 hrbase.1
  change (left.1 0, left.2) = (right.1 0, right.2) at h
  have hzero : left.1 0 = right.1 0 :=
    congrArg (fun x : Lattice.Site N × (Fin 2 × Fin 2) ↦ x.1) h
  have hsign : left.2 = right.2 :=
    congrArg (fun x : Lattice.Site N × (Fin 2 × Fin 2) ↦ x.2) h
  apply Prod.ext
  · funext r
    fin_cases r
    · exact hzero
    · exact hlparts.2.1.1.symm.trans
        (hzero.trans hrparts.2.1.1)
  · exact hsign

/-- The canonical repeated-away filter has at most four sign copies above a
child mode. -/
theorem sum_repeatedAwayCounterrotating_child_le_four_mul
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (f : Lattice.Site N → Real)
    (hf : ∀ mode, 0 ≤ f mode) :
    (∑ q ∈ repeatedAwayCounterrotatingSameSignRepresentatives N m observed,
        f (q.1 0)) ≤ 4 * ∑ mode : Lattice.Site N, f mode := by
  classical
  let source := repeatedAwayCounterrotatingSameSignRepresentatives N m observed
  let coord := repeatedAwayCoordinates (N := N)
  have hinj : Set.InjOn coord ↑source := by
    simpa [source, coord] using repeatedAwayCoordinates_injOn m observed
  calc
    (∑ q ∈ source, f (q.1 0)) =
        ∑ q ∈ source, f (coord q).1 := rfl
    _ = ∑ entry ∈ source.image coord, f entry.1 := by
      rw [Finset.sum_image]
      exact hinj
    _ ≤ ∑ entry : Lattice.Site N × (Fin 2 × Fin 2),
        f entry.1 := by
      exact Finset.sum_le_univ_sum_of_nonneg (fun entry ↦ hf entry.1)
    _ = 4 * ∑ mode : Lattice.Site N, f mode := by
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mode _
      ring

/-! ## The remaining acoustic moment -/

/-- The exact weighted inverse-frequency moment left by the sign-zero
observed-child correction after vertex/action cancellation.  The zero mode
contributes zero under Lean's totalized division; every physical selector
uses a strictly positive other frequency. -/
def observedChildAcousticInverseMoment
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Real :=
  ∑ other : OrderedModeIndex N,
    repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
        (orderedIndexEquiv.symm observed) other ^ 2 /
      orderedModeFrequency (harmonicHermitian m) other

theorem observedChildAcousticInverseMoment_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    0 ≤ observedChildAcousticInverseMoment m observed := by
  unfold observedChildAcousticInverseMoment
  exact Finset.sum_nonneg fun other _ ↦
    div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

/-- Site indexing and ordered indexing give the same acoustic moment. -/
theorem sum_site_repeatedCoefficient_sq_div_frequency_eq_acousticMoment
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    (∑ other : Lattice.Site N,
      repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm observed) (orderedIndexEquiv.symm other) ^ 2 /
        modeFrequency m other) =
      observedChildAcousticInverseMoment m observed := by
  unfold observedChildAcousticInverseMoment
  apply Fintype.sum_equiv orderedIndexEquiv.symm
  intro other
  simp [orderedModeFrequency_harmonicHermitian_eq]

/-- For a fixed common mode, Parseval and a frequency ceiling control the
frequency-weighted repeated coefficient sum. -/
theorem sum_frequency_mul_repeatedCoefficient_sq_fixed_common_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (common : OrderedModeIndex N) (ceiling : Real)
    (hceiling : 0 ≤ ceiling)
    (hfrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling) :
    (∑ other : OrderedModeIndex N,
      orderedModeFrequency (harmonicHermitian m) other *
        repeatedCubicCoefficient
          (harmonicNormalizedEdgeFrame m) common other ^ 2) ≤ ceiling := by
  calc
    (∑ other : OrderedModeIndex N,
      orderedModeFrequency (harmonicHermitian m) other *
        repeatedCubicCoefficient
          (harmonicNormalizedEdgeFrame m) common other ^ 2) ≤
        ∑ other : OrderedModeIndex N, ceiling *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) common other ^ 2 := by
      apply Finset.sum_le_sum
      intro other _
      exact mul_le_mul_of_nonneg_right (hfrequency other) (sq_nonneg _)
    _ = ceiling * inverseParticipationRatio
        (harmonicNormalizedEdgeFrame m) common := by
      rw [← Finset.mul_sum,
        sum_harmonicRepeatedCubicCoefficient_sq_eq_ipr]
    _ ≤ ceiling * 1 := by
      exact mul_le_mul_of_nonneg_left
        (inverseParticipationRatio_le_one
          (harmonicNormalizedEdgeFrame m)
          (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) common)
        hceiling
    _ = ceiling := mul_one _

/-- With the remaining child fixed, the unconditional Bessel estimate gives
the analogous frequency-weighted bound. -/
theorem sum_frequency_mul_repeatedCoefficient_sq_fixed_child_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (child : OrderedModeIndex N) (ceiling : Real)
    (hceiling : 0 ≤ ceiling)
    (hfrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling) :
    (∑ common : OrderedModeIndex N,
      orderedModeFrequency (harmonicHermitian m) common *
        repeatedCubicCoefficient
          (harmonicNormalizedEdgeFrame m) common child ^ 2) ≤ ceiling := by
  calc
    (∑ common : OrderedModeIndex N,
      orderedModeFrequency (harmonicHermitian m) common *
        repeatedCubicCoefficient
          (harmonicNormalizedEdgeFrame m) common child ^ 2) ≤
        ∑ common : OrderedModeIndex N, ceiling *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) common child ^ 2 := by
      apply Finset.sum_le_sum
      intro common _
      exact mul_le_mul_of_nonneg_right (hfrequency common) (sq_nonneg _)
    _ = ceiling * (∑ common : OrderedModeIndex N,
        repeatedCubicCoefficient
          (harmonicNormalizedEdgeFrame m) common child ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ceiling * 1 := by
      exact mul_le_mul_of_nonneg_left
        (sum_repeatedCubicCoefficient_sq_fixed_child_le_one
          (harmonicNormalizedEdgeFrame m) (by simp [Lattice.Site])
          (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) child)
        hceiling
    _ = ceiling := mul_one _

/-- The normalized vertex of any observed-child selector has two observed
legs and one other leg, regardless of the retained input orientation. -/
theorem normalizedInteractionWeight_observedChild_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    normalizedInteractionWeight m
        (quadraticCollisionModes observed selector.q) ≤
      (modeFrequency m observed / 2) ^ 2 *
        (modeFrequency m
          (selector.q.1 (otherQuadraticSlot selector.observedSlot)) / 2) *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm observed)
          (orderedIndexEquiv.symm
            (selector.q.1
              (otherQuadraticSlot selector.observedSlot))) ^ 2 := by
  generalize hslot : selector.observedSlot = slot
  fin_cases slot
  · have hobserved : observed = selector.q.1 0 := by
      simpa [hslot] using selector.observed_only.1
    have hmodes : quadraticCollisionModes observed selector.q =
        ![observed, observed, selector.q.1 1] := by
      funext r
      fin_cases r
      · rfl
      · exact hobserved.symm
      · rfl
    rw [hmodes]
    simpa [hslot, otherQuadraticSlot] using
      normalizedInteractionWeight_repeated_zero_one_le_frame
        m hsimple observed (selector.q.1 1)
  · have hobserved : observed = selector.q.1 1 := by
      simpa [hslot] using selector.observed_only.1
    have hmodes : quadraticCollisionModes observed selector.q =
        ![observed, selector.q.1 0, observed] := by
      funext r
      fin_cases r
      · rfl
      · rfl
      · exact hobserved.symm
    rw [hmodes]
    simpa [hslot, otherQuadraticSlot] using
      normalizedInteractionWeight_repeated_zero_two_le_frame
        m hsimple observed (selector.q.1 0)

/-- The repeated-away normalized vertex has the repeated child as common
label and the observed output as remaining label. -/
theorem normalizedInteractionWeight_repeatedAway_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hq : q ∈ repeatedAwayCounterrotatingSameSignRepresentatives
      N m observed) :
    normalizedInteractionWeight m (quadraticCollisionModes observed q) ≤
      (modeFrequency m (q.1 0) / 2) ^ 2 *
        (modeFrequency m observed / 2) *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm (q.1 0))
          (orderedIndexEquiv.symm observed) ^ 2 := by
  have hbase := Finset.mem_filter.mp hq
  have hparts :=
    (mem_positiveRepeatedChildSameSignRepresentatives_iff
      m observed q).1 hbase.1
  have hrepeat : q.1 0 = q.1 1 := hparts.2.1.1
  have hmodes : quadraticCollisionModes observed q =
      ![observed, q.1 1, q.1 1] := by
    funext r
    fin_cases r
    · rfl
    · exact hrepeat
    · rfl
  rw [hmodes, hrepeat]
  exact normalizedInteractionWeight_repeated_one_two_le_frame
    m hsimple (q.1 1) observed

/-- A single all-equal coefficient square is at most one. -/
theorem repeatedCubicCoefficient_self_sq_le_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mode : OrderedModeIndex N) :
    repeatedCubicCoefficient
      (harmonicNormalizedEdgeFrame m) mode mode ^ 2 ≤ 1 := by
  have hsingle :
      repeatedCubicCoefficient
          (harmonicNormalizedEdgeFrame m) mode mode ^ 2 ≤
        ∑ common : OrderedModeIndex N,
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) common mode ^ 2 :=
    Finset.single_le_sum
      (f := fun common : OrderedModeIndex N ↦
        repeatedCubicCoefficient
          (harmonicNormalizedEdgeFrame m) common mode ^ 2)
      (fun common _ ↦ sq_nonneg _) (Finset.mem_univ mode)
  exact hsingle.trans
    (sum_repeatedCubicCoefficient_sq_fixed_child_le_one
      (harmonicNormalizedEdgeFrame m) (by simp [Lattice.Site])
      (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) mode)

/-- All-equal channel-five parameters are determined by two signs and two
binary placement slots. -/
def allEqualChannelFiveCoordinates {N : Nat} [NeZero N]
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2)) :
    (Fin 2 × Fin 2) × (Fin 2 × Fin 2) :=
  (parameter.1.2, parameter.2)

theorem allEqualChannelFiveCoordinates_injOn
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Set.InjOn allEqualChannelFiveCoordinates
      (↑(positiveAllEqualChannelFiveParameters N m observed) :
        Set (QuadraticPhaseTerm N × (Fin 2 × Fin 2))) := by
  intro left hleft right hright h
  have hl :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed left).1 hleft
  have hr :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed right).1 hright
  have hlq :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed left.1).1 hl.1
  have hrq :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed right.1).1 hr.1
  change (left.1.2, left.2) = (right.1.2, right.2) at h
  have hsign : left.1.2 = right.1.2 :=
    congrArg (fun x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) ↦ x.1) h
  have hplacement : left.2 = right.2 :=
    congrArg (fun x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) ↦ x.2) h
  have hmodes : left.1.1 = right.1.1 := by
    funext input
    fin_cases input
    · exact hlq.2.2.1.symm.trans hrq.2.2.1
    · exact hlq.2.2.2.symm.trans hrq.2.2.2
  apply Prod.ext
  · exact Prod.ext hmodes hsign
  · exact hplacement

theorem card_positiveAllEqualChannelFiveParameters_le_sixteen
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    (positiveAllEqualChannelFiveParameters N m observed).card ≤ 16 := by
  classical
  let source := positiveAllEqualChannelFiveParameters N m observed
  let coord := allEqualChannelFiveCoordinates (N := N)
  have hinj : Set.InjOn coord ↑source := by
    simpa [source, coord] using
      allEqualChannelFiveCoordinates_injOn m observed
  calc
    source.card = (source.image coord).card := by
      symm
      exact Finset.card_image_of_injOn hinj
    _ ≤ (Finset.univ : Finset ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 16 := by decide

/-! ## Vertex/action cancellation algebra -/

@[simp] theorem abs_interactionSign_coefficient
    (sign : InteractionSign) : |sign.coefficient| = 1 := by
  cases sign <;> simp [InteractionSign.coefficient]

/-- Algebraic cancellation in the observed-child sign-zero sector.  Exactly
one inverse power of the other frequency remains. -/
theorem signZero_staticFactor_le_acoustic
    (kappa energyValue energyBound observedFrequency otherFrequency
      coefficientSq vertex : Real) (sign : InteractionSign)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : 0 ≤ energyValue)
    (hEnergyBound : energyValue ≤ energyBound)
    (hObservedFrequency : 0 < observedFrequency)
    (hOtherFrequency : 0 < otherFrequency)
    (hVertex : vertex ≤
      (observedFrequency / 2) ^ 2 * (otherFrequency / 2) * coefficientSq)
    (hCoefficientSq : 0 ≤ coefficientSq) :
    |(-4 : Real) * sign.coefficient *
        ((energyValue / observedFrequency) *
          (energyValue / observedFrequency))| *
        (kappa ^ 2 * vertex) * (2 / otherFrequency) ^ 2 ≤
      2 * kappa ^ 2 * energyBound ^ 2 *
        (coefficientSq / otherFrequency) := by
  have hreplace :
      |(-4 : Real) * sign.coefficient *
          ((energyValue / observedFrequency) *
            (energyValue / observedFrequency))| *
          (kappa ^ 2 * vertex) * (2 / otherFrequency) ^ 2 ≤
        |(-4 : Real) * sign.coefficient *
          ((energyValue / observedFrequency) *
            (energyValue / observedFrequency))| *
          (kappa ^ 2 * ((observedFrequency / 2) ^ 2 *
            (otherFrequency / 2) * coefficientSq)) *
          (2 / otherFrequency) ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hVertex (sq_nonneg kappa))
        (abs_nonneg _)) (sq_nonneg _)
  calc
    |(-4 : Real) * sign.coefficient *
        ((energyValue / observedFrequency) *
          (energyValue / observedFrequency))| *
        (kappa ^ 2 * vertex) * (2 / otherFrequency) ^ 2 ≤
      |(-4 : Real) * sign.coefficient *
        ((energyValue / observedFrequency) *
          (energyValue / observedFrequency))| *
        (kappa ^ 2 * ((observedFrequency / 2) ^ 2 *
          (otherFrequency / 2) * coefficientSq)) *
        (2 / otherFrequency) ^ 2 := hreplace
    _ = 2 * kappa ^ 2 * energyValue ^ 2 *
        (coefficientSq / otherFrequency) := by
      rw [abs_mul, abs_mul, abs_interactionSign_coefficient]
      rw [show |(-4 : Real)| = 4 by norm_num,
        abs_of_nonneg (mul_nonneg
          (div_nonneg hEnergy hObservedFrequency.le)
          (div_nonneg hEnergy hObservedFrequency.le))]
      field_simp [hObservedFrequency.ne', hOtherFrequency.ne']
      ring
    _ ≤ 2 * kappa ^ 2 * energyBound ^ 2 *
        (coefficientSq / otherFrequency) := by
      have heSq : energyValue ^ 2 ≤ energyBound ^ 2 :=
        (sq_le_sq₀ hEnergy hEnergyBoundNonneg).2 hEnergyBound
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heSq
          (mul_nonneg (by norm_num) (sq_nonneg kappa)))
        (div_nonneg hCoefficientSq hOtherFrequency.le)

/-- Algebraic cancellation for the observed-child all-plus sector. -/
theorem observedCounterrotating_staticFactor_le
    (kappa energyValue energyBound observedFrequency otherFrequency
      coefficientSq vertex : Real) (sign : InteractionSign)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : 0 ≤ energyValue)
    (hEnergyBound : energyValue ≤ energyBound)
    (hObservedFrequency : 0 < observedFrequency)
    (hOtherFrequency : 0 ≤ otherFrequency)
    (hVertex : vertex ≤
      (observedFrequency / 2) ^ 2 * (otherFrequency / 2) * coefficientSq)
    (hCoefficientSq : 0 ≤ coefficientSq) :
    |(-2 : Real) * sign.coefficient *
        ((energyValue / observedFrequency) *
          (energyValue / observedFrequency))| *
        (kappa ^ 2 * vertex) * (2 / observedFrequency) ^ 2 ≤
      (kappa ^ 2 * energyBound ^ 2 / observedFrequency ^ 2) *
        (otherFrequency * coefficientSq) := by
  have hreplace :
      |(-2 : Real) * sign.coefficient *
          ((energyValue / observedFrequency) *
            (energyValue / observedFrequency))| *
          (kappa ^ 2 * vertex) * (2 / observedFrequency) ^ 2 ≤
        |(-2 : Real) * sign.coefficient *
          ((energyValue / observedFrequency) *
            (energyValue / observedFrequency))| *
          (kappa ^ 2 * ((observedFrequency / 2) ^ 2 *
            (otherFrequency / 2) * coefficientSq)) *
          (2 / observedFrequency) ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hVertex (sq_nonneg kappa))
        (abs_nonneg _)) (sq_nonneg _)
  calc
    |(-2 : Real) * sign.coefficient *
        ((energyValue / observedFrequency) *
          (energyValue / observedFrequency))| *
        (kappa ^ 2 * vertex) * (2 / observedFrequency) ^ 2 ≤
      |(-2 : Real) * sign.coefficient *
        ((energyValue / observedFrequency) *
          (energyValue / observedFrequency))| *
        (kappa ^ 2 * ((observedFrequency / 2) ^ 2 *
          (otherFrequency / 2) * coefficientSq)) *
        (2 / observedFrequency) ^ 2 := hreplace
    _ = (kappa ^ 2 * energyValue ^ 2 / observedFrequency ^ 2) *
        (otherFrequency * coefficientSq) := by
      rw [abs_mul, abs_mul, abs_interactionSign_coefficient]
      rw [show |(-2 : Real)| = 2 by norm_num,
        abs_of_nonneg (mul_nonneg
          (div_nonneg hEnergy hObservedFrequency.le)
          (div_nonneg hEnergy hObservedFrequency.le))]
      field_simp [hObservedFrequency.ne']
    _ ≤ (kappa ^ 2 * energyBound ^ 2 / observedFrequency ^ 2) *
        (otherFrequency * coefficientSq) := by
      have heSq : energyValue ^ 2 ≤ energyBound ^ 2 :=
        (sq_le_sq₀ hEnergy hEnergyBoundNonneg).2 hEnergyBound
      have hdenom : 0 ≤ observedFrequency ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left heSq (sq_nonneg kappa)) hdenom)
        (mul_nonneg hOtherFrequency hCoefficientSq)

/-- Algebraic cancellation for the repeated-away all-plus sector. -/
theorem repeatedAway_staticFactor_le
    (kappa observedEnergy childEnergy energyBound observedFrequency
      childFrequency coefficientSq vertex : Real) (sign : InteractionSign)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hObservedEnergy : 0 ≤ observedEnergy)
    (hChildEnergy : 0 ≤ childEnergy)
    (hObservedEnergyBound : observedEnergy ≤ energyBound)
    (hChildEnergyBound : childEnergy ≤ energyBound)
    (hObservedFrequency : 0 < observedFrequency)
    (hChildFrequency : 0 < childFrequency)
    (hVertex : vertex ≤
      (childFrequency / 2) ^ 2 * (observedFrequency / 2) * coefficientSq)
    (hCoefficientSq : 0 ≤ coefficientSq) :
    |2 * sign.coefficient *
        (observedEnergy / observedFrequency) *
        (childEnergy / childFrequency)| *
        (kappa ^ 2 * vertex) * (2 / observedFrequency) ^ 2 ≤
      (kappa ^ 2 * energyBound ^ 2 / observedFrequency ^ 2) *
        (childFrequency * coefficientSq) := by
  have hreplace :
      |2 * sign.coefficient *
          (observedEnergy / observedFrequency) *
          (childEnergy / childFrequency)| *
          (kappa ^ 2 * vertex) * (2 / observedFrequency) ^ 2 ≤
        |2 * sign.coefficient *
          (observedEnergy / observedFrequency) *
          (childEnergy / childFrequency)| *
          (kappa ^ 2 * ((childFrequency / 2) ^ 2 *
            (observedFrequency / 2) * coefficientSq)) *
          (2 / observedFrequency) ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hVertex (sq_nonneg kappa))
        (abs_nonneg _)) (sq_nonneg _)
  calc
    |2 * sign.coefficient *
        (observedEnergy / observedFrequency) *
        (childEnergy / childFrequency)| *
        (kappa ^ 2 * vertex) * (2 / observedFrequency) ^ 2 ≤
      |2 * sign.coefficient *
        (observedEnergy / observedFrequency) *
        (childEnergy / childFrequency)| *
        (kappa ^ 2 * ((childFrequency / 2) ^ 2 *
          (observedFrequency / 2) * coefficientSq)) *
        (2 / observedFrequency) ^ 2 := hreplace
    _ = (kappa ^ 2 * (observedEnergy * childEnergy) /
          observedFrequency ^ 2) * (childFrequency * coefficientSq) := by
      rw [abs_mul, abs_mul, abs_mul, abs_interactionSign_coefficient]
      rw [abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
        abs_of_nonneg (div_nonneg hObservedEnergy hObservedFrequency.le),
        abs_of_nonneg (div_nonneg hChildEnergy hChildFrequency.le)]
      field_simp [hObservedFrequency.ne', hChildFrequency.ne']
    _ ≤ (kappa ^ 2 * energyBound ^ 2 / observedFrequency ^ 2) *
        (childFrequency * coefficientSq) := by
      have hproduct : observedEnergy * childEnergy ≤ energyBound ^ 2 := by
        calc
          observedEnergy * childEnergy ≤ energyBound * energyBound :=
            mul_le_mul hObservedEnergyBound hChildEnergyBound
              hChildEnergy hEnergyBoundNonneg
          _ = energyBound ^ 2 := by ring
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hproduct (sq_nonneg kappa))
          (sq_nonneg observedFrequency))
        (mul_nonneg hChildFrequency.le hCoefficientSq)

/-- Algebraic cancellation for one all-equal channel-five parameter. -/
theorem allEqual_staticFactor_le
    (kappa energyValue energyBound frequency coefficientSq vertex : Real)
    (sign : InteractionSign)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : 0 ≤ energyValue)
    (hEnergyBound : energyValue ≤ energyBound)
    (hFrequency : 0 < frequency)
    (hVertex : vertex ≤
      (frequency / 2) ^ 2 * (frequency / 2) * coefficientSq)
    (hCoefficientSq : 0 ≤ coefficientSq) :
    |sign.coefficient * (energyValue / frequency) ^ 2| *
        (kappa ^ 2 * vertex) * (2 / frequency) ^ 2 ≤
      (kappa ^ 2 * energyBound ^ 2 / (2 * frequency)) * coefficientSq := by
  have hreplace :
      |sign.coefficient * (energyValue / frequency) ^ 2| *
          (kappa ^ 2 * vertex) * (2 / frequency) ^ 2 ≤
        |sign.coefficient * (energyValue / frequency) ^ 2| *
          (kappa ^ 2 * ((frequency / 2) ^ 2 *
            (frequency / 2) * coefficientSq)) * (2 / frequency) ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hVertex (sq_nonneg kappa))
        (abs_nonneg _)) (sq_nonneg _)
  calc
    |sign.coefficient * (energyValue / frequency) ^ 2| *
        (kappa ^ 2 * vertex) * (2 / frequency) ^ 2 ≤
      |sign.coefficient * (energyValue / frequency) ^ 2| *
        (kappa ^ 2 * ((frequency / 2) ^ 2 *
          (frequency / 2) * coefficientSq)) * (2 / frequency) ^ 2 := hreplace
    _ = (kappa ^ 2 * energyValue ^ 2 / (2 * frequency)) *
        coefficientSq := by
      rw [abs_mul, abs_interactionSign_coefficient,
        one_mul, abs_of_nonneg (sq_nonneg _)]
      field_simp [hFrequency.ne']
    _ ≤ (kappa ^ 2 * energyBound ^ 2 / (2 * frequency)) *
        coefficientSq := by
      have heSq : energyValue ^ 2 ≤ energyBound ^ 2 :=
        (sq_le_sq₀ hEnergy hEnergyBoundNonneg).2 hEnergyBound
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left heSq (sq_nonneg kappa))
          (mul_nonneg (by norm_num) hFrequency.le)) hCoefficientSq

/-! ## Static-mass bounds -/

/-- The complete sign-zero static mass is controlled by the exact weighted
acoustic moment.  This is the sharp deterministic endpoint available from
frame orthogonality without an acoustic input. -/
theorem observedChildSignZeroStaticMass_le_acousticMoment
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed) :
    observedChildSignZeroStaticMass m kappa energy observed ≤
      16 * kappa ^ 2 * energyBound ^ 2 *
        observedChildAcousticInverseMoment m observed := by
  classical
  let common : OrderedModeIndex N := orderedIndexEquiv.symm observed
  let f : Lattice.Site N → Real := fun other ↦
    repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
        common (orderedIndexEquiv.symm other) ^ 2 /
      modeFrequency m other
  have hf (other : Lattice.Site N) : 0 ≤ f other := by
    exact div_nonneg (sq_nonneg _) (modeFrequency_nonneg m other)
  have hterm (selector : PositiveObservedChildSelector N m observed) :
      |observedChildSignZeroNetWeight m energy observed selector| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed selector.q)) *
          (2 / modeFrequency m
            (selector.q.1
              (otherQuadraticSlot selector.observedSlot))) ^ 2 ≤
        2 * kappa ^ 2 * energyBound ^ 2 *
          f (selector.q.1
            (otherQuadraticSlot selector.observedSlot)) := by
    let other := selector.q.1 (otherQuadraticSlot selector.observedSlot)
    let coefficientSq :=
      repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
        common (orderedIndexEquiv.symm other) ^ 2
    have hvertex := normalizedInteractionWeight_observedChild_le_frame
      m hsimple observed selector
    have hother : 0 < modeFrequency m other := by
      exact otherFrequency_pos_of_observedChildSelector m observed selector
    have halgebra := signZero_staticFactor_le_acoustic
      kappa (energy observed) energyBound (modeFrequency m observed)
      (modeFrequency m other) coefficientSq
      (normalizedInteractionWeight m
        (quadraticCollisionModes observed selector.q))
      (quadraticInputInteractionSign selector.q
        (otherQuadraticSlot selector.observedSlot))
      hEnergyBoundNonneg (hEnergy observed) (hEnergyBound observed)
      hObserved hother hvertex (sq_nonneg _)
    simpa [observedChildSignZeroNetWeight, modeAction, other,
      coefficientSq, common, f] using halgebra
  unfold observedChildSignZeroStaticMass
  calc
    (∑ selector ∈ observedChildSignZeroSelectors m observed,
      |observedChildSignZeroNetWeight m energy observed selector| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed selector.q)) *
          (2 / modeFrequency m
            (selector.q.1
              (otherQuadraticSlot selector.observedSlot))) ^ 2) ≤
        ∑ selector ∈ observedChildSignZeroSelectors m observed,
          2 * kappa ^ 2 * energyBound ^ 2 *
            f (selector.q.1
              (otherQuadraticSlot selector.observedSlot)) := by
      exact Finset.sum_le_sum fun selector _ ↦ hterm selector
    _ ≤ ∑ selector : PositiveObservedChildSelector N m observed,
        2 * kappa ^ 2 * energyBound ^ 2 *
          f (selector.q.1
            (otherQuadraticSlot selector.observedSlot)) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun selector ↦
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg kappa))
            (sq_nonneg energyBound))
          (hf _)
    _ = 2 * kappa ^ 2 * energyBound ^ 2 *
        (∑ selector : PositiveObservedChildSelector N m observed,
          f (selector.q.1
            (otherQuadraticSlot selector.observedSlot))) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * kappa ^ 2 * energyBound ^ 2 *
        (8 * ∑ other : Lattice.Site N, f other) := by
      exact mul_le_mul_of_nonneg_left
        (sum_observedChildSelector_other_le_eight_mul
          m observed f hf)
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg kappa))
          (sq_nonneg energyBound))
    _ = 16 * kappa ^ 2 * energyBound ^ 2 *
        observedChildAcousticInverseMoment m observed := by
      rw [show (∑ other : Lattice.Site N, f other) =
          observedChildAcousticInverseMoment m observed by
        simpa [f, common] using
          sum_site_repeatedCoefficient_sq_div_frequency_eq_acousticMoment
            m observed]
      ring

/-- Site-indexed form of the fixed-common frequency-weighted Parseval bound. -/
theorem sum_site_frequency_mul_repeatedCoefficient_sq_fixed_common_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (common : Lattice.Site N) (ceiling : Real)
    (hceiling : 0 ≤ ceiling)
    (hfrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling) :
    (∑ other : Lattice.Site N,
      modeFrequency m other *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other) ^ 2) ≤
      ceiling := by
  calc
    (∑ other : Lattice.Site N,
      modeFrequency m other *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm other) ^ 2) =
      ∑ other : OrderedModeIndex N,
        orderedModeFrequency (harmonicHermitian m) other *
          repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
            (orderedIndexEquiv.symm common) other ^ 2 := by
      apply Fintype.sum_equiv orderedIndexEquiv.symm
      intro other
      simp [orderedModeFrequency_harmonicHermitian_eq]
    _ ≤ ceiling :=
      sum_frequency_mul_repeatedCoefficient_sq_fixed_common_le
        m (orderedIndexEquiv.symm common) ceiling hceiling hfrequency

/-- Site-indexed form of the fixed-child frequency-weighted Bessel bound. -/
theorem sum_site_frequency_mul_repeatedCoefficient_sq_fixed_child_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (child : Lattice.Site N) (ceiling : Real)
    (hceiling : 0 ≤ ceiling)
    (hfrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling) :
    (∑ common : Lattice.Site N,
      modeFrequency m common *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm child) ^ 2) ≤
      ceiling := by
  calc
    (∑ common : Lattice.Site N,
      modeFrequency m common *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm common) (orderedIndexEquiv.symm child) ^ 2) =
      ∑ common : OrderedModeIndex N,
        orderedModeFrequency (harmonicHermitian m) common *
          repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
            common (orderedIndexEquiv.symm child) ^ 2 := by
      apply Fintype.sum_equiv orderedIndexEquiv.symm
      intro common
      simp [orderedModeFrequency_harmonicHermitian_eq]
    _ ≤ ceiling :=
      sum_frequency_mul_repeatedCoefficient_sq_fixed_child_le
        m (orderedIndexEquiv.symm child) ceiling hceiling hfrequency

/-- The observed-child all-plus static mass is volume independent once the
observed output frequency is kept explicit. -/
theorem observedChildCounterrotatingStaticMass_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling) :
    observedChildCounterrotatingStaticMass m kappa energy observed ≤
      8 * (kappa ^ 2 * energyBound ^ 2 /
        modeFrequency m observed ^ 2) * ceiling := by
  classical
  let C := kappa ^ 2 * energyBound ^ 2 / modeFrequency m observed ^ 2
  let f : Lattice.Site N → Real := fun other ↦
    modeFrequency m other *
      repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
        (orderedIndexEquiv.symm observed) (orderedIndexEquiv.symm other) ^ 2
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hf (other : Lattice.Site N) : 0 ≤ f other :=
    mul_nonneg (modeFrequency_nonneg m other) (sq_nonneg _)
  have hterm (selector : PositiveObservedChildSelector N m observed) :
      |observedChildSignOneNetWeight m energy observed selector| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed selector.q)) *
          (2 / modeFrequency m observed) ^ 2 ≤
        C * f (selector.q.1
          (otherQuadraticSlot selector.observedSlot)) := by
    let other := selector.q.1 (otherQuadraticSlot selector.observedSlot)
    let coefficientSq := repeatedCubicCoefficient
      (harmonicNormalizedEdgeFrame m) (orderedIndexEquiv.symm observed)
        (orderedIndexEquiv.symm other) ^ 2
    have halgebra := observedCounterrotating_staticFactor_le
      kappa (energy observed) energyBound (modeFrequency m observed)
      (modeFrequency m other) coefficientSq
      (normalizedInteractionWeight m
        (quadraticCollisionModes observed selector.q))
      (quadraticInputInteractionSign selector.q
        (otherQuadraticSlot selector.observedSlot))
      hEnergyBoundNonneg (hEnergy observed) (hEnergyBound observed)
      hObserved (modeFrequency_nonneg m other)
      (normalizedInteractionWeight_observedChild_le_frame
        m hsimple observed selector) (sq_nonneg _)
    simpa [observedChildSignOneNetWeight, modeAction, C, f, other,
      coefficientSq] using halgebra
  unfold observedChildCounterrotatingStaticMass
  calc
    (∑ selector ∈ observedChildCounterrotatingSelectors m observed,
      |observedChildSignOneNetWeight m energy observed selector| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed selector.q)) *
          (2 / modeFrequency m observed) ^ 2) ≤
        ∑ selector ∈ observedChildCounterrotatingSelectors m observed,
          C * f (selector.q.1
            (otherQuadraticSlot selector.observedSlot)) := by
      exact Finset.sum_le_sum fun selector _ ↦ hterm selector
    _ ≤ ∑ selector : PositiveObservedChildSelector N m observed,
        C * f (selector.q.1
          (otherQuadraticSlot selector.observedSlot)) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun selector ↦
        mul_nonneg hC (hf _)
    _ = C * (∑ selector : PositiveObservedChildSelector N m observed,
        f (selector.q.1
          (otherQuadraticSlot selector.observedSlot))) := by
      rw [Finset.mul_sum]
    _ ≤ C * (8 * ∑ other : Lattice.Site N, f other) :=
      mul_le_mul_of_nonneg_left
        (sum_observedChildSelector_other_le_eight_mul m observed f hf) hC
    _ ≤ C * (8 * ceiling) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (sum_site_frequency_mul_repeatedCoefficient_sq_fixed_common_le
            m observed ceiling hCeiling hFrequency) (by norm_num)) hC
    _ = 8 * (kappa ^ 2 * energyBound ^ 2 /
        modeFrequency m observed ^ 2) * ceiling := by
      simp only [C]
      ring

/-- The repeated-away all-plus static mass is likewise volume independent. -/
theorem repeatedAwayCounterrotatingStaticMass_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling) :
    repeatedAwayCounterrotatingStaticMass m kappa energy observed ≤
      4 * (kappa ^ 2 * energyBound ^ 2 /
        modeFrequency m observed ^ 2) * ceiling := by
  classical
  let C := kappa ^ 2 * energyBound ^ 2 / modeFrequency m observed ^ 2
  let f : Lattice.Site N → Real := fun child ↦
    modeFrequency m child *
      repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
        (orderedIndexEquiv.symm child) (orderedIndexEquiv.symm observed) ^ 2
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hf (child : Lattice.Site N) : 0 ≤ f child :=
    mul_nonneg (modeFrequency_nonneg m child) (sq_nonneg _)
  have hterm (q : QuadraticPhaseTerm N)
      (hq : q ∈ repeatedAwayCounterrotatingSameSignRepresentatives
        N m observed) :
      |repeatedAwaySameSignTwoCopyWeight m energy observed q| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed q)) *
          (2 / modeFrequency m observed) ^ 2 ≤ C * f (q.1 0) := by
    have hbase := Finset.mem_filter.mp hq
    have hparts :=
      (mem_positiveRepeatedChildSameSignRepresentatives_iff
        m observed q).1 hbase.1
    have hPositive : PositiveModeTuple m
        (quadraticCollisionModes observed q) := by
      simpa [positiveQuadraticSwapOrbitRepresentatives] using
        (Finset.mem_filter.mp hparts.1).2
    have hChild : 0 < modeFrequency m (q.1 0) := by
      simpa [quadraticCollisionModes] using hPositive (1 : Fin 3)
    let coefficientSq := repeatedCubicCoefficient
      (harmonicNormalizedEdgeFrame m) (orderedIndexEquiv.symm (q.1 0))
        (orderedIndexEquiv.symm observed) ^ 2
    have halgebra := repeatedAway_staticFactor_le
      kappa (energy observed) (energy (q.1 0)) energyBound
      (modeFrequency m observed) (modeFrequency m (q.1 0)) coefficientSq
      (normalizedInteractionWeight m (quadraticCollisionModes observed q))
      (quadraticInputInteractionSign q 0)
      hEnergyBoundNonneg (hEnergy observed) (hEnergy (q.1 0))
      (hEnergyBound observed) (hEnergyBound (q.1 0)) hObserved hChild
      (normalizedInteractionWeight_repeatedAway_le_frame
        m hsimple observed q hq) (sq_nonneg _)
    simpa [repeatedAwaySameSignTwoCopyWeight, modeAction, C, f,
      coefficientSq] using halgebra
  unfold repeatedAwayCounterrotatingStaticMass
  calc
    (∑ q ∈ repeatedAwayCounterrotatingSameSignRepresentatives N m observed,
      |repeatedAwaySameSignTwoCopyWeight m energy observed q| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed q)) *
          (2 / modeFrequency m observed) ^ 2) ≤
        ∑ q ∈ repeatedAwayCounterrotatingSameSignRepresentatives N m observed,
          C * f (q.1 0) := by
      exact Finset.sum_le_sum fun q hq ↦ hterm q hq
    _ = C * (∑ q ∈
        repeatedAwayCounterrotatingSameSignRepresentatives N m observed,
          f (q.1 0)) := by
      rw [Finset.mul_sum]
    _ ≤ C * (4 * ∑ child : Lattice.Site N, f child) :=
      mul_le_mul_of_nonneg_left
        (sum_repeatedAwayCounterrotating_child_le_four_mul
          m observed f hf) hC
    _ ≤ C * (4 * ceiling) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (sum_site_frequency_mul_repeatedCoefficient_sq_fixed_child_le
            m observed ceiling hCeiling hFrequency) (by norm_num)) hC
    _ = 4 * (kappa ^ 2 * energyBound ^ 2 /
        modeFrequency m observed ^ 2) * ceiling := by
      simp only [C]
      ring

/-- Every all-equal channel-five tuple is the physical triple
`[observed, observed, observed]`. -/
theorem normalizedInteractionWeight_allEqualChannelFive_le_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2))
    (hParameter : parameter ∈
      positiveAllEqualChannelFiveParameters N m observed) :
    normalizedInteractionWeight m
        (quadraticCollisionModes observed parameter.1) ≤
      (modeFrequency m observed / 2) ^ 2 *
        (modeFrequency m observed / 2) *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
          (orderedIndexEquiv.symm observed)
          (orderedIndexEquiv.symm observed) ^ 2 := by
  have hparts :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed parameter).1 hParameter
  have hqparts :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed parameter.1).1 hparts.1
  have hall := hqparts.2.2
  have hmodes : quadraticCollisionModes observed parameter.1 =
      ![observed, observed, observed] := by
    funext r
    fin_cases r
    · rfl
    · exact hall.1.symm
    · exact hall.2.symm
  rw [hmodes]
  exact normalizedInteractionWeight_repeated_zero_one_le_frame
    m hsimple observed observed

/-- The all-equal channel-five static mass is bounded independently of
volume; the factor eight is the exact coarse consequence of at most sixteen
parameters and the surviving one-half from vertex/action cancellation. -/
theorem allEqualChannelFiveStaticMass_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed) :
    allEqualChannelFiveStaticMass m kappa energy observed ≤
      8 * kappa ^ 2 * energyBound ^ 2 / modeFrequency m observed := by
  classical
  let coefficientSq := repeatedCubicCoefficient
    (harmonicNormalizedEdgeFrame m) (orderedIndexEquiv.symm observed)
      (orderedIndexEquiv.symm observed) ^ 2
  let C := kappa ^ 2 * energyBound ^ 2 /
    (2 * modeFrequency m observed)
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (by norm_num) hObserved.le)
  have hcoefficient : coefficientSq ≤ 1 := by
    simpa [coefficientSq] using repeatedCubicCoefficient_self_sq_le_one
      m (orderedIndexEquiv.symm observed)
  have hterm (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2))
      (hParameter : parameter ∈
        positiveAllEqualChannelFiveParameters N m observed) :
      |(quadraticInputInteractionSign parameter.1
          parameter.2.1).coefficient *
        modeAction energy (modeFrequency m) observed ^ 2| *
        (kappa ^ 2 * normalizedInteractionWeight m
          (quadraticCollisionModes observed parameter.1)) *
        (2 / modeFrequency m observed) ^ 2 ≤ C := by
    have halgebra := allEqual_staticFactor_le
      kappa (energy observed) energyBound (modeFrequency m observed)
      coefficientSq
      (normalizedInteractionWeight m
        (quadraticCollisionModes observed parameter.1))
      (quadraticInputInteractionSign parameter.1 parameter.2.1)
      hEnergyBoundNonneg (hEnergy observed) (hEnergyBound observed)
      hObserved
      (normalizedInteractionWeight_allEqualChannelFive_le_frame
        m hsimple observed parameter hParameter) (sq_nonneg _)
    have hfirst :
        |(quadraticInputInteractionSign parameter.1
            parameter.2.1).coefficient *
          modeAction energy (modeFrequency m) observed ^ 2| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed parameter.1)) *
          (2 / modeFrequency m observed) ^ 2 ≤ C * coefficientSq := by
      simpa [modeAction, C, coefficientSq] using halgebra
    exact hfirst.trans (by
      simpa using mul_le_mul_of_nonneg_left hcoefficient hC)
  unfold allEqualChannelFiveStaticMass
  calc
    (∑ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
      |(quadraticInputInteractionSign parameter.1
          parameter.2.1).coefficient *
        modeAction energy (modeFrequency m) observed ^ 2| *
        (kappa ^ 2 * normalizedInteractionWeight m
          (quadraticCollisionModes observed parameter.1)) *
        (2 / modeFrequency m observed) ^ 2) ≤
      ∑ _parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
        C := by
      exact Finset.sum_le_sum fun parameter hParameter ↦
        hterm parameter hParameter
    _ = ((positiveAllEqualChannelFiveParameters N m observed).card : Real) *
        C := by simp
    _ ≤ 16 * C := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast
          card_positiveAllEqualChannelFiveParameters_le_sixteen m observed) hC
    _ = 8 * kappa ^ 2 * energyBound ^ 2 /
        modeFrequency m observed := by
      simp only [C]
      field_simp [hObserved.ne']
      ring

/-- Aggregate static mass: three sectors are genuinely volume-independent,
and the sign-zero sector is exactly isolated in the weighted acoustic
moment. -/
theorem qLevelOffResonantCorrectionStaticMass_le_acousticMoment_add_uniform
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling) :
    qLevelOffResonantCorrectionStaticMass m kappa energy observed ≤
      16 * kappa ^ 2 * energyBound ^ 2 *
          observedChildAcousticInverseMoment m observed +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed := by
  have hrepeated := repeatedAwayCounterrotatingStaticMass_le
    m kappa energy observed energyBound ceiling hsimple
    hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency
  have hzero := observedChildSignZeroStaticMass_le_acousticMoment
    m kappa energy observed energyBound hsimple
    hEnergyBoundNonneg hEnergy hEnergyBound hObserved
  have hcounter := observedChildCounterrotatingStaticMass_le
    m kappa energy observed energyBound ceiling hsimple
    hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency
  have hall := allEqualChannelFiveStaticMass_le
    m kappa energy observed energyBound hsimple
    hEnergyBoundNonneg hEnergy hEnergyBound hObserved
  unfold qLevelOffResonantCorrectionStaticMass
    observedChildOffResonantStaticMass
  linarith

/-- The existing exact inverse-time theorem now carries an explicit true
volume bound.  No claim is made that the acoustic moment is uniformly
bounded. -/
theorem abs_qLevelOffResonantCorrectionSum_le_acousticMoment_add_uniform_over_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    {time : Real} (hTime : 0 < time) :
    |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 *
          observedChildAcousticInverseMoment m observed +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed) / time := by
  have hbase := abs_qLevelOffResonantCorrectionSum_le_inverseTime
    m kappa energy observed hTime hObserved
  exact hbase.trans (div_le_div_of_nonneg_right
    (qLevelOffResonantCorrectionStaticMass_le_acousticMoment_add_uniform
      m kappa energy observed energyBound ceiling hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency)
    hTime.le)

end

end ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound
