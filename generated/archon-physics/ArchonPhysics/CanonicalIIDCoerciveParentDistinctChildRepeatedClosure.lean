import ArchonPhysics.CanonicalIIDCoerciveRepeatedHistoryKineticBound
import ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
import ArchonPhysics.HamiltonianFirstLayerCollisionDecomposition
import ArchonPhysics.RepeatedModeTupleInteractionBound
import ArchonPhysics.ResonanceKernelLipschitz
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Parent-distinct child-repeated closure for the canonical iid FPUT chain

This file closes one precise part of the repeated-history residual without
assuming RPA or a Markov equation.

First, an actual quadratic Picard label is transported through the canonical
ordered-index equivalence.  The positive diagonal collision sum is then
split, as a literal finite-sum identity, into the four mode-equality sectors.
The child-repeated term is split once more into parent-distinct and all-equal
pieces.  These statements apply directly to the collision summand occurring
in the Hamiltonian first-layer Haar identity.

Second, the parent-distinct child-repeated broadened collision weight is
bounded by the complete child-equality plane.  The repeated-mode Parseval
estimate turns this into an explicit inverse-participation-ratio bound.  At
kinetic time, the coupling-weighted contribution is `O(rho)`, uniformly in
volume and coupling.  Consequently this sector vanishes along any sequence
for which the displayed edge-frame IPR ceiling `rho n` tends to zero.

The IPR hypothesis is intentionally visible.  It is not known here for the
canonical random-mass chain and is not replaced by an RPA assumption.  The
final theorem therefore reduces the former residual to an explicitly named
higher-order remainder under this transparent delocalization input.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveParentDistinctChildRepeatedClosure

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveRepeatedHistoryKineticBound
open ArchonPhysics.ChildRepeatedAllEqualBroadeningDecay
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.ThreeModeRawEqualityInclusionExclusion
open ArchonPhysics.UniformCollisionDensityTransfer
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter

noncomputable section

/-! ## Actual Picard labels and the collision partition -/

/-- The ordered three-mode label carried by one actual quadratic Picard term
with a fixed observed output mode. -/
def orderedModesOfQuadraticPicardLabel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) : OrderedModeTriple N :=
  fun r => orderedIndexEquiv.symm (quadraticCollisionModes observed term r)

/-- Transporting the ordered label back gives the literal modes in the
quadratic Hamiltonian Picard term. -/
theorem orderedIndexEquiv_orderedModesOfQuadraticPicardLabel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    (fun r => orderedIndexEquiv
      (orderedModesOfQuadraticPicardLabel observed term r)) =
        quadraticCollisionModes observed term := by
  funext r
  simp [orderedModesOfQuadraticPicardLabel]

/-- The canonical positive-frequency filter is exactly the physical filter
on an actual Picard label. -/
theorem isPositiveOrderedTriple_orderedModesOfQuadraticPicardLabel_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    IsPositiveOrderedTriple m
        (orderedModesOfQuadraticPicardLabel observed term) ↔
      PositiveModeTuple m (quadraticCollisionModes observed term) := by
  rw [isPositiveOrderedTriple_iff_physical]
  rw [orderedIndexEquiv_orderedModesOfQuadraticPicardLabel]

/-- Finite sum of actual positive quadratic Picard labels retained by one
ordered mode-sector predicate.  The value is arbitrary, so the comparison
below applies to the exact Hamiltonian collision summand rather than only to
a counting surrogate. -/
def positiveQuadraticPicardSectorSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (keep : OrderedModeTriple N -> Prop)
    (value : QuadraticPhaseTerm N -> Real) : Real := by
  classical
  exact ∑ term ∈ positiveQuadraticPhaseTerms m observed,
    if keep (orderedModesOfQuadraticPicardLabel observed term) then
      value term
    else 0

/-- Every actual positive quadratic Picard label belongs to exactly one of
the four ordered collision partitions.  This is a finite-sum identity; no
decorrelation, small-denominator estimate, or limiting argument enters. -/
theorem sum_positiveQuadraticPicardLabel_eq_four_collision_sectors
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (value : QuadraticPhaseTerm N -> Real) :
    (∑ term ∈ positiveQuadraticPhaseTerms m observed, value term) =
      positiveQuadraticPicardSectorSum m observed AllDistinctModes value +
      positiveQuadraticPicardSectorSum m observed ChildRepeated value +
      positiveQuadraticPicardSectorSum
        m observed ParentChildOneRepeated value +
      positiveQuadraticPicardSectorSum
        m observed ParentChildTwoRepeated value := by
  classical
  unfold positiveQuadraticPicardSectorSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro term _hterm
  let modes := orderedModesOfQuadraticPicardLabel observed term
  by_cases hchild : modes 1 = modes 2
  · simp [modes, ChildRepeated, ParentChildOneRepeated,
      ParentChildTwoRepeated, AllDistinctModes, hchild]
  · by_cases hone : modes 0 = modes 1
    · simp [modes, ChildRepeated, ParentChildOneRepeated,
        ParentChildTwoRepeated, AllDistinctModes, hchild, hone]
    · by_cases htwo : modes 0 = modes 2
      · have htwoOne : modes 2 ≠ modes 1 := Ne.symm hchild
        simp [modes, ChildRepeated, ParentChildOneRepeated,
          ParentChildTwoRepeated, AllDistinctModes, hchild, htwo,
          htwoOne]
      · simp [modes, ChildRepeated, ParentChildOneRepeated,
          ParentChildTwoRepeated, AllDistinctModes, hchild, hone, htwo]

/-- The child-repeated part of the actual Picard-label sum is exactly the
parent-distinct sector plus the all-three-equal sector. -/
theorem positiveQuadraticPicardSectorSum_childRepeated_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (value : QuadraticPhaseTerm N -> Real) :
    positiveQuadraticPicardSectorSum m observed ChildRepeated value =
      positiveQuadraticPicardSectorSum
          m observed ParentDistinctChildRepeated value +
        positiveQuadraticPicardSectorSum m observed AllThreeModesEqual value := by
  classical
  unfold positiveQuadraticPicardSectorSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro term _hterm
  let modes := orderedModesOfQuadraticPicardLabel observed term
  by_cases hchild : modes 1 = modes 2
  · by_cases hparent : modes 0 = modes 1
    · simp [modes, ChildRepeated, ParentDistinctChildRepeated,
        AllThreeModesEqual, hchild, hparent]
    · have hparentTwo : modes 0 ≠ modes 2 := by
        intro h
        exact hparent (h.trans hchild.symm)
      simp [modes, ChildRepeated, ParentDistinctChildRepeated,
        AllThreeModesEqual, hchild, hparentTwo]
  · simp [modes, ChildRepeated, ParentDistinctChildRepeated,
      AllThreeModesEqual, hchild]

/-- The exact physical first-layer collision summand attached to one
quadratic Picard label. -/
def physicalFirstLayerCollisionValue
    {N : Nat} [NeZero N] (kappa g : Real)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (energy : Lattice.Site N -> Real) (time : Real)
    (term : QuadraticPhaseTerm N) : Real :=
  (kappa * g) ^ 2 *
    normalizedInteractionWeight m (quadraticCollisionModes observed term) *
    (∏ r : Fin 2,
      modeAction energy (modeFrequency m) (term.1 r)) *
    finiteTimeResonanceWeight
      (quadraticPhaseMismatch (modeFrequency m) observed term) time

/-- Direct specialization of the finite Picard-label comparison to the
collision sum appearing in the Hamiltonian first-layer Haar identity. -/
theorem physicalFirstLayerCollisionSum_eq_four_collision_sectors
    {N : Nat} [NeZero N] (kappa g : Real)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (energy : Lattice.Site N -> Real) (time : Real) :
    (∑ term ∈ positiveQuadraticPhaseTerms m observed,
        physicalFirstLayerCollisionValue
          kappa g m observed energy time term) =
      positiveQuadraticPicardSectorSum m observed AllDistinctModes
          (physicalFirstLayerCollisionValue
            kappa g m observed energy time) +
      positiveQuadraticPicardSectorSum m observed ChildRepeated
          (physicalFirstLayerCollisionValue
            kappa g m observed energy time) +
      positiveQuadraticPicardSectorSum m observed ParentChildOneRepeated
          (physicalFirstLayerCollisionValue
            kappa g m observed energy time) +
      positiveQuadraticPicardSectorSum m observed ParentChildTwoRepeated
          (physicalFirstLayerCollisionValue
            kappa g m observed energy time) :=
  sum_positiveQuadraticPicardLabel_eq_four_collision_sectors
    m observed (physicalFirstLayerCollisionValue
      kappa g m observed energy time)

/-! ## Parent-distinct child-repeated broadening -/

/-- The broadened decay-channel weight with equal child labels and a
different parent label.  It is parametrized by the common child `k` and the
parent `q`, with no duplication. -/
def positiveParentDistinctChildRepeatedBroadenedInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (T : Real) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k then
      harmonicOrderedNormalizedInteractionWeight m ![q, k, k] *
        normalizedFiniteTimeResonanceKernel
          (orderedThreeWaveMismatch m decayInteractionSign ![q, k, k]) T
    else 0

theorem positiveParentDistinctChildRepeatedBroadenedInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) (T : Real) :
    0 <= positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T := by
  classical
  unfold positiveParentDistinctChildRepeatedBroadenedInteractionWeight
  apply Finset.sum_nonneg
  intro k _hk
  apply Finset.sum_nonneg
  intro q _hq
  split_ifs
  · exact mul_nonneg
      (harmonicOrderedNormalizedInteractionWeight_nonneg m _)
      (normalizedFiniteTimeResonanceKernel_nonneg _ T)
  · exact le_rfl

/-- Kernel height times the complete child-equality-plane static weight
dominates the parent-distinct broadened sector. -/
theorem positiveParentDistinctChildRepeatedBroadenedInteractionWeight_le_height
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {T : Real} (hT : 0 < T) :
    positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T <=
      positiveRepeatedOneTwoInteractionWeight m *
        (T / (2 * Real.pi)) := by
  classical
  unfold positiveParentDistinctChildRepeatedBroadenedInteractionWeight
    positiveRepeatedOneTwoInteractionWeight
  calc
    (∑ k, ∑ q,
      if IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k then
        harmonicOrderedNormalizedInteractionWeight m ![q, k, k] *
          normalizedFiniteTimeResonanceKernel
            (orderedThreeWaveMismatch m decayInteractionSign ![q, k, k]) T
      else 0) <=
        ∑ k, ∑ q,
          (if IsPositiveOrderedTriple m ![q, k, k] then
            harmonicOrderedNormalizedInteractionWeight m ![q, k, k]
          else 0) * (T / (2 * Real.pi)) := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro q _hq
      by_cases hpositive : IsPositiveOrderedTriple m ![q, k, k]
      · by_cases hdistinct : q ≠ k
        · rw [if_pos ⟨hpositive, hdistinct⟩, if_pos hpositive]
          exact mul_le_mul_of_nonneg_left
            (normalizedFiniteTimeResonanceKernel_le_height _ hT)
            (harmonicOrderedNormalizedInteractionWeight_nonneg m _)
        · rw [if_neg (fun h => hdistinct h.2), if_pos hpositive]
          exact mul_nonneg
            (harmonicOrderedNormalizedInteractionWeight_nonneg m _)
            (div_nonneg hT.le
              (mul_nonneg zero_le_two Real.pi_pos.le))
      · rw [if_neg (fun h => hpositive h.1), if_neg hpositive]
        simp
    _ = (∑ k, ∑ q,
          if IsPositiveOrderedTriple m ![q, k, k] then
            harmonicOrderedNormalizedInteractionWeight m ![q, k, k]
          else 0) * (T / (2 * Real.pi)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]

/-- Explicit finite-volume IPR estimate for the parent-distinct sector. -/
theorem positiveParentDistinctChildRepeatedBroadenedInteractionWeight_div_volume_le_of_ipr
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling rho : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    (hipr : forall k,
      inverseParticipationRatio (harmonicNormalizedEdgeFrame m) k <= rho)
    {T : Real} (hT : 0 < T) :
    positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T /
        (N : Real) <=
      (T / (2 * Real.pi)) * ((ceiling / 2) ^ 3 * rho) := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hplane : positiveRepeatedOneTwoInteractionWeight m / (N : Real) <=
      (ceiling / 2) ^ 3 * rho := by
    rw [(positiveRepeatedPairInteractionWeights_eq m).2]
    exact positiveRepeatedZeroOneInteractionWeight_div_volume_le_of_ipr
      m ceiling rho hceiling hfrequency hipr
  have hheight : 0 <= T / (2 * Real.pi) :=
    div_nonneg hT.le (mul_nonneg zero_le_two Real.pi_pos.le)
  calc
    positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T /
          (N : Real) <=
        (positiveRepeatedOneTwoInteractionWeight m *
          (T / (2 * Real.pi))) / (N : Real) :=
      div_le_div_of_nonneg_right
        (positiveParentDistinctChildRepeatedBroadenedInteractionWeight_le_height
          m hT) hN.le
    _ = (T / (2 * Real.pi)) *
        (positiveRepeatedOneTwoInteractionWeight m / (N : Real)) := by ring
    _ <= (T / (2 * Real.pi)) * ((ceiling / 2) ^ 3 * rho) :=
      mul_le_mul_of_nonneg_left hplane hheight

/-- At kinetic time the physical coupling square cancels the resonance-peak
height.  The remaining estimate is exactly proportional to the IPR ceiling. -/
theorem physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr
    {N : Nat} [NeZero N] (kappa g tau : Real)
    (m : Lattice.PositiveMassConfig N)
    (ceiling rho : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    (hipr : forall k,
      inverseParticipationRatio (harmonicNormalizedEdgeFrame m) k <= rho)
    (htau : 0 < tau) (hg : g ≠ 0) :
    (kappa * g) ^ 2 *
        (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
          m (tau / g ^ 2) / (N : Real)) <=
      kappa ^ 2 * (tau / (2 * Real.pi) * ((ceiling / 2) ^ 3 * rho)) := by
  have htime : 0 < tau / g ^ 2 := div_pos htau (sq_pos_of_ne_zero hg)
  have hbound :=
    positiveParentDistinctChildRepeatedBroadenedInteractionWeight_div_volume_le_of_ipr
      m ceiling rho hceiling hfrequency hipr htime
  have hgsq : 0 <= g ^ 2 := sq_nonneg g
  have hkappa : 0 <= kappa ^ 2 := sq_nonneg kappa
  calc
    (kappa * g) ^ 2 *
          (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real)) =
        kappa ^ 2 * (g ^ 2 *
          (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real))) := by ring
    _ <= kappa ^ 2 * (g ^ 2 *
        ((tau / g ^ 2) / (2 * Real.pi) *
          ((ceiling / 2) ^ 3 * rho))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound hgsq) hkappa
    _ = kappa ^ 2 *
        (tau / (2 * Real.pi) * ((ceiling / 2) ^ 3 * rho)) := by
      field_simp [hg]

/-! ## Canonical iid sequence and residual reduction -/

/-- Canonical per-site parent-distinct child-repeated broadened budget at
volume `N = n + 2`. -/
def canonicalParentDistinctChildRepeatedCollisionBudget
    (n : Nat) (omega : RandomEnsemble.SampleSpace) (T : Real) : Real :=
  let N := n + 2
  let m := canonicalIIDMassPhaseEnsemble.restrictPositiveMass
    (N := N) omega
  positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T /
    (N : Real)

theorem canonicalParentDistinctChildRepeatedCollisionBudget_nonneg
    (n : Nat) (omega : RandomEnsemble.SampleSpace) (T : Real) :
    0 <= canonicalParentDistinctChildRepeatedCollisionBudget n omega T := by
  dsimp [canonicalParentDistinctChildRepeatedCollisionBudget]
  exact div_nonneg
    (positiveParentDistinctChildRepeatedBroadenedInteractionWeight_nonneg _ _)
    (Nat.cast_nonneg _)

/-- Canonical kinetic-time IPR estimate with the support-derived universal
frequency ceiling `sqrt 5`. -/
theorem canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr
    (n : Nat) (omega : RandomEnsemble.SampleSpace)
    (kappa g tau rho : Real)
    (hipr : forall k,
      inverseParticipationRatio
        (harmonicNormalizedEdgeFrame
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := n + 2) omega)) k <= rho)
    (htau : 0 < tau) (hg : g ≠ 0) :
    (kappa * g) ^ 2 *
        canonicalParentDistinctChildRepeatedCollisionBudget
          n omega (tau / g ^ 2) <=
      kappa ^ 2 *
        (tau / (2 * Real.pi) * ((Real.sqrt 5 / 2) ^ 3 * rho)) := by
  apply physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr
    kappa g tau
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
      (N := n + 2) omega)
    (Real.sqrt 5) rho (Real.sqrt_nonneg 5)
    (fun k => iid_orderedModeFrequency_harmonic_le_sqrt_five
      canonicalIIDMassPhaseEnsemble omega k)
    hipr htau hg

/-- Under a displayed vanishing IPR ceiling, the parent-distinct sector is
automatically negligible at kinetic time. -/
theorem canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_tendsto_zero_of_ipr
    (size : Nat -> Nat) (omega : RandomEnsemble.SampleSpace)
    (kappa tau : Real) (htau : 0 < tau)
    (g rho : Nat -> Real) (hg0 : forall n, g n ≠ 0)
    (hrho : Tendsto rho atTop (nhds 0))
    (hipr : forall n k,
      inverseParticipationRatio
        (harmonicNormalizedEdgeFrame
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := size n + 2) omega)) k <= rho n) :
    Tendsto (fun n =>
      (kappa * g n) ^ 2 *
        canonicalParentDistinctChildRepeatedCollisionBudget
          (size n) omega (tau / (g n) ^ 2)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      mul_nonneg (sq_nonneg _) <|
        canonicalParentDistinctChildRepeatedCollisionBudget_nonneg
          (size n) omega _
  · exact Eventually.of_forall fun n =>
      canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr
        (size n) omega kappa (g n) tau (rho n) (hipr n) htau (hg0 n)
  · simpa using
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.mul
          (tendsto_const_nhds.mul hrho)))

/-- The old repeated-history residual is reduced to a genuinely higher-order
remainder once the explicit Picard-to-partition comparison and a vanishing
IPR ceiling are supplied.  No decay is stored inside a certificate field. -/
theorem repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_ipr_and_higherRemainder
    (size : Nat -> Nat) (omega : RandomEnsemble.SampleSpace)
    (kappa tau : Real) (htau : 0 < tau)
    (g rho : Nat -> Real) (hg0 : forall n, g n ≠ 0)
    (hg : Tendsto g atTop (nhds 0))
    (hrho : Tendsto rho atTop (nhds 0))
    (hipr : forall n k,
      inverseParticipationRatio
        (harmonicNormalizedEdgeFrame
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := size n + 2) omega)) k <= rho n)
    (budget higherRemainder : Nat -> Real)
    (controlledMultiplicity parentDistinctMultiplicity : Nat)
    (hbudget_nonneg : forall n, 0 <= budget n)
    (hhigher : Tendsto higherRemainder atTop (nhds 0))
    (hdominate : forall n,
      budget n <=
        (controlledMultiplicity : Real) *
            canonicalControlledRepeatedCollisionBudget
              (size n) omega (tau / (g n) ^ 2) +
          (parentDistinctMultiplicity : Real) *
            ((kappa * g n) ^ 2 *
              canonicalParentDistinctChildRepeatedCollisionBudget
                (size n) omega (tau / (g n) ^ 2)) +
          higherRemainder n) :
    Tendsto budget atTop (nhds 0) := by
  have hcontrolled :=
    canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero
      size omega tau htau g hg0 hg
  have hparent :=
    canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_tendsto_zero_of_ipr
      size omega kappa tau htau g rho hg0 hrho hipr
  apply squeeze_zero'
  · exact Eventually.of_forall hbudget_nonneg
  · exact Eventually.of_forall hdominate
  · have hcscaled : Tendsto (fun n =>
        (controlledMultiplicity : Real) *
          canonicalControlledRepeatedCollisionBudget
            (size n) omega (tau / (g n) ^ 2)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hcontrolled
    have hpscaled : Tendsto (fun n =>
        (parentDistinctMultiplicity : Real) *
          ((kappa * g n) ^ 2 *
            canonicalParentDistinctChildRepeatedCollisionBudget
              (size n) omega (tau / (g n) ^ 2))) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hparent
    simpa using (hcscaled.add hpscaled).add hhigher

end

end ArchonPhysics.CanonicalIIDCoerciveParentDistinctChildRepeatedClosure
