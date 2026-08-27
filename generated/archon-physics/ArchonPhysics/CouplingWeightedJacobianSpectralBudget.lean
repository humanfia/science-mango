import ArchonPhysics.CanonicalCollisionSoftLegBound

/-!
# N-uniform coupling-weighted Jacobian budgets

The actual three-mass coarea coefficient contains the physical cubic
interaction weight multiplied by a reciprocal-Jacobian modifier.  Summing a
worst-case bound over all ordered mode triples creates a spurious `N^2`
loss.  Here the existing exact spectral factorization is used instead.

If the joint modifier has a separable one-leg majorant, the complete
coupling-weighted sum divided by `N` is bounded by three one-leg effective
weight ceilings.  Thus the only nonseparable hard-sector obligation is an
upper envelope for the reciprocal lifted Jacobian itself.
-/

namespace ArchonPhysics.CouplingWeightedJacobianSpectralBudget

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.OrderedInteractionSpectralFactorization.Harmonic
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeLegKernelApproximationAlgebra

noncomputable section

set_option maxHeartbeats 2000000

/-- A nonnegative joint modifier attached to the genuine positive cubic
collision weight.  The intended modifier is a good-patch reciprocal
Jacobian, possibly with hard-frequency or rectangle filters. -/
def positiveCouplingWeightedTupleSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modifier : OrderedModeTriple N → Real) : Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      harmonicOrderedNormalizedInteractionWeight m modes * modifier modes
    else 0

/-- Insert the positive-frequency filter into each one-leg envelope. -/
def positiveSeparableLegWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (envelope : Fin 3 → OrderedModeIndex N → Real)
    (r : Fin 3) (k : OrderedModeIndex N) : Real :=
  orderedPositiveFrequencyIndicator m k * envelope r k

/-- On a positive tuple, the product of filtered envelopes is the ordinary
product of the three envelopes. -/
theorem prod_positiveSeparableLegWeight_of_positive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (envelope : Fin 3 → OrderedModeIndex N → Real)
    (modes : OrderedModeTriple N)
    (hpositive : IsPositiveOrderedTriple m modes) :
    (∏ r, positiveSeparableLegWeight m envelope r (modes r)) =
      ∏ r, envelope r (modes r) := by
  classical
  apply Finset.prod_congr rfl
  intro r _hr
  have hfrequency : 0 < orderedModeFrequency
      (harmonicHermitian m) (modes r) :=
    (mem_orderedPositiveModeIndices_iff m (modes r)).1 (hpositive r)
  simp [positiveSeparableLegWeight,
    orderedPositiveFrequencyIndicator, hfrequency]

/-- Outside the positive sector, at least one filtered one-leg envelope
vanishes. -/
theorem prod_positiveSeparableLegWeight_of_not_positive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (envelope : Fin 3 → OrderedModeIndex N → Real)
    (modes : OrderedModeTriple N)
    (hpositive : ¬ IsPositiveOrderedTriple m modes) :
    (∏ r, positiveSeparableLegWeight m envelope r (modes r)) = 0 := by
  classical
  simp only [IsPositiveOrderedTriple, not_forall] at hpositive
  obtain ⟨r, hr⟩ := hpositive
  have hfrequency : ¬ 0 < orderedModeFrequency
      (harmonicHermitian m) (modes r) := by
    intro hfrequency
    exact hr ((mem_orderedPositiveModeIndices_iff m (modes r)).2 hfrequency)
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  simp [positiveSeparableLegWeight,
    orderedPositiveFrequencyIndicator, hfrequency]

/-- A joint modifier dominated on positive tuples by a product of one-leg
envelopes is dominated after summing by the exactly factorized weighted
interaction moment. -/
theorem positiveCouplingWeightedTupleSum_le_separable
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modifier : OrderedModeTriple N → Real)
    (envelope : Fin 3 → OrderedModeIndex N → Real)
    (hmodifier : ∀ modes, IsPositiveOrderedTriple m modes →
      modifier modes ≤ ∏ r, envelope r (modes r)) :
    positiveCouplingWeightedTupleSum m modifier ≤
      ∑ modes : OrderedModeTriple N,
        harmonicOrderedNormalizedInteractionWeight m modes *
          ∏ r, positiveSeparableLegWeight m envelope r (modes r) := by
  classical
  unfold positiveCouplingWeightedTupleSum
  apply Finset.sum_le_sum
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive,
      prod_positiveSeparableLegWeight_of_positive m envelope modes hpositive]
    exact mul_le_mul_of_nonneg_left (hmodifier modes hpositive)
      (harmonicOrderedNormalizedInteractionWeight_nonneg m modes)
  · rw [if_neg hpositive,
      prod_positiveSeparableLegWeight_of_not_positive m envelope modes hpositive]
    simp

/-- Abstract N-uniform spectral budget.  Once the three effective one-leg
weights are bounded, the exact cubic projector factorization eliminates the
ordered-mode cardinality completely. -/
theorem positiveCouplingWeightedTupleSum_div_volume_le_of_separable
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modifier : OrderedModeTriple N → Real)
    (envelope : Fin 3 → OrderedModeIndex N → Real)
    (hmodifier : ∀ modes, IsPositiveOrderedTriple m modes →
      modifier modes ≤ ∏ r, envelope r (modes r))
    (bound : Fin 3 → Real) (hbound : ∀ r, 0 ≤ bound r)
    (heffective : ∀ r k,
      |activeNormalizedIndicatorEffectiveWeight m
        (positiveSeparableLegWeight m envelope r) k| ≤ bound r) :
    positiveCouplingWeightedTupleSum m modifier / (N : Real) ≤
      bound 0 * bound 1 * bound 2 := by
  classical
  let legWeight : Fin 3 → OrderedModeIndex N → Real :=
    positiveSeparableLegWeight m envelope
  let effectiveWeight : Fin 3 → OrderedModeIndex N → Real := fun r =>
    activeNormalizedIndicatorEffectiveWeight m (legWeight r)
  let separableSum : Real :=
    ∑ modes : OrderedModeTriple N,
      harmonicOrderedNormalizedInteractionWeight m modes *
        ∏ r, legWeight r (modes r)
  have hsum : positiveCouplingWeightedTupleSum m modifier ≤ separableSum :=
    positiveCouplingWeightedTupleSum_le_separable
      m modifier envelope hmodifier
  have hfactor : separableSum =
      ∑ j, ∑ l, ∏ r : Fin 3,
        spectralKernel (harmonicNormalizedEdgeFrame m)
          (effectiveWeight r) j l := by
    calc
      separableSum =
          ∑ j, ∑ l, ∏ r,
            weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
              (harmonicHermitian m)
              (harmonicNormalizedLegWeight m legWeight r) j l :=
        harmonicWeightedNormalizedInteractionMoment_factorization m legWeight
      _ = ∑ j, ∑ l, ∏ r : Fin 3,
          spectralKernel (harmonicNormalizedEdgeFrame m)
            (effectiveWeight r) j l := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro l _hl
        apply Finset.prod_congr rfl
        intro r _hr
        rw [weightedProjectedBondKernel_harmonicNormalizedLegWeight_eq_spectralKernel]
  have hparseval := abs_cubicSpectralKernel_div_card_le
    (u := harmonicNormalizedEdgeFrame m)
    (by simp [Lattice.Site])
    (harmonicNormalizedEdgeFrame_orthonormal_unconditional m)
    effectiveWeight bound hbound (by
      intro r k
      exact heffective r k)
  rw [← hfactor] at hparseval
  have hparsevalN :
      |separableSum / (N : Real)| ≤ bound 0 * bound 1 * bound 2 := by
    simpa [Lattice.Site] using hparseval
  have hNpos : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  calc
    positiveCouplingWeightedTupleSum m modifier / (N : Real) ≤
        separableSum / (N : Real) :=
      div_le_div_of_nonneg_right hsum hNpos.le
    _ ≤ |separableSum / (N : Real)| := le_abs_self _
    _ ≤ bound 0 * bound 1 * bound 2 := hparsevalN

/-- The active normalized positive leg remains bounded after multiplication
by any bounded one-leg envelope. -/
theorem abs_activeNormalized_positiveEnvelope_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (envelope : OrderedModeIndex N → Real)
    (envelopeCeiling : Real) (henvelopeCeiling : 0 ≤ envelopeCeiling)
    (henvelope : ∀ k, |envelope k| ≤ envelopeCeiling)
    (frequencyCeiling : Real) (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling)
    (k : OrderedModeIndex N) :
    |activeNormalizedIndicatorEffectiveWeight m
      (fun q => orderedPositiveFrequencyIndicator m q * envelope q) k| ≤
        (frequencyCeiling / 2) * envelopeCeiling := by
  classical
  by_cases hpositive : 0 < orderedModeFrequency (harmonicHermitian m) k
  · have hbase := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m k
    have hbaseCeiling :
        |activeOrderedEigenvalue m k *
            (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹| ≤
          frequencyCeiling / 2 :=
      hbase.trans
        (div_le_div_of_nonneg_right (hfrequency k) (by norm_num))
    rw [activeNormalizedIndicatorEffectiveWeight,
      orderedPositiveFrequencyIndicator, if_pos hpositive, one_mul]
    calc
      |activeOrderedEigenvalue m k * envelope k *
          (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹| =
          |activeOrderedEigenvalue m k *
            (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹| *
              |envelope k| := by
        simp only [abs_mul]
        ring
      _ ≤ (frequencyCeiling / 2) * envelopeCeiling :=
        mul_le_mul hbaseCeiling (henvelope k) (abs_nonneg _)
          (div_nonneg hfrequencyCeiling (by norm_num))
  · rw [activeNormalizedIndicatorEffectiveWeight,
      orderedPositiveFrequencyIndicator, if_neg hpositive]
    have hrhs : 0 ≤ (frequencyCeiling / 2) * envelopeCeiling :=
      mul_nonneg (div_nonneg hfrequencyCeiling (by norm_num))
        henvelopeCeiling
    simpa using hrhs

/-- Concrete separable-envelope criterion using only the harmonic frequency
ceiling and uniform bounds on the three envelope profiles. -/
theorem positiveCouplingWeightedTupleSum_div_volume_le_of_envelope_ceiling
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modifier : OrderedModeTriple N → Real)
    (envelope : Fin 3 → OrderedModeIndex N → Real)
    (hmodifier : ∀ modes, IsPositiveOrderedTriple m modes →
      modifier modes ≤ ∏ r, envelope r (modes r))
    (envelopeCeiling : Fin 3 → Real)
    (henvelopeCeiling : ∀ r, 0 ≤ envelopeCeiling r)
    (henvelope : ∀ r k, |envelope r k| ≤ envelopeCeiling r)
    (frequencyCeiling : Real) (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling) :
    positiveCouplingWeightedTupleSum m modifier / (N : Real) ≤
      ((frequencyCeiling / 2) * envelopeCeiling 0) *
        ((frequencyCeiling / 2) * envelopeCeiling 1) *
          ((frequencyCeiling / 2) * envelopeCeiling 2) := by
  apply positiveCouplingWeightedTupleSum_div_volume_le_of_separable
    m modifier envelope hmodifier
    (fun r => (frequencyCeiling / 2) * envelopeCeiling r)
  · intro r
    exact mul_nonneg (div_nonneg hfrequencyCeiling (by norm_num))
      (henvelopeCeiling r)
  · intro r k
    exact abs_activeNormalized_positiveEnvelope_le
      m (envelope r) (envelopeCeiling r) (henvelopeCeiling r)
      (henvelope r) frequencyCeiling hfrequencyCeiling hfrequency k

end

end ArchonPhysics.CouplingWeightedJacobianSpectralBudget
