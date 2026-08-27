import ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
import ArchonPhysics.DecayChannelModeEqualityPartition

/-!
# Child-repeated frequency triples remain on the diagonal under weak limits

The decay-channel sector in which the two child labels agree is not a
three-dimensional coarea sector.  At every finite volume its joint frequency
measure is carried by the closed plane `frequency 1 = frequency 2`.  This
module proves that exact carrier statement before any limit and then uses the
closed-set half of Portmanteau to preserve it for finite-measure weak limits.

No assertion that the diagonal component vanishes is made here.  The result
therefore keeps visible the possible singular reaction channel
`frequency 0 = 2 * frequency 1` instead of incorrectly forcing it into a
two-dimensional absolutely continuous child-pair law.
-/

open scoped Topology

namespace ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit

open ArchonPhysics
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The closed plane on which the two child frequencies agree. -/
def childRepeatedFrequencyDiagonal : Set (Fin 3 -> Real) :=
  {frequency | frequency 1 = frequency 2}

theorem childRepeatedFrequencyDiagonal_isClosed :
    IsClosed childRepeatedFrequencyDiagonal := by
  exact isClosed_eq (continuous_apply 1) (continuous_apply 2)

theorem childRepeatedFrequencyDiagonal_measurableSet :
    MeasurableSet childRepeatedFrequencyDiagonal :=
  childRepeatedFrequencyDiagonal_isClosed.measurableSet

/-- Equality of the child mode labels forces equality of their frequencies.
The converse is deliberately not claimed, since a degenerate spectrum can
have distinct labels with the same frequency. -/
theorem orderedFrequencyTriple_mem_childRepeatedFrequencyDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hchild : ChildRepeated modes) :
    orderedFrequencyTriple m modes ∈ childRepeatedFrequencyDiagonal := by
  change modes 1 = modes 2 at hchild
  change orderedModeFrequency (harmonicHermitian m) (modes 1) =
    orderedModeFrequency (harmonicHermitian m) (modes 2)
  rw [hchild]

/-- Every finite-volume child-repeated component is carried by the child
frequency diagonal. -/
theorem positiveWeightedFrequencyTripleMeasureWhere_childRepeated_compl_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedFrequencyTripleMeasureWhere m ChildRepeated
        (childRepeatedFrequencyDiagonalᶜ) = 0 := by
  classical
  unfold positiveWeightedFrequencyTripleMeasureWhere
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ ChildRepeated modes
  · rw [if_pos hkeep, Measure.smul_apply]
    simp [orderedFrequencyTriple_mem_childRepeatedFrequencyDiagonal
      m modes hkeep.2]
  · rw [if_neg hkeep]
    rfl

/-- Predicate-restricted finite sums of weighted Dirac masses are finite. -/
theorem positiveWeightedFrequencyTripleMeasureWhere_isFinite
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    IsFiniteMeasure (positiveWeightedFrequencyTripleMeasureWhere m keep) := by
  constructor
  unfold positiveWeightedFrequencyTripleMeasureWhere
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro modes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ keep modes
  · simp [hkeep]
  · simp [hkeep]

/-- Bundle a predicate-restricted per-site joint measure as a finite measure. -/
def perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) : FiniteMeasure (Fin 3 -> Real) :=
  ⟨perSitePositiveWeightedFrequencyTripleMeasureWhere m keep, by
    unfold perSitePositiveWeightedFrequencyTripleMeasureWhere
    let _ : IsFiniteMeasure
        (positiveWeightedFrequencyTripleMeasureWhere m keep) :=
      positiveWeightedFrequencyTripleMeasureWhere_isFinite m keep
    exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr (by
      exact_mod_cast NeZero.ne N))⟩

/-- Site normalization preserves the exact child-diagonal carrier. -/
theorem perSiteChildRepeatedFiniteMeasure_compl_diagonal_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    (perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
        m ChildRepeated : Measure (Fin 3 -> Real))
      (childRepeatedFrequencyDiagonalᶜ) = 0 := by
  change perSitePositiveWeightedFrequencyTripleMeasureWhere m ChildRepeated
      (childRepeatedFrequencyDiagonalᶜ) = 0
  unfold perSitePositiveWeightedFrequencyTripleMeasureWhere
  rw [Measure.smul_apply,
    positiveWeightedFrequencyTripleMeasureWhere_childRepeated_compl_eq_zero]
  simp

/-- Every finite-measure weak limit of canonical-volume child-repeated
components remains carried by the same closed child-frequency diagonal. -/
theorem childRepeatedPerSiteWeakLimit_compl_diagonal_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure (Fin 3 -> Real))
    (hweak : Tendsto
      (fun n : Nat =>
        perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
          (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated)
      atTop (nhds target)) :
    (target : Measure (Fin 3 -> Real))
      (childRepeatedFrequencyDiagonalᶜ) = 0 := by
  apply finiteMeasureWeakLimit_compl_closed_eq_zero
    (fun n : Nat =>
      perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated)
    target hweak childRepeatedFrequencyDiagonal
    childRepeatedFrequencyDiagonal_isClosed
  intro n
  exact perSiteChildRepeatedFiniteMeasure_compl_diagonal_eq_zero
    (ensemble.restrictPositiveMass (N := n + 2) omega)

end

end ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
