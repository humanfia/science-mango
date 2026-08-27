import ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
import ArchonPhysics.ChildRepeatedDiagonalHybridKernel
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Canonical weak-limit bridge for the child-repeated sector

The child-repeated part of the cubic decay sum is a genuine singular sector.
This file retains the normalized spectral ranks, proves the exact finite-volume
forgetful bridge to the existing child-repeated frequency measure, and gives
both interfaces which are actually justified by the current grounding:

* every supplied finite-measure weak limit remains on the repeated-child
  marked diagonal, and its frequency and mismatch pushforwards retain the
  exact lower-dimensional hybrid representation;
* for the frozen canonical iid ensemble, the child-repeated sequence has an
  almost-sure weakly convergent cofinal subsequence.  Along the same
  subsequence the complete marked measure converges to its already identified
  canonical limit.

No convergence of the child-repeated component along the complete sequence,
and no vanishing of its possible resonance `omega_parent = 2 omega_child`, is
asserted.
-/

open scoped Topology

namespace ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Predicate-restricted marked finite-volume measures -/

/-- Marked collision measure restricted to an arbitrary ordered-mode
predicate. -/
def positiveWeightedRankFrequencyTripleMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    Measure (Fin 3 -> RankFrequencyMark) := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes ∧ keep modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedRankFrequencyTriple m modes)
    else 0

theorem positiveWeightedRankFrequencyTripleMeasureWhere_isFinite
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    IsFiniteMeasure (positiveWeightedRankFrequencyTripleMeasureWhere m keep) := by
  constructor
  unfold positiveWeightedRankFrequencyTripleMeasureWhere
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro modes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ keep modes
  · simp [hkeep]
  · simp [hkeep]

/-- Bundled predicate-restricted marked collision measure. -/
def positiveWeightedRankFrequencyTripleFiniteMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  ⟨positiveWeightedRankFrequencyTripleMeasureWhere m keep,
    positiveWeightedRankFrequencyTripleMeasureWhere_isFinite m keep⟩

/-- Bundled predicate-restricted joint-frequency collision measure before
site normalization. -/
def positiveWeightedFrequencyTripleFiniteMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    FiniteMeasure (Fin 3 -> Real) :=
  ⟨positiveWeightedFrequencyTripleMeasureWhere m keep,
    positiveWeightedFrequencyTripleMeasureWhere_isFinite m keep⟩

/-- Forgetting ranks recovers exactly the predicate-restricted frequency
measure, with no simple-spectrum hypothesis. -/
theorem map_positiveWeightedRankFrequencyTripleMeasureWhere_forgetRank
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    (positiveWeightedRankFrequencyTripleMeasureWhere m keep).map
        forgetRankFrequencyTriple =
      positiveWeightedFrequencyTripleMeasureWhere m keep := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasureWhere
    positiveWeightedFrequencyTripleMeasureWhere
  rw [Measure.map_finset_sum'
    measurable_forgetRankFrequencyTriple.aemeasurable]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ keep modes
  · simp only [if_pos hkeep]
    rw [Measure.map_smul,
      Measure.map_dirac' measurable_forgetRankFrequencyTriple]
    rw [forgetRankFrequencyTriple_orderedRankFrequencyTriple]
  · simp [hkeep]

theorem map_positiveWeightedRankFrequencyTripleFiniteMeasureWhere_forgetRank
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    (positiveWeightedRankFrequencyTripleFiniteMeasureWhere m keep).map
        forgetRankFrequencyTriple =
      positiveWeightedFrequencyTripleFiniteMeasureWhere m keep := by
  apply FiniteMeasure.toMeasure_injective
  exact map_positiveWeightedRankFrequencyTripleMeasureWhere_forgetRank m keep

/-- The canonical child-repeated marked component. -/
def canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  (((n + 2 : Nat) : NNReal)⁻¹) •
    positiveWeightedRankFrequencyTripleFiniteMeasureWhere
      (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated

/-- The corresponding canonical child-repeated frequency component. -/
def canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    FiniteMeasure (Fin 3 -> Real) :=
  perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
    (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated

/-- Exact canonical forgetful bridge for the child-repeated sector. -/
theorem map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble n omega).map forgetRankFrequencyTriple =
      canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
        ensemble n omega := by
  apply FiniteMeasure.toMeasure_injective
  change Measure.map forgetRankFrequencyTriple
      ((((n + 2 : Nat) : NNReal)⁻¹ •
        positiveWeightedRankFrequencyTripleFiniteMeasureWhere
          (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated :
        FiniteMeasure (Fin 3 -> RankFrequencyMark)) : Measure _) =
    perSitePositiveWeightedFrequencyTripleMeasureWhere
      (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated
  rw [FiniteMeasure.toMeasure_smul, Measure.map_smul]
  rw [show
    Measure.map forgetRankFrequencyTriple
      (positiveWeightedRankFrequencyTripleFiniteMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega)
        ChildRepeated : Measure (Fin 3 -> RankFrequencyMark)) =
      positiveWeightedFrequencyTripleMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega)
        ChildRepeated by
      exact map_positiveWeightedRankFrequencyTripleMeasureWhere_forgetRank
        _ ChildRepeated]
  unfold perSitePositiveWeightedFrequencyTripleMeasureWhere
  change (((((n + 2 : Nat) : NNReal)⁻¹ : NNReal) : ENNReal) •
      positiveWeightedFrequencyTripleMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated) =
    (((n + 2 : Nat) : ENNReal)⁻¹ •
      positiveWeightedFrequencyTripleMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated)
  rw [ENNReal.coe_inv (by positivity : ((n + 2 : Nat) : NNReal) ≠ 0)]
  rfl

/-! ## Exact marked and hybrid carriers -/

/-- Equality of both rank-frequency child marks. -/
def childRepeatedRankFrequencyDiagonal :
    Set (Fin 3 -> RankFrequencyMark) :=
  {marks | marks 1 = marks 2}

theorem childRepeatedRankFrequencyDiagonal_isClosed :
    IsClosed childRepeatedRankFrequencyDiagonal := by
  exact isClosed_eq (continuous_apply 1) (continuous_apply 2)

theorem orderedRankFrequencyTriple_mem_childRepeatedRankFrequencyDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hchild : ChildRepeated modes) :
    orderedRankFrequencyTriple m modes ∈
      childRepeatedRankFrequencyDiagonal := by
  change orderedRankFrequencyMark m (modes 1) =
    orderedRankFrequencyMark m (modes 2)
  rw [hchild]

/-- The raw marked child-repeated measure is exactly carried by its marked
diagonal. -/
theorem positiveWeightedRankFrequencyTripleMeasureWhere_childRepeated_compl_diagonal_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedRankFrequencyTripleMeasureWhere m ChildRepeated
      (childRepeatedRankFrequencyDiagonalᶜ) = 0 := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasureWhere
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ ChildRepeated modes
  · rw [if_pos hkeep, Measure.smul_apply]
    simp [orderedRankFrequencyTriple_mem_childRepeatedRankFrequencyDiagonal
      m modes hkeep.2]
  · rw [if_neg hkeep]
    rfl

/-- Site normalization preserves the exact marked diagonal carrier. -/
theorem canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_compl_diagonal_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure ensemble n omega :
      Measure (Fin 3 -> RankFrequencyMark))
      (childRepeatedRankFrequencyDiagonalᶜ) = 0 := by
  unfold canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change _ * positiveWeightedRankFrequencyTripleMeasureWhere
      (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated
      (childRepeatedRankFrequencyDiagonalᶜ) = 0
  rw [positiveWeightedRankFrequencyTripleMeasureWhere_childRepeated_compl_diagonal_eq_zero]
  simp

/-- Parent/child frequencies together with the scalar decay mismatch. -/
def childRepeatedHybridCoordinates (frequency : Fin 3 -> Real) :
    (Real × Real) × Real :=
  (childRepeatedFrequencyProjection frequency,
    frequencyTripleMismatch decayInteractionSign frequency)

theorem continuous_childRepeatedHybridCoordinates :
    Continuous childRepeatedHybridCoordinates := by
  unfold childRepeatedHybridCoordinates
  exact continuous_childRepeatedFrequencyProjection.prodMk (by
    unfold frequencyTripleMismatch
    fun_prop)

theorem measurable_childRepeatedHybridCoordinates :
    Measurable childRepeatedHybridCoordinates :=
  continuous_childRepeatedHybridCoordinates.measurable

/-- Graph of the lower-dimensional reaction mismatch
`omega_parent - 2 * omega_child`. -/
def childRepeatedHybridGraph : Set ((Real × Real) × Real) :=
  {data | data.2 = childRepeatedDecayMismatch data.1}

theorem childRepeatedHybridGraph_isClosed :
    IsClosed childRepeatedHybridGraph := by
  exact isClosed_eq continuous_snd
    (continuous_childRepeatedDecayMismatch.comp continuous_fst)

theorem childRepeatedHybridCoordinates_mem_graph_of_mem_diagonal
    {frequency : Fin 3 -> Real}
    (hfrequency : frequency ∈ childRepeatedFrequencyDiagonal) :
    childRepeatedHybridCoordinates frequency ∈ childRepeatedHybridGraph := by
  change frequencyTripleMismatch decayInteractionSign frequency =
    childRepeatedDecayMismatch
      (childRepeatedFrequencyProjection frequency)
  rw [← frequencyTripleMismatch_decay_diagonalLift]
  congr 1
  exact (childRepeatedFrequencyDiagonalLift_projection_eq_of_mem hfrequency).symm

/-- Any diagonal-supported frequency measure pushes forward to the exact
hybrid reaction graph. -/
theorem map_childRepeatedHybridCoordinates_compl_graph_eq_zero
    (measure : Measure (Fin 3 -> Real))
    (hsupport : measure (childRepeatedFrequencyDiagonalᶜ) = 0) :
    Measure.map childRepeatedHybridCoordinates measure
      (childRepeatedHybridGraphᶜ) = 0 := by
  rw [Measure.map_apply measurable_childRepeatedHybridCoordinates
    childRepeatedHybridGraph_isClosed.measurableSet.compl]
  apply measure_mono_null _ hsupport
  intro frequency hfrequency
  simp only [mem_preimage, mem_compl_iff] at hfrequency ⊢
  intro hdiagonal
  exact hfrequency
    (childRepeatedHybridCoordinates_mem_graph_of_mem_diagonal hdiagonal)

end

end ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
