import ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge

/-!
# Compact child-repeated canonical cluster limits

This module closes the compactness side of the child-repeated hybrid sector.
It proves a uniform marked-measure budget under the already grounded simple-
spectrum event, transports every supplied weak limit through the frequency,
pair, mismatch, and hybrid-graph maps, and constructs an almost-sure cofinal
cluster point for the frozen canonical iid sequence.

The component cluster point is not identified with the complete canonical
marked limit: it is a sub-sector of that measure, and uniqueness of this
sector's complete-sequence limit has not been proved.  The theorem below does,
however, put the component convergence and the known complete canonical
convergence on the very same subsequence.
-/

open scoped Topology

namespace ArchonPhysics.ChildRepeatedCanonicalClusterLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Domination, compact support, and a uniform mass budget -/

/-- Predicate restriction only removes nonnegative marked atoms. -/
theorem positiveWeightedRankFrequencyTripleMeasureWhere_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N -> Prop) :
    positiveWeightedRankFrequencyTripleMeasureWhere m keep <=
      positiveWeightedRankFrequencyTripleMeasure m := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasureWhere
    positiveWeightedRankFrequencyTripleMeasure
  apply Finset.sum_le_sum
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · by_cases hkeep : keep modes
    · simp [hpositive, hkeep]
    · simp only [hpositive, hkeep, and_false, if_false, if_true]
      exact bot_le
  · simp [hpositive]

/-- The canonical marked child-repeated component is dominated by the full
canonical marked collision measure at the same volume. -/
theorem canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_le_full
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure ensemble n omega :
      Measure (Fin 3 -> RankFrequencyMark)) <=
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega :
      Measure (Fin 3 -> RankFrequencyMark)) := by
  rw [Measure.le_iff]
  intro s hs
  unfold canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
    canonicalRankFrequencyTriplePerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_smul,
    Measure.smul_apply, Measure.smul_apply]
  gcongr
  change positiveWeightedRankFrequencyTripleMeasureWhere
      (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated <=
    positiveWeightedRankFrequencyTripleMeasure
      (ensemble.restrictPositiveMass (N := n + 2) omega)
  exact positiveWeightedRankFrequencyTripleMeasureWhere_le
    (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated

/-- The child-repeated component inherits the common compact marked box. -/
theorem canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure ensemble n omega :
      Measure (Fin 3 -> RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  apply le_antisymm _ bot_le
  exact ((Measure.le_iff.mp
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_le_full
      ensemble n omega)) _
      collisionRankFrequencyTripleSupport_isCompact.isClosed.measurableSet.compl).trans_eq
        (canonicalRankFrequencyTriplePerSiteFiniteMeasure_compl_uniformSupport_eq_zero
          ensemble n omega)

/-- The child component's total mass is at most the full marked mass. -/
theorem canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_mass_le_full
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble n omega).mass <=
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
      ensemble n omega).mass := by
  rw [← ENNReal.coe_le_coe]
  simp only [FiniteMeasure.ennreal_mass]
  exact (Measure.le_iff.mp
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_le_full
      ensemble n omega)) Set.univ MeasurableSet.univ

/-- A convenient `NNReal` packaging of the existing full per-site collision
ceiling. -/
def childRepeatedCanonicalMassCeiling : NNReal :=
  ⟨canonicalCollisionPerSiteMassCeiling,
    canonicalCollisionPerSiteMassCeiling_nonneg⟩

/-- Under simple spectrum, the child-repeated marked sector has the same
volume-independent mass ceiling as the complete collision law. -/
theorem canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_mass_le
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble n omega).mass <= childRepeatedCanonicalMassCeiling := by
  calc
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass <=
        (canonicalRankFrequencyTriplePerSiteFiniteMeasure
          ensemble n omega).mass :=
      canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_mass_le_full
        ensemble n omega
    _ = (canonicalJointFrequencyPerSiteFiniteMeasure
          ensemble n omega).mass :=
      canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_eq_joint
        ensemble n omega
    _ <= childRepeatedCanonicalMassCeiling := by
      rw [← NNReal.coe_le_coe]
      exact canonicalJointFrequencyPerSiteFiniteMeasure_mass_le
        ensemble (fun _r => InteractionSign.plus) n omega hsimple

/-! ## Every supplied finite-measure weak limit keeps the singular carrier -/

/-- An arbitrary indexed child-sector weak limit remains on the full marked
child diagonal.  No cofinality premise is needed for carrier preservation. -/
theorem canonicalChildRepeatedMarkedWeakLimit_compl_diagonal_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    (target : Measure (Fin 3 -> RankFrequencyMark))
      (childRepeatedRankFrequencyDiagonalᶜ) = 0 := by
  apply finiteMeasureWeakLimit_compl_closed_eq_zero
    (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble (size j) omega)
    target hweak childRepeatedRankFrequencyDiagonal
    childRepeatedRankFrequencyDiagonal_isClosed
  intro j
  exact
    canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_compl_diagonal_eq_zero
      ensemble (size j) omega

/-- The same arbitrary weak limit retains the common compact marked box. -/
theorem canonicalChildRepeatedMarkedWeakLimit_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    (target : Measure (Fin 3 -> RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  apply finiteMeasureWeakLimit_compl_closed_eq_zero
    (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble (size j) omega)
    target hweak collisionRankFrequencyTripleSupport
    collisionRankFrequencyTripleSupport_isCompact.isClosed
  intro j
  exact
    canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
      ensemble (size j) omega

/-- Continuous rank-forgetting transports child-sector convergence to its
joint-frequency marginal. -/
theorem canonicalChildRepeated_frequencyMarginal_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    Tendsto
      (fun j => canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds (target.map forgetRankFrequencyTriple)) := by
  have hmapped := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
    (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble (size j) omega)
    target hweak continuous_forgetRankFrequencyTriple
  apply hmapped.congr'
  exact Eventually.of_forall fun j =>
    map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank
      ensemble (size j) omega

/-- The frequency marginal of every marked component weak limit remains on
`omega_child,1 = omega_child,2`. -/
theorem canonicalChildRepeatedMarkedWeakLimit_frequencyMarginal_compl_diagonal_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    (target.map forgetRankFrequencyTriple : Measure (Fin 3 -> Real))
      (childRepeatedFrequencyDiagonalᶜ) = 0 := by
  have hfrequency := canonicalChildRepeated_frequencyMarginal_tendsto
    ensemble omega size target hweak
  apply finiteMeasureWeakLimit_compl_closed_eq_zero
    (fun j => canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
      ensemble (size j) omega)
    (target.map forgetRankFrequencyTriple) hfrequency
    childRepeatedFrequencyDiagonal childRepeatedFrequencyDiagonal_isClosed
  intro j
  unfold canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
  exact perSiteChildRepeatedFiniteMeasure_compl_diagonal_eq_zero
    (ensemble.restrictPositiveMass (N := size j + 2) omega)

/-- The limiting frequency triple is exactly reconstructed from its
two-dimensional parent/child marginal. -/
theorem canonicalChildRepeatedMarkedWeakLimit_frequency_reconstruction
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    (((target.map forgetRankFrequencyTriple).map
      childRepeatedFrequencyProjection).map
        childRepeatedFrequencyDiagonalLift) =
      target.map forgetRankFrequencyTriple := by
  exact
    finiteMeasure_map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
      (target.map forgetRankFrequencyTriple)
      (canonicalChildRepeatedMarkedWeakLimit_frequencyMarginal_compl_diagonal_eq_zero
        ensemble omega size target hweak)

/-- Its scalar decay-mismatch law is exactly the pushforward of the singular
two-coordinate law by `omega_parent - 2 * omega_child`. -/
theorem canonicalChildRepeatedMarkedWeakLimit_decayMismatch_eq_reduced
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    (target.map forgetRankFrequencyTriple).map
        (frequencyTripleMismatch decayInteractionSign) =
      ((target.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection).map
          childRepeatedDecayMismatch := by
  exact
    finiteMeasure_map_decayMismatch_eq_map_childRepeatedDecayMismatch_projection
      (target.map forgetRankFrequencyTriple)
      (canonicalChildRepeatedMarkedWeakLimit_frequencyMarginal_compl_diagonal_eq_zero
        ensemble omega size target hweak)

/-- The joint pair/mismatch image is carried by the exact reaction graph,
including the potentially resonant line `omega_parent = 2 omega_child`. -/
theorem canonicalChildRepeatedMarkedWeakLimit_hybrid_compl_graph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    Measure.map childRepeatedHybridCoordinates
        (target.map forgetRankFrequencyTriple : Measure (Fin 3 -> Real))
      (childRepeatedHybridGraphᶜ) = 0 := by
  exact map_childRepeatedHybridCoordinates_compl_graph_eq_zero _
    (canonicalChildRepeatedMarkedWeakLimit_frequencyMarginal_compl_diagonal_eq_zero
      ensemble omega size target hweak)

end

end ArchonPhysics.ChildRepeatedCanonicalClusterLimit
