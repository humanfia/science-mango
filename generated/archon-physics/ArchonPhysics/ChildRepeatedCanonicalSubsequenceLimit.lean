import ArchonPhysics.ChildRepeatedCanonicalClusterLimit
import ArchonPhysics.DecayChannelMismatchSectorWeakLimit

/-!
# Frozen-iid child-repeated subsequences and mismatch-sector alignment

This file identifies the scalar pushforward of the marked child-repeated
component with the exact `ChildRepeated` term in the decay-sector DAG.  It
also packages the only honest exact-resonance criterion for this singular
component: its zero-mismatch atom vanishes precisely when the reduced
parent/child law gives no mass to `omega_parent = 2 * omega_child`.

Finally, compact support and the grounded simple-spectrum event construct an
almost-sure cofinal marked cluster point.  The already proved full canonical
marked convergence is retained along the same selected subsequence.
-/

open scoped Topology

namespace ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Exact alignment with the scalar decay-sector DAG -/

/-- At every canonical volume, the scalar decay pushforward of the
child-repeated frequency component is exactly the `ChildRepeated` sector used
by `DecayChannelMismatchSectorWeakLimit`. -/
theorem map_canonicalChildRepeatedFrequencyPerSiteFiniteMeasure_decay_eq_sector
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    (canonicalChildRepeatedFrequencyPerSiteFiniteMeasure ensemble n omega).map
        (frequencyTripleMismatch decayInteractionSign) =
      canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) n omega := by
  apply FiniteMeasure.toMeasure_injective
  change Measure.map (frequencyTripleMismatch decayInteractionSign)
      (perSitePositiveWeightedFrequencyTripleMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated) =
    ((((n + 2 : Nat) : NNReal)⁻¹ •
      positiveWeightedMismatchFiniteMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega)
        decayInteractionSign ChildRepeated : FiniteMeasure Real) : Measure Real)
  unfold perSitePositiveWeightedFrequencyTripleMeasureWhere
  rw [Measure.map_smul]
  rw [map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere]
  rw [FiniteMeasure.toMeasure_smul]
  change (((n + 2 : Nat) : ENNReal)⁻¹ •
      positiveWeightedMismatchMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega)
        decayInteractionSign ChildRepeated) =
    ((((((n + 2 : Nat) : NNReal)⁻¹ : NNReal) : ENNReal)) •
      positiveWeightedMismatchMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega)
        decayInteractionSign ChildRepeated)
  rw [ENNReal.coe_inv (by positivity : ((n + 2 : Nat) : NNReal) ≠ 0)]
  rfl

/-- A marked child-component weak limit therefore supplies, by continuous
pushforward, a genuine weak limit for the scalar `ChildRepeated` DAG sector. -/
theorem canonicalChildRepeated_decaySector_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) (size j) omega)
      atTop
      (nhds ((target.map forgetRankFrequencyTriple).map
        (frequencyTripleMismatch decayInteractionSign))) := by
  have hfrequency := canonicalChildRepeated_frequencyMarginal_tendsto
    ensemble omega size target hweak
  have hmismatch := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
    (fun j => canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
      ensemble (size j) omega)
    (target.map forgetRankFrequencyTriple) hfrequency
      (show Continuous (frequencyTripleMismatch decayInteractionSign) by
        unfold frequencyTripleMismatch
        fun_prop)
  apply hmismatch.congr'
  exact Eventually.of_forall fun j =>
    map_canonicalChildRepeatedFrequencyPerSiteFiniteMeasure_decay_eq_sector
      ensemble (size j) omega

/-! ## The exact conditional zero-atom interface -/

/-- The reduced exact-resonance line
`omega_parent - 2 * omega_child = 0`. -/
def childRepeatedReducedResonanceLine : Set (Real × Real) :=
  {frequency | childRepeatedDecayMismatch frequency = 0}

theorem childRepeatedReducedResonanceLine_isClosed :
    IsClosed childRepeatedReducedResonanceLine := by
  exact isClosed_eq continuous_childRepeatedDecayMismatch continuous_const

/-- Evaluation of the reduced mismatch pushforward at zero is exactly the
mass of the two-coordinate law on the reduced resonance line. -/
theorem map_childRepeatedDecayMismatch_singleton_zero
    (measure : FiniteMeasure (Real × Real)) :
    (measure.map childRepeatedDecayMismatch : Measure Real)
        ({0} : Set Real) =
      (measure : Measure (Real × Real))
        childRepeatedReducedResonanceLine := by
  rw [FiniteMeasure.toMeasure_map, Measure.map_apply
    measurable_childRepeatedDecayMismatch (measurableSet_singleton 0)]
  rfl

/-- Thus the child scalar mismatch cluster is zero-atom exactly when its
reduced singular law gives the reaction line zero mass. -/
theorem canonicalChildRepeatedMarkedWeakLimit_decay_singleton_zero_iff
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target)) :
    (((target.map forgetRankFrequencyTriple).map
        (frequencyTripleMismatch decayInteractionSign) :
      FiniteMeasure Real) : Measure Real) ({0} : Set Real) = 0 ↔
    (((target.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))
        childRepeatedReducedResonanceLine = 0 := by
  rw [canonicalChildRepeatedMarkedWeakLimit_decayMismatch_eq_reduced
    ensemble omega size target hweak]
  rw [map_childRepeatedDecayMismatch_singleton_zero]

/-- One-sided form convenient for the sector recombination theorem. -/
theorem canonicalChildRepeatedMarkedWeakLimit_decay_singleton_zero_of_reducedLine
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size j) omega)
      atTop (nhds target))
    (hline : (((target.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))
        childRepeatedReducedResonanceLine = 0) :
    (((target.map forgetRankFrequencyTriple).map
        (frequencyTripleMismatch decayInteractionSign) :
      FiniteMeasure Real) : Measure Real) ({0} : Set Real) = 0 :=
  (canonicalChildRepeatedMarkedWeakLimit_decay_singleton_zero_iff
    ensemble omega size target hweak).2 hline

end

end ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit
