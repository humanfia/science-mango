import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
import ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
import ArchonPhysics.DecayChannelMismatchSectorWeakLimit

/-!
# Exact four-sector partition of canonical marked collision measures

The decay-channel mode-equality partition is lifted here without loss to the
rank-frequency marked measure.  The construction is exact at every finite
volume and commutes with the signed mismatch pushforward.  Consequently the
two regular sectors and the two parent--child error sectors can be recombined
before resonance broadening; no global joint density is assumed.
-/

open scoped ENNReal

namespace ArchonPhysics.CanonicalRankFrequencyMarkedFourSectorPartition

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Exact four-sector partition of the raw marked rank-frequency measure. -/
theorem positiveWeightedRankFrequencyTripleMeasure_eq_modeEqualityPartition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedRankFrequencyTripleMeasure m =
      positiveWeightedRankFrequencyTripleMeasureWhere m AllDistinctModes +
      positiveWeightedRankFrequencyTripleMeasureWhere m ChildRepeated +
      positiveWeightedRankFrequencyTripleMeasureWhere
        m ParentChildOneRepeated +
      positiveWeightedRankFrequencyTripleMeasureWhere
        m ParentChildTwoRepeated := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasure
    positiveWeightedRankFrequencyTripleMeasureWhere
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · by_cases hchild : modes 1 = modes 2
    · simp [hpositive, ChildRepeated, ParentChildOneRepeated,
        ParentChildTwoRepeated, AllDistinctModes, hchild]
    · by_cases hone : modes 0 = modes 1
      · simp [hpositive, ChildRepeated, ParentChildOneRepeated,
          ParentChildTwoRepeated, AllDistinctModes, hchild, hone]
      · by_cases htwo : modes 0 = modes 2
        · have htwoOne : modes 2 ≠ modes 1 := Ne.symm hchild
          simp [hpositive, ChildRepeated, ParentChildOneRepeated,
            ParentChildTwoRepeated, AllDistinctModes, hchild, htwo, htwoOne]
        · simp [hpositive, ChildRepeated, ParentChildOneRepeated,
            ParentChildTwoRepeated, AllDistinctModes, hchild, hone, htwo]
  · simp [hpositive]

/-- Bundled finite-measure form of the exact raw partition. -/
theorem positiveWeightedRankFrequencyTripleFiniteMeasure_eq_modeEqualityPartition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedRankFrequencyTripleFiniteMeasure m =
      positiveWeightedRankFrequencyTripleFiniteMeasureWhere
          m AllDistinctModes +
        positiveWeightedRankFrequencyTripleFiniteMeasureWhere
          m ChildRepeated +
        positiveWeightedRankFrequencyTripleFiniteMeasureWhere
          m ParentChildOneRepeated +
        positiveWeightedRankFrequencyTripleFiniteMeasureWhere
          m ParentChildTwoRepeated := by
  apply FiniteMeasure.toMeasure_injective
  exact positiveWeightedRankFrequencyTripleMeasure_eq_modeEqualityPartition m

/-- One canonical per-site marked sector, indexed with the same `n + 2`
physical volume convention as the complete marked measure. -/
def canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (n : Nat) (omega : Omega) :
    FiniteMeasure (Fin 3 → RankFrequencyMark) :=
  (((n + 2 : Nat) : NNReal)⁻¹) •
    positiveWeightedRankFrequencyTripleFiniteMeasureWhere
      (ensemble.restrictPositiveMass (N := n + 2) omega)
      (keep (N := n + 2))

/-- The complete canonical marked measure is exactly the sum of its four
mode-equality sectors at every finite volume. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_eq_sectorSum
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega =
      canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure ensemble
          (fun {_N} _inst ↦ AllDistinctModes) n omega +
        canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure ensemble
          (fun {_N} _inst ↦ ChildRepeated) n omega +
        canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure ensemble
          (fun {_N} _inst ↦ ParentChildOneRepeated) n omega +
        canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure ensemble
          (fun {_N} _inst ↦ ParentChildTwoRepeated) n omega := by
  unfold canonicalRankFrequencyTriplePerSiteFiniteMeasure
    canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure
  rw [positiveWeightedRankFrequencyTripleFiniteMeasure_eq_modeEqualityPartition,
    smul_add, smul_add, smul_add]

/-- On marked tuples, the Euclidean mismatch definition reduces exactly to
the ordinary signed mismatch of the forgotten frequency triple. -/
theorem markedFrequencyMismatch_eq_frequencyTripleMismatch_forgetRank
    (sign : Fin 3 → InteractionSign) :
    markedFrequencyMismatch sign =
      frequencyTripleMismatch sign ∘ forgetRankFrequencyTriple := by
  funext marks
  simp [markedFrequencyMismatch, forgetRankFrequencyTripleEuclidean,
    euclideanFrequencyTripleMismatch]

/-- Signed mismatch pushforward of any raw marked sector is exactly the
corresponding scalar sector. -/
theorem map_positiveWeightedRankFrequencyTripleMeasureWhere_markedMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) :
    Measure.map (markedFrequencyMismatch sign)
        (positiveWeightedRankFrequencyTripleMeasureWhere m keep) =
      positiveWeightedMismatchMeasureWhere m sign keep := by
  rw [markedFrequencyMismatch_eq_frequencyTripleMismatch_forgetRank]
  rw [← Measure.map_map (measurable_frequencyTripleMismatch sign)
    measurable_forgetRankFrequencyTriple]
  rw [map_positiveWeightedRankFrequencyTripleMeasureWhere_forgetRank]
  exact map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere
    m sign keep

/-- Canonical per-site normalization commutes exactly with the signed
mismatch pushforward on every sector. -/
theorem map_canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure_mismatch
    (ensemble : IIDMassPhaseEnsemble Omega)
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (n : Nat) (omega : Omega) :
    (canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure
        ensemble keep n omega).map
          (markedFrequencyMismatch decayInteractionSign) =
      canonicalDecaySectorPerSiteMismatchFiniteMeasure
        ensemble keep n omega := by
  apply FiniteMeasure.toMeasure_injective
  unfold canonicalRankFrequencyMarkedSectorPerSiteFiniteMeasure
    canonicalDecaySectorPerSiteMismatchFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasureWhere
  rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_smul,
    Measure.map_smul]
  change _ • Measure.map (markedFrequencyMismatch decayInteractionSign)
      (positiveWeightedRankFrequencyTripleMeasureWhere
        (ensemble.restrictPositiveMass (N := n + 2) omega)
        (keep (N := n + 2))) = _
  rw [map_positiveWeightedRankFrequencyTripleMeasureWhere_markedMismatch]
  rw [FiniteMeasure.toMeasure_smul]
  rfl

end

end ArchonPhysics.CanonicalRankFrequencyMarkedFourSectorPartition
