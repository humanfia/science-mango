import ArchonPhysics.CanonicalChildRepeatedFrequencyMismatchJointClosure
import ArchonPhysics.CanonicalDecayAnnealedSectorSmallBallAggregation
import ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge

/-!
# Canonical decay-sector volume domination

This module records the arbitrary-measurable-set analogue of the decay
small-ball aggregation.  In particular, the genuine two-mass child atlas is
pushed through the bounded physical frequency square to give a scalar
`ChildRepeated` mismatch estimate.  The four sector estimates then combine
exactly into the canonical annealed marked-mismatch domination interface.

No all-distinct or parent--child density estimate is invented here: those
three sector fields remain explicit inputs to the final aggregation theorem.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.CanonicalDecayAnnealedSectorVolumeDomination

open ArchonPhysics
open ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall
open ArchonPhysics.CanonicalChildRepeatedAnnealedSectorBridge
open ArchonPhysics.CanonicalChildRepeatedFrequencyMismatchJointClosure
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalDecayAnnealedSectorSmallBallAggregation
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
open ArchonPhysics.ChildRepeatedMismatchPushforwardLInfinity
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set

noncomputable section

/-- An arbitrary-measurable-set annealed density estimate for one member of
the canonical decay partition.  Marked index `n` corresponds to sector index
`n + 1`, exactly as in the four-sector finite-volume identity. -/
structure CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop) where
  constant : ENNReal
  constant_ne_top : constant ≠ ∞
  error : Nat → ENNReal
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound : ∀ n : Nat, ∀ A : Set Real, MeasurableSet A →
    (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        keep (n + 1) : Measure Real) A ≤
      constant * (volume : Measure Real) A + error n

/-- The strong actual two-mass atlas estimate pushes through
`(omega_parent, omega_child) ↦ omega_parent - 2 omega_child`.  The only
loss is the transverse physical frequency width `sqrt 5`; the exceptional
mass remains exactly the atlas bad error. -/
theorem canonicalDecaySectorAnnealed_childRepeated_apply_le_of_actualAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (n : Nat) {A : Set Real} (hA : MeasurableSet A) :
    (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst ↦ ChildRepeated) (n + 1) : Measure Real) A ≤
      (data.regularCeiling *
          ENNReal.ofReal collisionFrequencyCeiling) *
          (volume : Measure Real) A +
        data.badError n := by
  rw [canonicalDecaySectorAnnealed_childRepeated_eq_map_reduced]
  simp only [FiniteMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_childRepeatedDecayMismatch hA]
  let reduced : Measure (Real × Real) :=
    canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1)
  change reduced (childRepeatedDecayMismatch ⁻¹' A) ≤
    (data.regularCeiling * ENNReal.ofReal collisionFrequencyCeiling) *
      (volume : Measure Real) A + data.badError n
  have hsupport :
      reduced (childRepeatedFrequencySquare collisionFrequencyCeiling)ᶜ = 0 := by
    exact canonicalChildRepeatedReducedAnnealed_compl_frequencySquare_eq_zero
      (n + 1)
  have haesupport : ∀ᵐ frequency ∂reduced,
      frequency ∈ childRepeatedFrequencySquare collisionFrequencyCeiling :=
    ae_iff.mpr hsupport
  have hrestrict :
      reduced (childRepeatedDecayMismatch ⁻¹' A) =
        reduced
          (childRepeatedDecayMismatch ⁻¹' A ∩
            childRepeatedFrequencySquare collisionFrequencyCeiling) := by
    rw [← Measure.measure_inter_eq_of_ae haesupport]
    rw [inter_comm]
  rw [hrestrict]
  calc
    reduced
        (childRepeatedDecayMismatch ⁻¹' A ∩
          childRepeatedFrequencySquare collisionFrequencyCeiling) ≤
      data.regularCeiling *
          (volume : Measure (Real × Real))
            (childRepeatedDecayMismatch ⁻¹' A ∩
              childRepeatedFrequencySquare collisionFrequencyCeiling) +
        data.badError n :=
      canonicalChildRepeatedReducedAnnealed_apply_le_of_actualAtlas
        data n
        ((measurable_childRepeatedDecayMismatch hA).inter
          (childRepeatedFrequencySquare_isClosed
            collisionFrequencyCeiling).measurableSet)
    _ ≤ data.regularCeiling *
          (ENNReal.ofReal collisionFrequencyCeiling *
            (volume : Measure Real) A) + data.badError n := by
      gcongr
      exact
        volume_childRepeatedDecayMismatch_preimage_inter_frequencySquare_le
          hA
    _ = (data.regularCeiling *
          ENNReal.ofReal collisionFrequencyCeiling) *
          (volume : Measure Real) A + data.badError n := by
      rw [mul_assoc]

/-- The actual two-mass atlas sequence therefore discharges the complete
scalar `ChildRepeated` arbitrary-set sector field. -/
def canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence) :
    CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ChildRepeated) where
  constant := data.regularCeiling *
    ENNReal.ofReal collisionFrequencyCeiling
  constant_ne_top := ENNReal.mul_ne_top data.regularCeiling_ne_top
    ENNReal.ofReal_ne_top
  error := data.badError
  error_tendsto_zero := data.badError_tendsto_zero
  bound := canonicalDecaySectorAnnealed_childRepeated_apply_le_of_actualAtlas
    data

/-- Four arbitrary-set sector estimates aggregate to the honest canonical
annealed volume-domination certificate. -/
def canonicalMarkedMismatchAnnealedVolumeDomination_of_decaySectors
    (allDistinct : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ AllDistinctModes))
    (childRepeated : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ChildRepeated))
    (parentChildOne : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ParentChildOneRepeated))
    (parentChildTwo : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ParentChildTwoRepeated)) :
    CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination
      decayInteractionSign where
  constant := allDistinct.constant + childRepeated.constant +
    parentChildOne.constant + parentChildTwo.constant
  constant_ne_top := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨allDistinct.constant_ne_top, childRepeated.constant_ne_top⟩,
        parentChildOne.constant_ne_top⟩,
      parentChildTwo.constant_ne_top⟩
  error := fun n ↦ allDistinct.error n + childRepeated.error n +
    parentChildOne.error n + parentChildTwo.error n
  error_tendsto_zero := by
    simpa using
      (((allDistinct.error_tendsto_zero.add
        childRepeated.error_tendsto_zero).add
        parentChildOne.error_tendsto_zero).add
        parentChildTwo.error_tendsto_zero)
  bound := by
    intro n A hA
    rw [canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_decay_eq_sectorSum]
    simp only [FiniteMeasure.toMeasure_add, Measure.add_apply]
    calc
      _ ≤
          (allDistinct.constant * (volume : Measure Real) A +
              allDistinct.error n) +
            (childRepeated.constant * (volume : Measure Real) A +
              childRepeated.error n) +
            (parentChildOne.constant * (volume : Measure Real) A +
              parentChildOne.error n) +
            (parentChildTwo.constant * (volume : Measure Real) A +
              parentChildTwo.error n) := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (allDistinct.bound n A hA)
              (childRepeated.bound n A hA))
            (parentChildOne.bound n A hA))
          (parentChildTwo.bound n A hA)
      _ =
          (allDistinct.constant + childRepeated.constant +
              parentChildOne.constant + parentChildTwo.constant) *
              (volume : Measure Real) A +
            (allDistinct.error n + childRepeated.error n +
              parentChildOne.error n + parentChildTwo.error n) := by
        ring

/-- Consumer-ready specialization: the actual child atlas closes its sector,
so full decay domination is reduced to the all-distinct and the two
parent--child arbitrary-set fields. -/
def canonicalMarkedMismatchAnnealedVolumeDomination_of_decaySectors_of_childAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (allDistinct : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ AllDistinctModes))
    (parentChildOne : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ParentChildOneRepeated))
    (parentChildTwo : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ParentChildTwoRepeated)) :
    CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination
      decayInteractionSign :=
  canonicalMarkedMismatchAnnealedVolumeDomination_of_decaySectors
    allDistinct
    (canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
      data)
    parentChildOne parentChildTwo

/-- The resulting deterministic canonical decay collision measure is
Lebesgue dominated with the exact summed sector constant. -/
theorem canonicalCollisionPerSiteMeasureLimit_decay_le_smul_volume_of_sectors_of_childAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (allDistinct : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ AllDistinctModes))
    (parentChildOne : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ParentChildOneRepeated))
    (parentChildTwo : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ParentChildTwoRepeated)) :
    (canonicalCollisionPerSiteMeasureLimit canonicalIIDMassPhaseEnsemble
        decayInteractionSign : Measure Real) ≤
      (allDistinct.constant +
          data.regularCeiling * ENNReal.ofReal collisionFrequencyCeiling +
          parentChildOne.constant + parentChildTwo.constant) •
        (volume : Measure Real) := by
  have hdomination :=
    canonicalMarkedMismatchPerSiteLimit_le_smul_volume
      (canonicalMarkedMismatchAnnealedVolumeDomination_of_decaySectors_of_childAtlas
        data allDistinct parentChildOne parentChildTwo)
  change (((canonicalRankFrequencyMarkedPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble).map
        (markedFrequencyMismatch decayInteractionSign) : FiniteMeasure Real) :
      Measure Real) ≤ _ at hdomination
  rw [map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_eq_collision] at hdomination
  change (canonicalCollisionPerSiteMeasureLimit canonicalIIDMassPhaseEnsemble
      decayInteractionSign : Measure Real) ≤
    (allDistinct.constant +
        data.regularCeiling * ENNReal.ofReal collisionFrequencyCeiling +
        parentChildOne.constant + parentChildTwo.constant) •
      (volume : Measure Real) at hdomination
  exact hdomination

end

end ArchonPhysics.CanonicalDecayAnnealedSectorVolumeDomination
