import ArchonPhysics.CanonicalAnnealedAdditiveTriangleTraceTransfer
import ArchonPhysics.CanonicalChildRepeatedAnnealedCompactAtlasCertificate
import ArchonPhysics.CanonicalOnShellChildPairUniformIntegrabilityClosure
import ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity

/-!
# Canonical child atlases and the full trace certificate

There are two different measure-theoretic statements in the child-atlas
chain, and this module keeps them separate.

* A compact child-repeated atlas controls one-dimensional resonance strips
  for that sector.  It supplies the child-repeated small-ball certificate.
* A full canonical child trace is a two-dimensional measure.  Its upper
  absolute continuity follows from the uniform lifted-density estimate, and
  its lower absolute continuity follows from actual cross-volume chart
  coverage together with local lower averaging.

Consequently the compact child-repeated atlas alone is not used to claim
absolute continuity of the full trace.  The final constructor below exposes
the lifted-density, local-averaging, and coverage inputs explicitly.
-/

namespace ArchonPhysics.CanonicalChildAtlasTraceCertificateBridge

open Filter MeasureTheory Set
open ArchonPhysics
open ArchonPhysics.AnnealedAdditiveTriangleCollisionKernel
open ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
open ArchonPhysics.CanonicalAnnealedAdditiveTriangleTraceTransfer
open ArchonPhysics.CanonicalChildRepeatedAnnealedCompactAtlasCertificate
open ArchonPhysics.CanonicalDecayAnnealedSmallBallCertificate
open ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellChildPairUniformIntegrabilityClosure
open ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open scoped ENNReal MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A uniform density bound for the raw lifted Euclidean frequency law gives
the `upper` field of the full canonical trace certificate.  This is a
large-time weak-limit statement, not a realization-wise density claim. -/
theorem canonicalTraceCertificate_upper_of_euclidean_lifted_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n ↦
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (C : ENNReal) (hC : C ≠ ∞)
    (hlifted :
      Measure.map
          (euclideanChildMismatchCoordinates
            RandomMassThreeWaveCollisionNetwork.decayInteractionSign)
          (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
            Measure (EuclideanSpace Real (Fin 3))) ≤
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) :
    (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      (childFrequencyPairMeasure
        (annealedAdditiveTriangleCollision
          collisionFrequencyCeiling)).restrict
            (additiveFrequencyTriangle collisionFrequencyCeiling) := by
  have hupper :=
    canonicalBroadenedWeakLimit_childPair_upperAbsoluteContinuity_of_euclidean_lifted_le
      ensemble time htime_pos target hweak C hC hlifted
  simpa [childFrequencyPairMeasure_restrict_eq] using hupper

/-- Actual cross-volume two-mass charts give the `lower` field of the full
canonical trace certificate, provided their regular images cover the whole
triangle a.e. and every local weighted chart law is seen by the target.
Neither condition is inferred from compactness or Jacobian regularity. -/
theorem canonicalTraceCertificate_lower_of_crossVolume_actualAtlas
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (spec : Nat → ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling
        (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec
      collisionFrequencyCeiling) :
    (childFrequencyPairMeasure
        (annealedAdditiveTriangleCollision
          collisionFrequencyCeiling)).restrict
            (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) := by
  have hlower :
      volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) := by
    exact
      volume_additiveTriangle_ac_of_crossVolume_actualTwoMass_regularSources
        spec collisionFrequencyCeiling
          (Measure.map markedChildFrequencyPair target)
          (by
            simpa [CrossVolumeActualLocalLowerAveraging] using hlocal)
          (by simpa [CrossVolumeActualTriangleCover] using hcover)
  simpa [childFrequencyPairMeasure_restrict_eq] using hlower

/-- The strongest current actual-model constructor for the full canonical
trace certificate.  Its upper and lower model inputs are visibly distinct:
uniform lifted density for upper AC, and actual local averaging plus full
triangle coverage for lower AC. -/
theorem canonicalTraceCertificate_of_crossVolume_actualAtlas_of_lifted_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n ↦
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (spec : Nat → ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling
        (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec
      collisionFrequencyCeiling)
    (C : ENNReal) (hC : C ≠ ∞)
    (hlifted :
      Measure.map
          (euclideanChildMismatchCoordinates
            RandomMassThreeWaveCollisionNetwork.decayInteractionSign)
          (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
            Measure (EuclideanSpace Real (Fin 3))) ≤
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) :
    CanonicalTraceCertificate target where
  lower := canonicalTraceCertificate_lower_of_crossVolume_actualAtlas
    target spec hlocal hcover
  upper := canonicalTraceCertificate_upper_of_euclidean_lifted_le
    ensemble time htime_pos target hweak C hC hlifted
/-- Two-sided trace absolute continuity has the exact density consequence:
the canonical child trace is the planar restricted-volume measure with its
Radon--Nikodym density, and that density is nonzero almost everywhere on the
whole physical triangle. -/
theorem canonicalTraceCertificate_exists_ae_nonzero_density
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (certificate : CanonicalTraceCertificate target) :
    ∃ density : Real × Real → ENNReal,
      Measurable density ∧
      (∀ᵐ pair ∂volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling),
        density pair ≠ 0) ∧
      (volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling)).withDensity
            density =
        (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) := by
  let reference : Measure (Real × Real) :=
    volume.restrict
      (additiveFrequencyTriangle collisionFrequencyCeiling)
  let trace : Measure (Real × Real) :=
    (Measure.map markedChildFrequencyPair target).restrict
      (additiveFrequencyTriangle collisionFrequencyCeiling)
  have hupper : trace ≪ reference := by
    simpa only [trace, reference] using certificate.volume_upper
  have hlower : reference ≪ trace := by
    simpa only [trace, reference] using certificate.volume_lower
  have hpositiveTrace :
      ∀ᵐ pair ∂trace, 0 < trace.rnDeriv reference pair :=
    Measure.rnDeriv_pos hupper
  have hpositiveReference :
      ∀ᵐ pair ∂reference, 0 < trace.rnDeriv reference pair :=
    hlower.ae_le hpositiveTrace
  refine ⟨trace.rnDeriv reference, Measure.measurable_rnDeriv _ _, ?_, ?_⟩
  · simpa only [trace, reference] using
      hpositiveReference.mono fun _pair hpositive ↦ ne_of_gt hpositive
  · simpa only [trace, reference] using
      Measure.withDensity_rnDeriv_eq trace reference hupper


/-- The two certificates produced by the child-atlas chain live at different
measure levels, so they are recorded as separate fields rather than as one
unqualified absolute-continuity assertion. -/
structure ChildRepeatedSmallBallTraceBundle
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark)) where
  smallBall : CanonicalDecaySectorAnnealedMarkedIndexSmallBallBound
    (fun {_N} _inst ↦ ChildRepeated)
  trace : CanonicalTraceCertificate target


/-- Honest combined endpoint for the compact child-repeated atlas and the
full two-dimensional trace.  The compact atlas discharges only the
child-repeated small-ball factor; the full trace certificate still uses the
separate actual coverage and lifted-density inputs above. -/
def childRepeatedSmallBall_and_traceCertificate
    (data : ActualTwoMassChildRepeatedAnnealedCompactAtlasSequence)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n ↦
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (spec : Nat → ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling
        (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec
      collisionFrequencyCeiling)
    (C : ENNReal) (hC : C ≠ ∞)
    (hlifted :
      Measure.map
          (euclideanChildMismatchCoordinates
            RandomMassThreeWaveCollisionNetwork.decayInteractionSign)
          (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
            Measure (EuclideanSpace Real (Fin 3))) ≤
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) :
    ChildRepeatedSmallBallTraceBundle target where
  smallBall :=
    canonicalChildRepeatedDecaySectorAnnealedSmallBallBound_of_compactAtlas
      data
  trace :=
    canonicalTraceCertificate_of_crossVolume_actualAtlas_of_lifted_le
      ensemble time htime_pos target hweak spec hlocal hcover C hC hlifted

end

end ArchonPhysics.CanonicalChildAtlasTraceCertificateBridge
