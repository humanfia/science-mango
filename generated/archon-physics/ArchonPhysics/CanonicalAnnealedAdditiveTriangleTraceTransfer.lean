import ArchonPhysics.AnnealedAdditiveTriangleCollisionKernel
import ArchonPhysics.CanonicalLInfinityGenuineLogEntropyCompactRelaxation
import ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity

/-!
# Canonical annealed trace transfer

This module isolates the one genuine random-lattice input which remains after
weak-limit graph support: equivalence of the canonical child-frequency trace
and the explicit nonzero annealed additive-triangle reference trace.  The
existing IDS graph theorem then supplies mode-to-frequency factorization, so
the certificate implies bounded-measurable rigidity and the compact RN
relaxation endpoint.
-/

namespace ArchonPhysics.CanonicalAnnealedAdditiveTriangleTraceTransfer

open Filter MeasureTheory Set
open ArchonPhysics.AnnealedAdditiveTriangleCollisionKernel
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalLInfinityGenuineLogEntropyCompactRelaxation
open ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

/-- The canonical target child trace and the explicit annealed reference have
the same null sets on the full physical additive triangle. -/
structure CanonicalTraceCertificate
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark)) : Prop where
  lower :
    (childFrequencyPairMeasure
        (annealedAdditiveTriangleCollision
          collisionFrequencyCeiling)).restrict
            (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling)
  upper :
    (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      (childFrequencyPairMeasure
        (annealedAdditiveTriangleCollision
          collisionFrequencyCeiling)).restrict
            (additiveFrequencyTriangle collisionFrequencyCeiling)

namespace CanonicalTraceCertificate

theorem volume_lower
    {target : FiniteMeasure (Fin 3 → RankFrequencyMark)}
    (certificate : CanonicalTraceCertificate target) :
    volume.restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) := by
  simpa [childFrequencyPairMeasure_restrict_eq] using certificate.lower

theorem volume_upper
    {target : FiniteMeasure (Fin 3 → RankFrequencyMark)}
    (certificate : CanonicalTraceCertificate target) :
    (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      volume.restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) := by
  simpa [childFrequencyPairMeasure_restrict_eq] using certificate.upper

/-- A nonzero a.e. density on the entire additive triangle is exactly the
model-side input needed to construct the canonical trace certificate. -/
theorem ofPositiveDensity
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    {density : Real × Real → ENNReal}
    (hdensity : AEMeasurable density
      (volume.restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling)))
    (hdensity_ne_zero :
      ∀ᵐ pair ∂volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling),
        density pair ≠ 0)
    (htrace :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) =
        (volume.restrict
          (additiveFrequencyTriangle
            collisionFrequencyCeiling)).withDensity density) :
    CanonicalTraceCertificate target where
  lower := by
    rw [childFrequencyPairMeasure_restrict_eq, htrace]
    exact withDensity_absolutelyContinuous' hdensity hdensity_ne_zero
  upper := by
    rw [childFrequencyPairMeasure_restrict_eq, htrace]
    exact withDensity_absolutelyContinuous _ _

end CanonicalTraceCertificate

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Weak-limit graph support plus the single trace certificate gives the
bounded-measurable rigidity contract. -/
theorem boundedMeasurableAEFrequencyBalanceRigid_of_traceCertificate
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (certificate : CanonicalTraceCertificate target) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    BoundedMeasurableAEFrequencyBalanceRigid collision := by
  exact
    boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_equivalentChildTrace
      ensemble time htime_pos htime target hweak certificate.volume_lower
        certificate.volume_upper

/-- The trace certificate directly replaces the atlas/rigidity premise in
the genuine-log-entropy compact RN relaxation theorem.  Compactness, strict
action buffer, and deficit coercivity remain explicit dynamical inputs. -/
theorem tendsto_deficit_zero_of_traceCertificate
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (traceCertificate : CanonicalTraceCertificate target)
    (g : Real) (hg : g ≠ 0)
    {repairFloor actualBuffer : Real} (hrepairFloor : 0 < repairFloor)
    (hstrictBuffer : repairFloor < actualBuffer)
    (states : Set (CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)))
    (hstates : IsCompact states)
    (trajectory : Real → CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak))
    (deficit : CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak) → Real)
    (htrajectory : ∀ t, 0 ≤ t → trajectory t ∈ states)
    (htrajectoryODE : ∀ t, 0 ≤ t →
      HasDerivAt trajectory
        (rnCollisionVectorField
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          g (trajectory t)) t)
    (hdeficitContinuous : ContinuousOn deficit states)
    (hactionBuffer : ∀ action, action ∈ states →
      AELowerBound
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak) actualBuffer action)
    (hdeficitEquilibrium : ∀ action, action ∈ states →
      (∃ scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure
            (ofCanonicalBroadenedWeakLimit ensemble time
              htime_pos htime target hweak),
          (action mode)⁻¹ = scale *
            (ofCanonicalBroadenedWeakLimit ensemble time
              htime_pos htime target hweak).frequency mode) →
      deficit action = 0)
    (hdeficitNonnegative : ∀ t, 0 ≤ t →
      0 ≤ deficit (trajectory t))
    (hdeficitAntitone :
      AntitoneOn (fun t => deficit (trajectory t)) (Ici 0)) :
    Tendsto (fun t => deficit (trajectory t)) atTop (nhds 0) := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  have hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision :=
    boundedMeasurableAEFrequencyBalanceRigid_of_traceCertificate
      ensemble time htime_pos htime target hweak traceCertificate
  exact tendsto_deficit_zero_of_compact_canonicalLogEntropy_rnCollisionODE
    collision hrigid g hg hrepairFloor hstrictBuffer states hstates
      trajectory deficit htrajectory htrajectoryODE hdeficitContinuous
      hactionBuffer hdeficitEquilibrium hdeficitNonnegative
      hdeficitAntitone

end

end ArchonPhysics.CanonicalAnnealedAdditiveTriangleTraceTransfer
