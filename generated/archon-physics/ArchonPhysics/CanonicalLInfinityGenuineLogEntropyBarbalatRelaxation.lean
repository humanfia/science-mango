import ArchonPhysics.CanonicalLInfinityLogEntropyChainRule
import ArchonPhysics.CompactDissipationBarbalatRelaxation

/-!
# Genuine-log RN relaxation by the Barbalat route

This endpoint replaces monotonicity of the chosen physical deficit by uniform
continuity in time of the genuine scaled entropy production.  Compactness
still generates the entropy ceiling, while the strict-buffer chain rule
generates its derivative along the actual RN collision ODE.
-/

namespace ArchonPhysics.CanonicalLInfinityGenuineLogEntropyBarbalatRelaxation

open Filter MeasureTheory Set
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalLInfinityCompactEntropyRelaxation
open ArchonPhysics.CanonicalLInfinityLogEntropyChainRule
open ArchonPhysics.CanonicalLInfinityLogEntropyFunctional
open ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity
open ArchonPhysics.CompactDissipationBarbalatRelaxation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityEntropyStationarity
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A compact strictly positive RN orbit relaxes to the rigid equilibrium
class without assuming that the selected physical deficit is monotone. -/
theorem tendsto_deficit_zero_of_compact_canonicalLogEntropy_barbalat_rnCollisionODE
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision)
    (g : Real) (hg : g ≠ 0)
    {repairFloor actualBuffer : Real} (hrepairFloor : 0 < repairFloor)
    (hstrictBuffer : repairFloor < actualBuffer)
    (states : Set (CanonicalLInfinity collision)) (hstates : IsCompact states)
    (trajectory : Real -> CanonicalLInfinity collision)
    (deficit : CanonicalLInfinity collision -> Real)
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (htrajectoryODE : forall t, 0 <= t ->
      HasDerivAt trajectory
        (rnCollisionVectorField collision g (trajectory t)) t)
    (hdeficitContinuous : ContinuousOn deficit states)
    (hactionBuffer : forall action, action ∈ states ->
      AELowerBound collision actualBuffer action)
    (hdeficitEquilibrium : forall action, action ∈ states ->
      (exists scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure collision,
          (action mode)⁻¹ = scale * collision.frequency mode) ->
      deficit action = 0)
    (hdeficitNonnegative : forall t, 0 <= t ->
      0 <= deficit (trajectory t))
    (hdissipationTrajectoryUniformContinuous :
      UniformContinuousOn
        (fun t => g ^ 2 *
          canonicalLogEntropyProduction collision repairFloor (trajectory t))
        (Ici 0)) :
    Tendsto (fun t => deficit (trajectory t)) atTop (nhds 0) := by
  obtain ⟨entropyCeiling, hentropyCeiling⟩ :=
    exists_canonicalLogEntropy_ceiling_on_compact
      collision hrepairFloor states hstates
  apply tendsto_deficit_zero_of_compact_state_barbalat
    states hstates trajectory deficit
      (fun action => g ^ 2 *
        canonicalLogEntropyProduction collision repairFloor action)
      (fun t => canonicalLogEntropy collision repairFloor (trajectory t))
      entropyCeiling htrajectory hdeficitContinuous
  · exact ((continuous_const.mul
      (continuous_canonicalLogEntropyProduction
        collision hrepairFloor))).continuousOn
  · intro action _haction
    exact mul_nonneg (sq_nonneg g)
      (canonicalLogEntropyProduction_nonnegative
        collision hrepairFloor action)
  · intro action haction hzero
    have hproductionZero :
        canonicalLogEntropyProduction collision repairFloor action = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hg)
    have hrepairBound : AELowerBound collision repairFloor action :=
      (hactionBuffer action haction).mono fun _mode hmode =>
        (le_of_lt hstrictBuffer).trans hmode
    obtain ⟨_hstationary, scale, hscale⟩ :=
      stationary_and_inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
        collision hrigid hrepairFloor action hrepairBound hproductionZero
    exact hdeficitEquilibrium action haction ⟨scale, hscale⟩
  · exact hdeficitNonnegative
  · exact hdissipationTrajectoryUniformContinuous
  · intro t ht
    exact hasDerivAt_canonicalLogEntropy_along_rnCollisionODE
      collision g hrepairFloor hstrictBuffer trajectory
        (htrajectoryODE t ht)
        (hactionBuffer (trajectory t) (htrajectory t ht))
  · intro t ht
    exact hentropyCeiling (trajectory t) (htrajectory t ht)

end

end ArchonPhysics.CanonicalLInfinityGenuineLogEntropyBarbalatRelaxation
