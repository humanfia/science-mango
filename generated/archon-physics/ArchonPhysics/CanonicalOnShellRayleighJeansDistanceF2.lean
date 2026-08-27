import ArchonPhysics.CanonicalOnShellAutomaticGenuineLogEntropyBarbalatRelaxation
import ArchonPhysics.PositiveTimeTwoTimeKineticHittingBounds

/-!
# A concrete Rayleigh--Jeans distance for the canonical on-shell F2 route

The target-facing entropy relaxation theorem accepts an abstract nonnegative
continuous deficit which vanishes on every Rayleigh--Jeans equilibrium.  This
module supplies such a deficit rather than leaving those three properties as
contracts: it is the metric distance in canonical `L-infinity` to the set of
all inverse-frequency equilibrium classes.

For the actual canonical broadened weak-limit collision, the existing
cross-volume rigidity and genuine logarithmic entropy theorem therefore give
convergence of this concrete distance to zero.  Continuity of the collision
ODE at time zero then turns an initially separated positive threshold into a
robust two-time kinetic hitting window.

The theorem deliberately retains the genuinely model-specific cross-volume
atlas estimates and the genuinely dynamical compact positive global orbit.
It is a continuum F2 endpoint; it does not manufacture the finite-model
`RobustTwoTimeF2Certificate` used by the current release adapter.
-/

namespace ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2

open Filter MeasureTheory Metric Set
open ArchonPhysics
open ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
open ArchonPhysics.CanonicalOnShellAutomaticGenuineLogEntropyBarbalatRelaxation
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.PositiveTimeTwoTimeKineticHittingBounds
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.TwoTimeKineticHittingBounds
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The full Rayleigh--Jeans equilibrium class of one resonant collision
measure: inverse action is proportional to frequency almost everywhere. -/
def rayleighJeansEquilibriumSet
    (collision : ResonantThreeWaveMeasure Mode) :
    Set (CanonicalLInfinity collision) :=
  {action | exists scale : Real,
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      (action mode)⁻¹ = scale * collision.frequency mode}

/-- Canonical `L-infinity` distance to the full Rayleigh--Jeans equilibrium
class.  This is a concrete, nonnegative physical deficit. -/
def rayleighJeansDistance
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) : Real :=
  infDist action (rayleighJeansEquilibriumSet collision)

/-- The concrete Rayleigh--Jeans distance is globally continuous. -/
theorem continuous_rayleighJeansDistance
    (collision : ResonantThreeWaveMeasure Mode) :
    Continuous (rayleighJeansDistance collision) := by
  exact continuous_infDist_pt (rayleighJeansEquilibriumSet collision)

/-- The concrete Rayleigh--Jeans distance is nonnegative. -/
theorem rayleighJeansDistance_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    0 <= rayleighJeansDistance collision action := by
  exact infDist_nonneg

/-- Every inverse-frequency equilibrium has zero concrete distance. -/
theorem rayleighJeansDistance_eq_zero_of_equilibrium
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision)
    (haction : exists scale : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        (action mode)⁻¹ = scale * collision.frequency mode) :
    rayleighJeansDistance collision action = 0 := by
  exact infDist_zero_of_mem haction

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Under the actual canonical on-shell atlas and compact positive global
orbit hypotheses, the concrete distance to the Rayleigh--Jeans class tends
to zero.  Continuity, nonnegativity, and the equilibrium zero-set condition
are all discharged by `rayleighJeansDistance`. -/
theorem tendsto_rayleighJeansDistance_zero_of_canonicalOnShell
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target))
    (spec : Nat -> ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec collisionFrequencyCeiling)
    (hupper :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling))
    (g : Real) (hg : g ≠ 0)
    {repairFloor actualBuffer : Real} (hrepairFloor : 0 < repairFloor)
    (hstrictBuffer : repairFloor < actualBuffer)
    (states : Set (CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)))
    (hstates : IsCompact states)
    (trajectory : Real -> CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak))
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (htrajectoryODE : forall t, 0 <= t ->
      HasDerivAt trajectory
        (rnCollisionVectorField
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          g (trajectory t)) t)
    (hactionBuffer : forall action, action ∈ states ->
      AELowerBound
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak) actualBuffer action) :
    Tendsto
      (fun t => rayleighJeansDistance
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak)
        (trajectory t))
      atTop (nhds 0) := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  exact
    tendsto_deficit_zero_of_canonicalOnShell_crossVolume_automatic_barbalat
      ensemble time htime_pos htime target hweak spec hlocal hcover hupper
        g hg hrepairFloor hstrictBuffer states hstates trajectory
        (rayleighJeansDistance collision) htrajectory htrajectoryODE
        (continuous_rayleighJeansDistance collision).continuousOn
        hactionBuffer
        (fun action _haction hequilibrium =>
          rayleighJeansDistance_eq_zero_of_equilibrium
            collision action hequilibrium)
        (fun t _ht => rayleighJeansDistance_nonnegative
          collision (trajectory t))

/-- The same genuine entropy relaxation produces the release-relevant robust
two-time window for the concrete continuum Rayleigh--Jeans distance whenever
the initial distance is strictly above a positive threshold. -/
theorem exists_robustRayleighJeansHittingWindow_of_canonicalOnShell
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target))
    (spec : Nat -> ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec collisionFrequencyCeiling)
    (hupper :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling))
    (g : Real) (hg : g ≠ 0)
    {repairFloor actualBuffer : Real} (hrepairFloor : 0 < repairFloor)
    (hstrictBuffer : repairFloor < actualBuffer)
    (states : Set (CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)))
    (hstates : IsCompact states)
    (trajectory : Real -> CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak))
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (htrajectoryODE : forall t, 0 <= t ->
      HasDerivAt trajectory
        (rnCollisionVectorField
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          g (trajectory t)) t)
    (hactionBuffer : forall action, action ∈ states ->
      AELowerBound
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak) actualBuffer action)
    (delta : Real) (hdelta : 0 < delta)
    (hseparated : delta < rayleighJeansDistance
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)
      (trajectory 0)) :
    exists lower upper : Real,
      RobustKineticHittingWindow
        (fun t => rayleighJeansDistance
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          (trajectory t))
        delta lower upper := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  let distance : Real -> Real :=
    fun t => rayleighJeansDistance collision (trajectory t)
  have hrelax : Tendsto distance atTop (nhds 0) := by
    exact tendsto_rayleighJeansDistance_zero_of_canonicalOnShell
      ensemble time htime_pos htime target hweak spec hlocal hcover hupper
        g hg hrepairFloor hstrictBuffer states hstates trajectory
        htrajectory htrajectoryODE hactionBuffer
  have htrajectoryContinuousAt : ContinuousAt trajectory 0 :=
    (htrajectoryODE 0 le_rfl).continuousAt
  have hdistanceContinuousAt : ContinuousAt distance 0 := by
    exact (continuous_rayleighJeansDistance collision).continuousAt.comp
      htrajectoryContinuousAt
  have hright : Tendsto distance (nhdsWithin 0 (Ioi 0))
      (nhds (rayleighJeansDistance collision (trajectory 0))) :=
    hdistanceContinuousAt.mono_left inf_le_left
  exact exists_robustKineticHittingWindow_of_tendsto_right
    distance (rayleighJeansDistance collision (trajectory 0)) delta
      hdelta hseparated hright hrelax

end

end ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
