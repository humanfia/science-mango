import ArchonPhysics.CanonicalOnShellMarkedClusterExistence
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Compact support of canonical on-shell marked weak limits

Every canonical broadened marked measure is carried by one common compact
rank--frequency box.  Finite-measure weak convergence also controls total
mass, so the closed-set half of Portmanteau shows that every weak limit,
including the zero limit, is carried by the same box.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport

open ArchonPhysics
open ArchonPhysics.CanonicalOnShellMarkedClusterExistence
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ModalPhaseMismatch
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Finite-measure weak convergence preserves a common closed carrier.  In
contrast with the probability-measure formulation, no nonzero hypothesis is
needed because weak convergence of finite measures also controls total mass. -/
theorem finiteMeasureWeakLimit_compl_closed_eq_zero
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (source : Nat -> FiniteMeasure X) (target : FiniteMeasure X)
    (hweak : Tendsto source atTop (nhds target))
    (K : Set X) (hK : IsClosed K)
    (hsupport : forall n, (source n : Measure X) Kᶜ = 0) :
    (target : Measure X) Kᶜ = 0 := by
  have hle := FiniteMeasure.limsup_measure_closed_le_of_tendsto hweak hK
  have hsourceOnK :
      (fun n => (source n : Measure X) K) =
        fun n => ((source n).mass : ENNReal) := by
    funext n
    rw [measure_of_measure_compl_eq_zero (hsupport n)]
    exact FiniteMeasure.ennreal_mass.symm
  have hmassENN : Tendsto (fun n => ((source n).mass : ENNReal))
      atTop (nhds (target.mass : ENNReal)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
  rw [hsourceOnK, hmassENN.limsup_eq] at hle
  have huniv_le : (target : Measure X) Set.univ <=
      (target : Measure X) K := by
    simpa only [FiniteMeasure.ennreal_mass] using hle
  have heq : (target : Measure X) K =
      (target : Measure X) Set.univ :=
    le_antisymm (measure_mono (Set.subset_univ K)) huniv_le
  rw [measure_compl hK.measurableSet (measure_ne_top _ _), heq]
  exact tsub_self _

/-- Every finite weak limit of canonical broadened marked measures is carried
by the same common compact box, including the zero limit. -/
theorem canonicalBroadenedWeakLimit_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble sign (time n) (htime_pos n))
      atTop (nhds target)) :
    (target : Measure (Fin 3 -> RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  apply finiteMeasureWeakLimit_compl_closed_eq_zero
    (fun n =>
      canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign (time n) (htime_pos n)) target hweak
    collisionRankFrequencyTripleSupport
    collisionRankFrequencyTripleSupport_isCompact.isClosed
  intro n
  exact
    canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
      ensemble sign (time n) (htime_pos n)

end

end ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
