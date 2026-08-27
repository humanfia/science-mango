import ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
import ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit

/-!
# Canonical on-shell weak limits inherit the scalar-IDS graph

The deterministic raw marked thermodynamic measure is a positive scalar
multiple of the canonical graph-lift probability measure.  Weighting it by a
finite-time resonance density cannot create mass outside that graph.  Since
the graph is closed, every subsequent finite-measure weak limit remains on
the same graph.
-/

namespace ArchonPhysics.CanonicalOnShellMarkedGraphSupport

open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSContinuity
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The unnormalized deterministic marked limit is carried by the fixed
canonical scalar-IDS graph. -/
theorem canonicalRankFrequencyMarkedPerSiteMeasureLimit_compl_graph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
      Measure (Fin 3 -> RankFrequencyMark))
        (rankFrequencyTripleGraph canonicalScalarIDSValue)ᶜ = 0 := by
  have hac :
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
        Measure (Fin 3 -> RankFrequencyMark)) ≪
      (canonicalRankFrequencyMarkedMeasureLimit ensemble :
        Measure (Fin 3 -> RankFrequencyMark)) := by
    unfold canonicalRankFrequencyMarkedPerSiteMeasureLimit
    rw [FiniteMeasure.toMeasure_smul,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  exact hac
    (canonicalRankFrequencyMarkedMeasureLimit_compl_graph_eq_zero ensemble)

/-- Multiplication by the normalized finite-time resonance density preserves
the fixed scalar-IDS graph carrier. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_graph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (T : Real) (hT : 0 < T) :
    (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
      ensemble sign T hT : Measure (Fin 3 -> RankFrequencyMark))
        (rankFrequencyTripleGraph canonicalScalarIDSValue)ᶜ = 0 := by
  have hac :
      (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign T hT : Measure (Fin 3 -> RankFrequencyMark)) ≪
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
        Measure (Fin 3 -> RankFrequencyMark)) := by
    unfold canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
      broadenedResonanceMeasure
    exact withDensity_absolutelyContinuous _ _
  exact hac
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit_compl_graph_eq_zero
      ensemble)

/-- Every large-time canonical broadened weak limit is automatically carried
by the same fixed scalar-IDS graph. -/
theorem canonicalBroadenedWeakLimit_compl_graph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble sign (time n) (htime_pos n))
      atTop (nhds target)) :
    (target : Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph canonicalScalarIDSValue)ᶜ = 0 := by
  apply finiteMeasureWeakLimit_compl_closed_eq_zero
    (fun n =>
      canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign (time n) (htime_pos n))
    target hweak (rankFrequencyTripleGraph canonicalScalarIDSValue)
    (isClosed_rankFrequencyTripleGraph continuous_canonicalScalarIDSValue)
  intro n
  exact
    canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_graph_eq_zero
      ensemble sign (time n) (htime_pos n)

end

end ArchonPhysics.CanonicalOnShellMarkedGraphSupport
