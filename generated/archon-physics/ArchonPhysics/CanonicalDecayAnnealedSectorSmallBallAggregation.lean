import ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization
import ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedSmallBallBridge
import ArchonPhysics.DecaySectorAnnealedClusterBridge

/-!
# Canonical annealed decay-sector small-ball aggregation

The marked mismatch barycenter is exactly the sum of the four annealed
mode-equality sectors, with the one-step index shift forced by the marked
volume convention.  This is the model-side aggregation identity needed to
combine all-distinct, child-repeated, and the two automatic parent--child
estimates before passing to the deterministic thermodynamic limit.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalDecayAnnealedSectorSmallBallAggregation

open ArchonPhysics
open ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open MeasureTheory Set

noncomputable section

/-- Exact finite-volume law-level sector partition.  Marked index `n` has
physical volume `n + 3`, hence sector index `n + 1`. -/
theorem canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_decay_eq_sectorSum
    (n : Nat) :
    canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
        decayInteractionSign n =
      canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => AllDistinctModes) (n + 1) +
        canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ChildRepeated) (n + 1) +
        canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ParentChildOneRepeated) (n + 1) +
        canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ParentChildTwoRepeated) (n + 1) := by
  apply FiniteMeasure.toMeasure_injective
  ext A hA
  rw [canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_apply
    decayInteractionSign n hA]
  simp only [FiniteMeasure.toMeasure_add, Measure.add_apply]
  rw [canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
      (fun {_N} _inst => AllDistinctModes) (n + 1) hA,
    canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
      (fun {_N} _inst => ChildRepeated) (n + 1) hA,
    canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
      (fun {_N} _inst => ParentChildOneRepeated) (n + 1) hA,
    canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
      (fun {_N} _inst => ParentChildTwoRepeated) (n + 1) hA]
  simp_rw [map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_markedMismatch,
    canonicalCollisionPerSiteFiniteMeasure_decay_eq_sectorSum,
    FiniteMeasure.toMeasure_add, Measure.add_apply]
  have hall : Measurable fun omega =>
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst => AllDistinctModes) (n + 1) omega : Measure Real) A :=
    (Measure.measurable_coe hA).comp
      (measurable_toMeasure_canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst => AllDistinctModes) (n + 1))
  have hchild : Measurable fun omega =>
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst => ChildRepeated) (n + 1) omega : Measure Real) A :=
    (Measure.measurable_coe hA).comp
      (measurable_toMeasure_canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst => ChildRepeated) (n + 1))
  have hone : Measurable fun omega =>
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst => ParentChildOneRepeated) (n + 1) omega :
          Measure Real) A :=
    (Measure.measurable_coe hA).comp
      (measurable_toMeasure_canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst => ParentChildOneRepeated) (n + 1))
  calc
    _ =
        (∫⁻ omega,
          (canonicalDecaySectorPerSiteMismatchFiniteMeasure
                canonicalIIDMassPhaseEnsemble
                (fun {_N} _inst => AllDistinctModes) (n + 1) omega :
              Measure Real) A +
            (canonicalDecaySectorPerSiteMismatchFiniteMeasure
                canonicalIIDMassPhaseEnsemble
                (fun {_N} _inst => ChildRepeated) (n + 1) omega :
              Measure Real) A +
            (canonicalDecaySectorPerSiteMismatchFiniteMeasure
                canonicalIIDMassPhaseEnsemble
                (fun {_N} _inst => ParentChildOneRepeated) (n + 1) omega :
              Measure Real) A ∂ RandomEnsemble.canonicalLaw) +
          ∫⁻ omega,
            (canonicalDecaySectorPerSiteMismatchFiniteMeasure
                canonicalIIDMassPhaseEnsemble
                (fun {_N} _inst => ParentChildTwoRepeated) (n + 1) omega :
              Measure Real) A ∂ RandomEnsemble.canonicalLaw :=
      lintegral_add_left ((hall.add hchild).add hone) _
    _ =
        ((∫⁻ omega,
          (canonicalDecaySectorPerSiteMismatchFiniteMeasure
                canonicalIIDMassPhaseEnsemble
                (fun {_N} _inst => AllDistinctModes) (n + 1) omega :
              Measure Real) A +
            (canonicalDecaySectorPerSiteMismatchFiniteMeasure
                canonicalIIDMassPhaseEnsemble
                (fun {_N} _inst => ChildRepeated) (n + 1) omega :
              Measure Real) A ∂ RandomEnsemble.canonicalLaw) +
          ∫⁻ omega,
            (canonicalDecaySectorPerSiteMismatchFiniteMeasure
                canonicalIIDMassPhaseEnsemble
                (fun {_N} _inst => ParentChildOneRepeated) (n + 1) omega :
              Measure Real) A ∂ RandomEnsemble.canonicalLaw) +
        ∫⁻ omega,
          (canonicalDecaySectorPerSiteMismatchFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (fun {_N} _inst => ParentChildTwoRepeated) (n + 1) omega :
            Measure Real) A ∂ RandomEnsemble.canonicalLaw := by
      congr 1
      exact lintegral_add_left (hall.add hchild) _
    _ = _ := by
      congr 2
      exact lintegral_add_left hall _

end

end ArchonPhysics.CanonicalDecayAnnealedSectorSmallBallAggregation
