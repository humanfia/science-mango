import ArchonPhysics.CanonicalDecayAnnealedParentChildSmallBall

/-!
# Canonical decay small-ball reduction to the two main sectors

The full marked decay-channel mismatch measure is reduced here to annealed
small-ball estimates for only the all-distinct and child-repeated sectors.
The two parent--child sectors are discharged by their already proved
quadratic bounds.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalDecayAnnealedMainSectorSmallBallReduction

open ArchonPhysics
open ArchonPhysics.CanonicalDecayAnnealedParentChildSmallBall
open ArchonPhysics.CanonicalDecayAnnealedSectorSmallBallAggregation
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedSmallBallBridge
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- Real evaluation of the law-level four-sector identity is bounded by the
sum of the four real evaluations.  This form avoids any irrelevant finiteness
side conditions in downstream estimates. -/
theorem canonicalMarkedMismatchAnnealed_decay_apply_toReal_le_sectorSum
    (n : Nat) (A : Set Real) :
    ((canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
        decayInteractionSign n : Measure Real) A).toReal ≤
      ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => AllDistinctModes) (n + 1) : Measure Real) A).toReal +
        ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ChildRepeated) (n + 1) : Measure Real) A).toReal +
        ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ParentChildOneRepeated) (n + 1) : Measure Real) A).toReal +
        ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ParentChildTwoRepeated) (n + 1) : Measure Real) A).toReal := by
  rw [canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_decay_eq_sectorSum]
  simp only [FiniteMeasure.toMeasure_add, Measure.add_apply]
  have hsum (a b c d : ENNReal) :
      (((a + b) + c) + d).toReal ≤
        ((a.toReal + b.toReal) + c.toReal) + d.toReal := by
    calc
      _ ≤ ((a + b) + c).toReal + d.toReal := ENNReal.toReal_add_le
      _ ≤ ((a + b).toReal + c.toReal) + d.toReal := by
        gcongr
        exact (ENNReal.toReal_add_le :
          (a + b + c).toReal ≤ (a + b).toReal + c.toReal)
      _ ≤ _ := by
        gcongr
        exact (ENNReal.toReal_add_le :
          (a + b).toReal ≤ a.toReal + b.toReal)
  exact hsum _ _ _ _

end


end ArchonPhysics.CanonicalDecayAnnealedMainSectorSmallBallReduction
