import ArchonPhysics.CanonicalDecayAnnealedSectorSmallBallAggregation

/-!
# Annealed parent--child decay-sector small-ball bounds

The two repeated parent--child sectors already satisfy a realization-wise
quadratic estimate.  This module passes that estimate through the genuine
canonical-law barycenter; no quenched conclusion is inferred from an
annealed premise.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalDecayAnnealedParentChildSmallBall

open ArchonPhysics
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open MeasureTheory Set

noncomputable section

/-- The first parent--child sector keeps its uniform quadratic small-ball
bound after averaging over the canonical iid law. -/
theorem canonicalDecaySectorAnnealed_parentChildOne_smallBall
    (n : Nat) {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst => ParentChildOneRepeated) n : Measure Real)
        (absoluteMismatchSublevel delta)).toReal ≤
      (5 / 8 : Real) * delta ^ 2 := by
  have hconstant : 0 ≤ (5 / 8 : Real) * delta ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg delta)
  have hpointwise : ∀ omega,
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
          canonicalIIDMassPhaseEnsemble
          (fun {_N} _inst => ParentChildOneRepeated) n omega : Measure Real)
          (absoluteMismatchSublevel delta) ≤
        ENNReal.ofReal ((5 / 8 : Real) * delta ^ 2) := by
    intro omega
    have hreal :
        ((canonicalDecaySectorPerSiteMismatchFiniteMeasure
            canonicalIIDMassPhaseEnsemble
            (fun {_N} _inst => ParentChildOneRepeated) n omega : Measure Real)
            (absoluteMismatchSublevel delta)).toReal ≤
          (5 / 8 : Real) * delta ^ 2 := by
      simpa only [canonicalDecaySector_parentChildOne_eq_iid_tail] using
        iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure_smallBall
          canonicalIIDMassPhaseEnsemble omega (n + 1) hdelta hdelta1
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hconstant]
    exact hreal
  have hbarycenter :
      (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ParentChildOneRepeated) n : Measure Real)
          (absoluteMismatchSublevel delta) ≤
        ENNReal.ofReal ((5 / 8 : Real) * delta ^ 2) := by
    rw [canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
      (fun {_N} _inst => ParentChildOneRepeated) n
      (measurableSet_absoluteMismatchSublevel delta)]
    calc
      _ ≤ ∫⁻ _omega,
          ENNReal.ofReal ((5 / 8 : Real) * delta ^ 2)
          ∂ RandomEnsemble.canonicalLaw := lintegral_mono hpointwise
      _ = _ := by simp
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    ENNReal.ofReal_ne_top).mpr hbarycenter
  simpa only [ENNReal.toReal_ofReal hconstant] using hreal

/-- The second parent--child sector has the same annealed quadratic bound. -/
theorem canonicalDecaySectorAnnealed_parentChildTwo_smallBall
    (n : Nat) {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst => ParentChildTwoRepeated) n : Measure Real)
        (absoluteMismatchSublevel delta)).toReal ≤
      (5 / 8 : Real) * delta ^ 2 := by
  have hconstant : 0 ≤ (5 / 8 : Real) * delta ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg delta)
  have hpointwise : ∀ omega,
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
          canonicalIIDMassPhaseEnsemble
          (fun {_N} _inst => ParentChildTwoRepeated) n omega : Measure Real)
          (absoluteMismatchSublevel delta) ≤
        ENNReal.ofReal ((5 / 8 : Real) * delta ^ 2) := by
    intro omega
    have hreal :
        ((canonicalDecaySectorPerSiteMismatchFiniteMeasure
            canonicalIIDMassPhaseEnsemble
            (fun {_N} _inst => ParentChildTwoRepeated) n omega : Measure Real)
            (absoluteMismatchSublevel delta)).toReal ≤
          (5 / 8 : Real) * delta ^ 2 := by
      simpa only [canonicalDecaySector_parentChildTwo_eq_iid_tail] using
        iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure_smallBall
          canonicalIIDMassPhaseEnsemble omega (n + 1) hdelta hdelta1
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hconstant]
    exact hreal
  have hbarycenter :
      (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
          (fun {_N} _inst => ParentChildTwoRepeated) n : Measure Real)
          (absoluteMismatchSublevel delta) ≤
        ENNReal.ofReal ((5 / 8 : Real) * delta ^ 2) := by
    rw [canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
      (fun {_N} _inst => ParentChildTwoRepeated) n
      (measurableSet_absoluteMismatchSublevel delta)]
    calc
      _ ≤ ∫⁻ _omega,
          ENNReal.ofReal ((5 / 8 : Real) * delta ^ 2)
          ∂ RandomEnsemble.canonicalLaw := lintegral_mono hpointwise
      _ = _ := by simp
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    ENNReal.ofReal_ne_top).mpr hbarycenter
  simpa only [ENNReal.toReal_ofReal hconstant] using hreal

end


end ArchonPhysics.CanonicalDecayAnnealedParentChildSmallBall
