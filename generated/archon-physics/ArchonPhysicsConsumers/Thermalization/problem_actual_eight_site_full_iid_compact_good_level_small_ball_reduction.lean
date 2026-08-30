import ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction

/-!
# Consumer: compact good-level full-eight iid small-ball reduction

This consumer records the exact global statement available from the actual
full-eight finite atlas: a finite linear coefficient on every compact
quantitative regular level, plus the unreduced iid mass of its complement.
-/

open scoped ENNReal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.RandomEnsemble
open MeasureTheory

noncomputable section

theorem problem_actual_eight_site_full_iid_compact_good_level_small_ball_reduction
    (n : Nat) :
    ∃ coefficient : ENNReal, coefficient ≠ (∞ : ENNReal) ∧
      ∀ delta : Real, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
            {point |
              |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient * ENNReal.ofReal (2 * delta) +
            fullEightSelectedJacobianBadMass n := by
  exact
    exists_finiteCoefficient_actualEightSite_fullIID_goodLevel_smallBallUpper
      n

end

end ArchonPhysicsConsumers.Thermalization
