import ArchonPhysics.ActualEightSiteFullIIDEpsilonLevelSmallBall

/-!
# Consumer: finite epsilon-level full-eight iid small-ball bound

For every positive tolerance, a finite compact good level supplies a finite
linear coefficient and leaves precisely the actual irregular mass plus that
tolerance.  Under the separate almost-everywhere regularity condition, only
the tolerance remains.
-/

open scoped ENNReal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
open ArchonPhysics.ActualEightSiteFullIIDEpsilonLevelSmallBall
open ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit
open ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory

noncomputable section

theorem problem_actual_eight_site_full_iid_epsilon_level_small_ball
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    (∃ n : Nat, ∃ coefficient : ENNReal,
      coefficient ≠ (∞ : ENNReal) ∧
      fullEightSelectedJacobianBadMass n <
        fullEightSelectedJacobianIrregularMass + epsilon ∧
      ∀ delta : Real, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
            {point |
              |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient * ENNReal.ofReal (2 * delta) +
            fullEightSelectedJacobianIrregularMass + epsilon) ∧
    ((∀ᵐ x ∂(finiteMassLaw 8),
        x ∈ fullEightSelectedJacobianRegularSet) →
      ∃ n : Nat, ∃ coefficient : ENNReal,
        coefficient ≠ (∞ : ENNReal) ∧
        fullEightSelectedJacobianBadMass n < epsilon ∧
        ∀ delta : Real, 0 ≤ delta →
          (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
              {point |
                |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
            coefficient * ENNReal.ofReal (2 * delta) + epsilon) := by
  refine ⟨
    exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper
      hepsilon,
    ?_⟩
  intro hregular
  exact
    exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper_of_regular_ae
      hregular hepsilon

end

end ArchonPhysicsConsumers.Thermalization
