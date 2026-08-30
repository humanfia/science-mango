import ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit

/-!
# Consumer: exact limit of the full-eight compact good-level bad mass

The compact levels exhaust precisely the physical regular locus.  Their
exceptional masses converge to, and have infimum equal to, the actual iid
mass of the irregular locus.  Vanishing is therefore equivalent to a
separate almost-everywhere regularity theorem.
-/

open scoped ENNReal Topology

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
open ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit
open ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set

noncomputable section

theorem problem_actual_eight_site_full_iid_good_level_limit_audit :
    ((⋃ n, fullEightSelectedJacobianGoodLevel n) =
        fullEightMassSupportCube ∩ fullEightSelectedJacobianRegularSet) ∧
    Tendsto fullEightSelectedJacobianBadMass atTop
      (nhds fullEightSelectedJacobianIrregularMass) ∧
    ((⨅ n, fullEightSelectedJacobianBadMass n) =
      fullEightSelectedJacobianIrregularMass) ∧
    (Tendsto fullEightSelectedJacobianBadMass atTop (nhds 0) ↔
      ∀ᵐ x ∂(finiteMassLaw 8),
        x ∈ fullEightSelectedJacobianRegularSet) := by
  exact ⟨
    iUnion_fullEightSelectedJacobianGoodLevel_eq_support_inter_regular,
    tendsto_fullEightSelectedJacobianBadMass_irregularMass,
    iInf_fullEightSelectedJacobianBadMass_eq_irregularMass,
    tendsto_fullEightSelectedJacobianBadMass_zero_iff_regular_ae⟩

end

end ArchonPhysicsConsumers.Thermalization
