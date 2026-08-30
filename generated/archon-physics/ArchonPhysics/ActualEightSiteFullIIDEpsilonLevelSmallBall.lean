import ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit

/-!
# Finite epsilon-level full-eight iid small-ball reduction

The compact quantitative good levels have finite-atlas linear small-ball
bounds, while their exceptional masses converge to the exact mass of the
irregular locus.  Consequently, for every positive `ENNReal` tolerance one
can choose one finite level and one finite coefficient whose bound loses only
the irregular mass plus that tolerance.

The irregular mass is retained explicitly.  It disappears only in the two
conditional corollaries, where either its vanishing or equivalent
almost-everywhere regularity is supplied as a hypothesis.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.ActualEightSiteFullIIDEpsilonLevelSmallBall

open ArchonPhysics
open ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
open ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit
open ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set

noncomputable section

/-- At every positive tolerance there is one finite compact level and one
finite atlas coefficient giving a uniform-in-`delta` small-ball bound with
the exact irregular mass and the requested tolerance as the only residual.
-/
theorem exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, ∃ coefficient : ENNReal,
      coefficient ≠ (∞ : ENNReal) ∧
      fullEightSelectedJacobianBadMass n <
        fullEightSelectedJacobianIrregularMass + epsilon ∧
      ∀ delta : Real, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
            {point |
              |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient * ENNReal.ofReal (2 * delta) +
            fullEightSelectedJacobianIrregularMass + epsilon := by
  have hirregularFinite :
      fullEightSelectedJacobianIrregularMass ≠ (∞ : ENNReal) := by
    unfold fullEightSelectedJacobianIrregularMass
    exact measure_ne_top _ _
  have hirregularLt :
      fullEightSelectedJacobianIrregularMass <
        fullEightSelectedJacobianIrregularMass + epsilon :=
    ENNReal.lt_add_right hirregularFinite (ne_of_gt hepsilon)
  have heventually :
      ∀ᶠ n : Nat in atTop,
        fullEightSelectedJacobianBadMass n <
          fullEightSelectedJacobianIrregularMass + epsilon :=
    (tendsto_order.mp
      tendsto_fullEightSelectedJacobianBadMass_irregularMass).2
        _ hirregularLt
  obtain ⟨n, hn⟩ := eventually_atTop.mp heventually
  obtain ⟨coefficient, hcoefficientFinite, hlevel⟩ :=
    exists_finiteCoefficient_actualEightSite_fullIID_goodLevel_smallBallUpper n
  refine ⟨n, coefficient, hcoefficientFinite, hn n le_rfl, ?_⟩
  intro delta hdelta
  calc
    (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
          {point |
            |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
        coefficient * ENNReal.ofReal (2 * delta) +
          fullEightSelectedJacobianBadMass n :=
      hlevel delta hdelta
    _ ≤ coefficient * ENNReal.ofReal (2 * delta) +
          (fullEightSelectedJacobianIrregularMass + epsilon) :=
      add_le_add le_rfl (le_of_lt (hn n le_rfl))
    _ = coefficient * ENNReal.ofReal (2 * delta) +
          fullEightSelectedJacobianIrregularMass + epsilon := by
      rw [add_assoc]

/-- If the irregular locus has zero iid mass, the finite-level residual can
be made smaller than every prescribed positive tolerance. -/
theorem exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper_of_irregularMass_eq_zero
    (hirregular : fullEightSelectedJacobianIrregularMass = 0)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, ∃ coefficient : ENNReal,
      coefficient ≠ (∞ : ENNReal) ∧
      fullEightSelectedJacobianBadMass n < epsilon ∧
      ∀ delta : Real, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
            {point |
              |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient * ENNReal.ofReal (2 * delta) + epsilon := by
  obtain ⟨n, coefficient, hfinite, hbad, hbound⟩ :=
    exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper
      hepsilon
  refine ⟨n, coefficient, hfinite, ?_, ?_⟩
  · simpa [hirregular] using hbad
  · intro delta hdelta
    simpa [hirregular, add_assoc] using hbound delta hdelta

/-- Equivalent conditional version phrased by actual almost-everywhere
regularity of the full-eight iid mass law. -/
theorem exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper_of_regular_ae
    (hregular :
      ∀ᵐ x ∂(finiteMassLaw 8),
        x ∈ fullEightSelectedJacobianRegularSet)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, ∃ coefficient : ENNReal,
      coefficient ≠ (∞ : ENNReal) ∧
      fullEightSelectedJacobianBadMass n < epsilon ∧
      ∀ delta : Real, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
            {point |
              |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient * ENNReal.ofReal (2 * delta) + epsilon := by
  apply
    exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper_of_irregularMass_eq_zero
  · exact
      fullEightSelectedJacobianIrregularMass_eq_zero_iff_regular_ae.mpr
        hregular
  · exact hepsilon

end

end ArchonPhysics.ActualEightSiteFullIIDEpsilonLevelSmallBall
