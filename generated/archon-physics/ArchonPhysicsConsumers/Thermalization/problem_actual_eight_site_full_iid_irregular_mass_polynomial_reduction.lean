import ArchonPhysics.ActualEightSiteFullIIDIrregularMassPolynomialReduction

/-!
# Consumer: algebraic reduction of the actual full-eight irregular mass

The mass-boundary, repeated-spectrum, and selected-mode positivity sectors
are discharged unconditionally.  The only remaining input is an explicit
nonzero inverse-mass elimination polynomial for the selected projector-minor
zero locus.  Given that certificate, the irregular mass vanishes and the
finite-level epsilon small-ball bound follows.
-/

open scoped ENNReal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
open ArchonPhysics.ActualEightSiteFullIIDEpsilonLevelSmallBall
open ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit
open ArchonPhysics.ActualEightSiteFullIIDIrregularMassPolynomialReduction
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory

noncomputable section

theorem problem_actual_eight_site_full_iid_irregular_mass_polynomial_reduction
    (certificate : FullEightSelectedProjectorMinorPolynomialCertificate) :
    fullEightSelectedJacobianIrregularMass = 0 ∧
    (∀ᵐ x ∂(finiteMassLaw 8),
      x ∈ fullEightSelectedJacobianRegularSet) ∧
    ∀ {epsilon : ENNReal}, 0 < epsilon →
      ∃ n : Nat, ∃ coefficient : ENNReal,
        coefficient ≠ (∞ : ENNReal) ∧
        fullEightSelectedJacobianBadMass n < epsilon ∧
        ∀ delta : Real, 0 ≤ delta →
          (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
              {point |
                |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
            coefficient * ENNReal.ofReal (2 * delta) + epsilon := by
  exact ⟨
    fullEightSelectedJacobianIrregularMass_eq_zero_of_polynomialCertificate
      certificate,
    fullEightSelectedJacobianRegularSet_ae_of_polynomialCertificate
      certificate,
    fun hepsilon =>
      exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper_of_polynomialCertificate
        certificate hepsilon⟩

end

end ArchonPhysicsConsumers.Thermalization
