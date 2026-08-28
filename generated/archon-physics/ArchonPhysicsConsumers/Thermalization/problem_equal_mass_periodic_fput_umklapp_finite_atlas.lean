import ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas

/-!
# Consumer endpoints for the explicit finite Umklapp atlas

The endpoints expose the principal-zone degeneracy classification, the
three monotonicity patches, the explicit fixed-sign local interval at every
nondegenerate resonant root, and the complete two-branch arcsine formula.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

noncomputable section

theorem equalMassPeriodicFPUT_umklappDegeneracyClassification_consumer
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi) :
    UmklappK₂DerivativeDegenerate k₀ k₁ k₂ ↔
      k₀ + k₁ = 2 * Real.pi ∨
        (2 * Real.pi < k₀ + k₁ ∧
          k₂ = (k₀ + k₁) / 2 - Real.pi) ∨
        (k₀ + k₁ < 2 * Real.pi ∧
          k₂ = (k₀ + k₁) / 2 + Real.pi) :=
  umklappK₂DerivativeDegenerate_iff_principal_ordered
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi

theorem equalMassPeriodicFPUT_umklappAtlasHasThreeBranches_consumer :
    Fintype.card UmklappAtlasBranch = 3 :=
  card_umklappAtlasBranch

theorem equalMassPeriodicFPUT_nondegeneratePointCoveredByAtlas_consumer
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi)
    (hnondegenerate : ¬ UmklappK₂DerivativeDegenerate k₀ k₁ k₂) :
    ∃ branch : UmklappAtlasBranch,
      k₂ ∈ umklappAtlasPatch branch k₀ k₁ :=
  exists_umklappAtlasBranch_of_nondegenerate
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi hnondegenerate

theorem equalMassPeriodicFPUT_resonantRootFixedSignLocalInterval_consumer
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    ∃ branch : UmklappAtlasBranch,
      k₂ ∈ Ioo (umklappAtlasLocalLeft branch k₀ k₁ k₂)
          (umklappAtlasLocalRight branch k₀ k₁ k₂) ∧
      ((∀ z ∈ Icc (umklappAtlasLocalLeft branch k₀ k₁ k₂)
              (umklappAtlasLocalRight branch k₀ k₁ k₂),
            0 < umklappK₂DerivativeFactor k₀ k₁ z) ∨
        (∀ z ∈ Icc (umklappAtlasLocalLeft branch k₀ k₁ k₂)
              (umklappAtlasLocalRight branch k₀ k₁ k₂),
            umklappK₂DerivativeFactor k₀ k₁ z < 0)) :=
  positiveDiscriminant_resonantRoot_has_explicit_fixedSign_interval
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi hdisc hresonant

theorem equalMassPeriodicFPUT_eachArcsineBranchIsResonant_consumer
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (branch : UmklappArcsineBranch) :
    umklappReducedFourWaveMismatch k₀ k₁
      (umklappArcsineRoot branch k₀ k₁) = 0 :=
  umklappArcsineRoot_resonant hdisc branch

theorem equalMassPeriodicFPUT_arcsineBranchesCoverPrincipalRoots_consumer
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    k₂ = umklappArcsineRoot .principal k₀ k₁ ∨
      k₂ = umklappArcsineRoot .outer k₀ k₁ :=
  resonantRoot_eq_principal_or_outer_arcsineRoot
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi hdisc hresonant

#print axioms equalMassPeriodicFPUT_umklappDegeneracyClassification_consumer
#print axioms equalMassPeriodicFPUT_umklappAtlasHasThreeBranches_consumer
#print axioms equalMassPeriodicFPUT_nondegeneratePointCoveredByAtlas_consumer
#print axioms equalMassPeriodicFPUT_resonantRootFixedSignLocalInterval_consumer
#print axioms equalMassPeriodicFPUT_eachArcsineBranchIsResonant_consumer
#print axioms equalMassPeriodicFPUT_arcsineBranchesCoverPrincipalRoots_consumer

end

end ArchonPhysicsConsumers.Thermalization
