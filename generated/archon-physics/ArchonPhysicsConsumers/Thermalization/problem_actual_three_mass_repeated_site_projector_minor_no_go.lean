import ArchonPhysics.ActualThreeMassRepeatedSiteProjectorMinorNoGo

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.ActualThreeMassRepeatedSiteProjectorMinorNoGo
open Set

noncomputable section

/-- The explicit joint mass--spectral numerator itself collapses, so a later
resultant cannot supply the missing nonzero witness in this sector. -/
theorem problem_actualThreeMass_repeatedSite_adjugateNumerator_eq_zero
    {N : Nat} [NeZero N] (site₀ site₁ site₂ : Lattice.Site N)
    (hsite : ¬ Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂)) :
    actualThreeMassAdjugateSpectralPolynomial site₀ site₁ site₂ = 0 :=
  actualThreeMassAdjugateSpectralPolynomial_eq_zero_of_not_injective
    site₀ site₁ site₂ hsite


/-- Consumer-facing exact obstruction: without injective selected sites the
actual collision-weighted projector-minor law is entirely supported at zero. -/
theorem problem_actualThreeMass_repeatedSite_projectorMinorLaw_concentratedAtZero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (hsite : ¬ Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂)) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ ({0} : Set Real) =
      actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ univ :=
  actualThreeMassCollisionWeightedProjectorMinorDistribution_singleton_zero_eq_univ_of_not_injective
    fixed site₀ site₁ site₂ hsite

#print axioms problem_actualThreeMass_repeatedSite_projectorMinorLaw_concentratedAtZero
#print axioms problem_actualThreeMass_repeatedSite_adjugateNumerator_eq_zero

end

end ArchonPhysicsConsumers.Thermalization
