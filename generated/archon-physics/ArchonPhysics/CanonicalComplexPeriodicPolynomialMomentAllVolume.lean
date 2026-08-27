import ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw

/-!
# Canonical complex periodic polynomial moments at every positive volume

The window theorem is naturally stated at volumes `W + (m + 1)`.  Removing
that finite prefix yields the same almost-sure limit for the single common
sequence of all positive volumes `N = n + 1`.  This alignment is needed when
many polynomial approximations, with different locality radii, approximate
one exact thermodynamic sequence.
-/

namespace ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentAllVolume

open ArchonPhysics
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

private theorem restrictMassFin_heq_of_volume_eq
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    {N M : Nat} (hNM : N = M) :
    HEq (ensemble.restrictMassFin (N := N) omega)
      (ensemble.restrictMassFin (N := M) omega) := by
  subst M
  rfl

/-- Complete periodic complex polynomial double moment per site for the first
`n + 1` mass coordinates. -/
def canonicalPositiveVolumeComplexPeriodicPolynomialMoment
    (ensemble : IIDMassPhaseEnsemble Omega)
    (cosineDegree sineDegree : Fin 3 -> Nat)
    (cosineCoefficient sineCoefficient : Fin 3 -> Nat -> Real)
    (n : Nat) (omega : Omega) : Complex :=
  complexPeriodicPolynomialDoubleMomentPerSite
    (ensemble.restrictMassFin (N := n + 1) omega)
    cosineDegree sineDegree cosineCoefficient sineCoefficient

/-- Fixed complex polynomial moments converge almost surely along the one
common sequence of every positive volume. -/
theorem canonicalPositiveVolumeComplexPeriodicPolynomialMoment_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 -> Nat)
    (cosineCoefficient sineCoefficient : Fin 3 -> Nat -> Real)
    (hcosine : forall r, cosineDegree r + 1 <= windowRadius)
    (hsine : forall r, sineDegree r + 1 <= windowRadius) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalPositiveVolumeComplexPeriodicPolynomialMoment ensemble
            cosineDegree sineDegree cosineCoefficient sineCoefficient
            n omega)
        atTop
        (𝓝 (complexWindowMean ensemble (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient))) := by
  filter_upwards
    [canonicalRestrictedComplexPeriodicPolynomialMoment_strongLaw_ae
      ensemble windowRadius cosineDegree sineDegree
        cosineCoefficient sineCoefficient hcosine hsine] with omega homega
  have hshift : Tendsto
      (fun n : Nat =>
        canonicalPositiveVolumeComplexPeriodicPolynomialMoment ensemble
          cosineDegree sineDegree cosineCoefficient sineCoefficient
          (n + (2 * windowRadius + 1)) omega)
      atTop
      (𝓝 (complexWindowMean ensemble (2 * windowRadius + 1)
        (complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient))) := by
    convert homega using 1
    funext n
    simp only [canonicalPositiveVolumeComplexPeriodicPolynomialMoment,
      canonicalRestrictedComplexPeriodicPolynomialMoment]
    have hvolume :
        n + (2 * windowRadius + 1) + 1 =
          2 * windowRadius + 1 + (n + 1) := by omega
    congr 1
    · apply proof_irrel_heq
    · exact restrictMassFin_heq_of_volume_eq ensemble omega hvolume
  exact (tendsto_add_atTop_iff_nat (2 * windowRadius + 1)).mp hshift

end


end ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentAllVolume
