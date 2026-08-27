import ArchonPhysics.DeterministicPeriodicKernelWindowReindex

/-!
# Consumer: deterministic periodic-kernel/window reindex

This consumer exposes the assumption-free finite periodic double-moment
identity used before the iid window strong law.  It deliberately makes no
thermodynamic or continuous-kernel claim.
-/

namespace ArchonPhysicsConsumers.Thermalization.DeterministicPeriodicKernelWindowReindex

open ArchonPhysics
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.DeterministicPeriodicKernelWindowReindex
open ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
open ArchonPhysics.PeriodicPolynomialWindowReindex

noncomputable section

theorem finitePeriodicDoubleMoment_eq_centeredWindowAverage
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    let centerBig :=
      Fin.castAdd m (centeredWindowIndex windowRadius)
    complexPeriodicPolynomialDoubleMomentPerSite x
        cosineDegree sineDegree cosineCoefficient sineCoefficient =
      (∑ target : Fin ((2 * windowRadius + 1) + m),
        complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient
          (translatedMassWindow x
            (finCenteringShift centerBig target))) /
        (((2 * windowRadius + 1) + m : Nat) : Real) := by
  exact
    complexPeriodicPolynomialDoubleMomentPerSite_eq_centeredWindowAverage
      x cosineDegree sineDegree cosineCoefficient sineCoefficient
        hcosine hsine

#print axioms complexPeriodicPolynomialDoubleMomentPerSite_eq_centeredWindowAverage
#print axioms complexWeightedInteractionPolynomialMomentPerSite_eq_centeredWindowAverage
#print axioms finitePeriodicDoubleMoment_eq_centeredWindowAverage

end


end ArchonPhysicsConsumers.Thermalization.DeterministicPeriodicKernelWindowReindex
