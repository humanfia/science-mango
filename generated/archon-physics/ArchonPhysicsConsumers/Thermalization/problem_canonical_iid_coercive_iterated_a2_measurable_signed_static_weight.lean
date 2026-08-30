import ArchonPhysics.CanonicalIIDCoerciveIteratedA2MeasurableSignedStaticWeight

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2MeasurableSignedStaticWeight
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Consumer-facing audit: measurable radii suffice for the canonical signed
A2 static weight, without assuming measurability of Mathlib's legacy
eigenvector-basis signs. -/
example (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall mode, Measurable fun sample => radius sample mode)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Measurable
      (actualSignedIteratedA2StaticWeightSample ensemble kappa radius
        observed term) :=
  measurable_actualSignedIteratedA2StaticWeightSample
    ensemble kappa radius hradius observed term

/-- Consumer-facing audit: the signed replacement and legacy coefficient
have identical norms almost surely under the iid continuous-mass law. -/
example (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N) (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ∀ᵐ aeSample ∂ensemble.probability,
      ‖actualSignedIteratedA2StaticWeightSample ensemble kappa radius
          observed term aeSample‖ =
        ‖actualIteratedA2StaticWeightSample ensemble kappa radius
          observed term aeSample‖ :=
  norm_actualSignedIteratedA2StaticWeightSample_eq_ae
    ensemble hN kappa radius observed term

#print axioms measurable_actualSignedIteratedA2StaticWeightSample
#print axioms signedIteratedQuadraticSecondPicardStaticCoefficient_eq_orientationProducts_mul
#print axioms integrable_actualSignedIteratedA2StaticWeightSample

end

end ArchonPhysicsConsumers.Thermalization
