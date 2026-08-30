import ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Consumer-facing certificate construction with no legacy signed-basis
measurability premise. -/
example (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (channel : CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay.IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradiusMeasurable : forall mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hmismatchLaw :
      physlibIteratedA2MismatchLaw ensemble channel observed term ≪ volume) :
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble channel kappa
      radius observed term :=
  actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
    ensemble hN channel kappa R hR radius hradiusMeasurable hradiusBound
      observed term hmismatchLaw

/-- Consumer-facing fixed-volume `g^2`/`g^-2` qualitative conclusion. -/
example (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (channel : CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay.IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradiusMeasurable : forall mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hmismatchLaw :
      physlibIteratedA2MismatchLaw ensemble channel observed term ≪ volume) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_mismatchLaw_absolutelyContinuous
    ensemble hN channel kappa R hR radius hradiusMeasurable hradiusBound
      observed term hmismatchLaw

#print axioms actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
#print axioms
  tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_mismatchLaw_absolutelyContinuous
#print axioms actualSignedIteratedA2StaticWeightedChannelExpectation_eq_orientedLegacy

end

end ArchonPhysicsConsumers.Thermalization
