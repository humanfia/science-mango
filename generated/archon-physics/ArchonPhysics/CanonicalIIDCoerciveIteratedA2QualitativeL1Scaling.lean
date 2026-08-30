import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
import ArchonPhysics.WeakCouplingQualitativeFourierKineticScale

/-!
# Actual A2 scaling from a qualitative L1 mismatch density

At fixed finite volume, an actual iterated-A2 channel needs only an `L1`
pushforward density to be negligible after external `g^2` scaling on the
`g^-2` window.  The proof uses Riemann--Lebesgue and continuous Cesaro
averaging; it supplies no quantitative rate uniform in volume.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeakCouplingQualitativeFourierKineticScale
open Filter MeasureTheory Set

noncomputable section

/-- Qualitative `L1` Fourier certificate for one actual weighted A2 channel. -/
abbrev ActualIteratedA2WeightedChannelL1FourierCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :=
  WeightedMismatchL1FourierCertificate ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term) weight

/-- Actual weighted-channel qualitative kinetic closure at fixed volume. -/
theorem tendsto_actualIteratedA2WeightedChannel_qualitativeL1
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelL1FourierCertificate
      ensemble channel weight observed term) :
    Tendsto
      (weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  certificate.tendsto_kineticAccumulation

/-- Fixed-`kappa` static specialization.  The external parameter `g` is not
part of the density certificate. -/
abbrev ActualIteratedA2StaticL1FourierCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :=
  ActualIteratedA2WeightedChannelL1FourierCertificate ensemble channel
    (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
    observed term

/-- Standard external-`g` actual accumulation from only an `L1` mismatch
density.  It is a fixed-volume statement and gives no chart-cost rate. -/
theorem tendsto_actualIteratedA2StaticExternalWeakCoupling_qualitativeL1
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2StaticL1FourierCertificate
      ensemble channel kappa radius observed term) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [funext fun g =>
    actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble channel kappa radius observed term g]
  exact certificate.tendsto_kineticAccumulation

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
