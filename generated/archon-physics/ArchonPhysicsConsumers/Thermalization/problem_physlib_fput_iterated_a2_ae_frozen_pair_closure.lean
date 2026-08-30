import ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Consumer endpoint with the sharp almost-everywhere quantifier over the
frozen complementary mass environment. -/
theorem problem_physlib_fput_iterated_a2_ae_frozen_pair_signed_closure
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site N → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcertificate : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      Nonempty (IteratedA2PairAlgebraicRegularityCertificate
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term))
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_ae_frozenPair_algebraicCertificates
      ensemble hN site₁ site₂ hsite channel kappa R hR radius
        hradiusMeasurable hradiusBound observed term hcertificate havoid

#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure.physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure.physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_regularNoncritical
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure.physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_algebraicCertificates
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure.tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_ae_frozenPair_algebraicCertificates
#print axioms problem_physlib_fput_iterated_a2_ae_frozen_pair_signed_closure

end

end ArchonPhysicsConsumers.Thermalization
