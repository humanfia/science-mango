import ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Consumer-facing fixed-volume endpoint: finite algebraic nonvanishing in
every frozen pair environment, plus acoustic avoidance, yields the signed
`g^2`/`g^-2` qualitative closure without global fibre injectivity or a
uniform Jacobian lower bound. -/
theorem problem_physlib_fput_iterated_a2_countable_local_signed_closure
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
    (certificate : ∀ rest : FiniteMassVector
        (finiteVolumeMassPairComplement site₁ site₂),
      IteratedA2PairAlgebraicRegularityCertificate
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_frozenPair_algebraicCertificates
      ensemble hN site₁ site₂ hsite channel kappa R hR radius
        hradiusMeasurable hradiusBound observed term certificate havoid

end

end ArchonPhysicsConsumers.Thermalization
