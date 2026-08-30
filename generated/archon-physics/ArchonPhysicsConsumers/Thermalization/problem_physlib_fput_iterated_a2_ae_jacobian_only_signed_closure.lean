import ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereJacobianOnlySignedClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereJacobianOnlySignedClosure
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Consumer endpoint with only almost-everywhere frozen-environment
Jacobian-eliminant obligations. -/
theorem problem_physlib_fput_iterated_a2_ae_jacobian_only_signed_closure
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
    (jacobianPolynomial : FiniteMassVector
        (finiteVolumeMassPairComplement site₁ site₂) →
      MvPolynomial (Fin 2) Real)
    (hjacobianPolynomial : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      jacobianPolynomial rest ≠ 0)
    (hjacobianZero : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      ∀ pair,
        pair ∈ interior iidMassPairSupport →
        SimpleOrderedSpectrum
            (twoSiteHarmonicHermitian
              (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
              site₁ site₂ pair) →
        physlibIteratedA2PairMismatchVerticalJacobian
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term pair = 0 →
        MvPolynomial.eval (iidInverseMassPairCoordinates pair)
            (jacobianPolynomial rest) = 0)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    tendsto_actualSignedIteratedA2WeakCoupling_of_ae_frozenPair_jacobianCertificates
      ensemble hN site₁ site₂ hsite channel kappa R hR radius
        hradiusMeasurable hradiusBound observed term jacobianPolynomial
        hjacobianPolynomial hjacobianZero havoid

#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereJacobianOnlySignedClosure.tendsto_actualSignedIteratedA2WeakCoupling_of_ae_frozenPair_jacobianCertificates
#print axioms problem_physlib_fput_iterated_a2_ae_jacobian_only_signed_closure

end

end ArchonPhysicsConsumers.Thermalization
