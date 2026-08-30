import ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing

/-!
# Almost-everywhere Jacobian-only actual signed iterated-A2 closure

The full iid Fubini reconstruction ignores null sets of frozen complementary
mass environments.  Combining that fact with unconditional nonvanishing of
the two-site spectrum resultant leaves only a channel-specific Jacobian
eliminant, and its two algebraic obligations are required only almost
everywhere in the frozen environment.

The result is fixed-volume and qualitative.  It does not provide a
volume-uniform rate or the microscopic RPA/recollision estimates.
-/

namespace ArchonPhysics
namespace PhyslibFPUTIteratedA2AlmostEverywhereJacobianOnlySignedClosure

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Signed fixed-volume closure from a Jacobian eliminant which is nonzero and
valid for almost every frozen complementary mass environment. -/
theorem tendsto_actualSignedIteratedA2WeakCoupling_of_ae_frozenPair_jacobianCertificates
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
  apply
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_ae_frozenPair_algebraicCertificates
      ensemble hN site₁ site₂ hsite channel kappa R hR radius
        hradiusMeasurable hradiusBound observed term
  · filter_upwards [hjacobianPolynomial, hjacobianZero] with rest hpoly hzero
    exact ⟨algebraicRegularityCertificateOfJacobian
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      channel observed term hsite (jacobianPolynomial rest) hpoly hzero⟩
  · exact havoid

end

end PhyslibFPUTIteratedA2AlmostEverywhereJacobianOnlySignedClosure
end ArchonPhysics
