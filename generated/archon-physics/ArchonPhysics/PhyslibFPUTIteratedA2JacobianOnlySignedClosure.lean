import ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing

/-!
# Jacobian-only actual signed iterated-A2 closure

The countable-local absolute-continuity endpoint asks for a complete
algebraic regularity certificate in every frozen complementary environment.
The spectrum-nonvanishing theorem constructs the spectrum half of that
certificate for every positive background and every pair of distinct varied
sites.  Consequently the only channel-specific algebraic input left at this
endpoint is a nonzero Jacobian polynomial whose zero set contains the genuine
vertical-Jacobian zero set on the regular supported chart.

This is a fixed-volume qualitative signed weak-coupling theorem.  It assumes
neither spectrum-polynomial nonvanishing, global fibre injectivity, a uniform
Jacobian lower bound, nor legacy eigenvector-sign/weight measurability.
-/

namespace ArchonPhysics
namespace PhyslibFPUTIteratedA2JacobianOnlySignedClosure

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter Set
open scoped Topology

noncomputable section

/-- Actual signed fixed-volume iterated-`A2` weak-coupling closure from only
the channel-specific Jacobian polynomial in every frozen pair environment.

The unconditional positive-path specialization supplies the omitted
spectrum-polynomial nonvanishing field of the local algebraic certificate.
All remaining hypotheses are visible in this statement. -/
theorem tendsto_actualSignedIteratedA2WeakCoupling_of_frozenPair_jacobianCertificates
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
    (hjacobianPolynomial : ∀ rest, jacobianPolynomial rest ≠ 0)
    (hjacobianZero : ∀ rest pair,
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
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_frozenPair_algebraicCertificates
      ensemble hN site₁ site₂ hsite channel kappa R hR radius
        hradiusMeasurable hradiusBound observed term
  · intro rest
    exact
      algebraicRegularityCertificateOfJacobian
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        channel observed term hsite (jacobianPolynomial rest)
          (hjacobianPolynomial rest) (hjacobianZero rest)
  · exact havoid

end

end PhyslibFPUTIteratedA2JacobianOnlySignedClosure
end ArchonPhysics
