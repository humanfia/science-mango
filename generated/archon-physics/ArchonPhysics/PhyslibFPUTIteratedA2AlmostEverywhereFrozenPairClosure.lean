import ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity

/-!
# Almost-everywhere frozen-environment closure for actual iterated-A2 mismatches

The exact selected-pair/complement reconstruction is an integral over the
frozen complementary environment.  Consequently, absolute continuity of the
selected-pair law is needed only for almost every frozen environment, rather
than at every (including zero-probability) environment.  This module records
that sharp quantifier and propagates it through the algebraic-certificate and
signed weak-coupling endpoints.

This remains a fixed-volume qualitative result.  It gives neither a uniform
in-volume density bound nor microscopic RPA/recollision control.
-/

namespace ArchonPhysics
namespace PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1
open ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- Almost-everywhere frozen-pair absolute continuity suffices for absolute
continuity of the complete finite-volume iid mismatch law. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hpair : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      Measure.map
          (physlibIteratedA2PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term)
          iidMassPairLaw ≪ (volume : Measure Real)) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  apply Measure.AbsolutelyContinuous.mk
  intro target htarget htargetZero
  rw [physlibIteratedA2MismatchLaw_apply_eq_lintegral_frozenPair
    ensemble site₁ site₂ hsite channel observed term htarget]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hpair] with rest hrest
  exact hrest htargetZero

/-- Almost-everywhere frozen environments with almost-everywhere regular and
noncritical pair charts imply full iid absolute continuity. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_regularNoncritical
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      ∀ᵐ pair ∂iidMassPairLaw,
        pair ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term ∧
          physlibIteratedA2PairMismatchVerticalJacobian
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term pair ≠ 0) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  apply physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair
    ensemble site₁ site₂ hsite channel observed term
  filter_upwards [hregular] with rest hrest
  exact
    physlibIteratedA2PairMismatchMap_absolutelyContinuous_volume_of_regularNoncritical_ae
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      hsite channel observed term hrest

/-- It is enough that a finite algebraic regularity certificate exists for
almost every frozen complementary environment. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_algebraicCertificates
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcertificate : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      Nonempty (IteratedA2PairAlgebraicRegularityCertificate
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term))
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  apply
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_regularNoncritical
      ensemble site₁ site₂ hsite channel observed term
  filter_upwards [hcertificate] with rest hrest
  rcases hrest with ⟨certificate⟩
  simpa [IteratedA2PairAlgebraicRegularityCertificate.regularSet] using
    certificate.regularSet_ae havoid

/-- Signed fixed-volume `g²`/`g⁻²` qualitative closure under algebraic
regularity certificates in almost every frozen complementary environment. -/
theorem tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_ae_frozenPair_algebraicCertificates
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
  apply
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_mismatchLaw_absolutelyContinuous
      ensemble hN channel kappa R hR radius hradiusMeasurable hradiusBound
        observed term
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_algebraicCertificates
      ensemble site₁ site₂ hsite channel observed term hcertificate havoid

end

end PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure
end ArchonPhysics
