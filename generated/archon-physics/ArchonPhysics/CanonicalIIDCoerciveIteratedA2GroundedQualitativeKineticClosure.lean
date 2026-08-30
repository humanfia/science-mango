import ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
import ArchonPhysics.CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability
import ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
import ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate

/-!
# Grounded fixed-volume qualitative kinetic closure for an actual A2 channel

This module composes four independently checked layers:

1. actual ordered-spectrum strict differentiability of an iterated-`A2`
   mismatch in two selected iid mass coordinates;
2. a displayed global one-fibre transversality certificate, uniform over the
   frozen complementary masses, giving absolute continuity of the actual
   mismatch law;
3. the explicit finite-volume bound
   `norm staticWeight <= 4 * |kappa|^2 * R^3`, giving integrability of a
   measurable bounded-radius physical weight; and
4. the Radon--Nikodym construction of an `L1` complex mismatch density,
   followed by Riemann--Lebesgue and continuous Cesaro averaging on the
   `g^-2` window.

Thus the final `L1` density is constructed rather than supplied as a premise.
The remaining hypotheses are visible model statements: global fibre
injectivity and a positive Jacobian lower bound at this fixed volume, plus
measurability of the legacy signed-eigenvector static weight.  Charge-matched
total return channels cannot satisfy the injectivity premise and belong in
the feedback block.  No uniform-in-volume rate, RPA, recollision estimate, or
microscopic-to-kinetic limit is asserted.
-/

namespace ArchonPhysics
namespace CanonicalIIDCoerciveIteratedA2GroundedQualitativeKineticClosure

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The actual fixed-volume `L1` Fourier certificate constructed from
physical transversality and bounded measurable static-weight data. -/
def actualIteratedA2StaticL1Certificate_of_uniformGlobalTransversality
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hweight : Measurable
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term))
    (hregular : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term)
    (hinjective : forall rest first, first ∈ massSupport -> InjOn
      (fun second => physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second))
      massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      jacLower <= |physlibIteratedA2PairMismatchVerticalJacobian
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second)|) :
    ActualIteratedA2StaticL1FourierCertificate ensemble channel kappa radius
      observed term := by
  apply weightedMismatchL1FourierCertificate_of_map_absolutelyContinuous
    ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term)
    (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
    (measurable_actualIteratedA2MismatchSample
      ensemble channel observed term)
    hweight
    (integrable_actualIteratedA2StaticWeightSample ensemble kappa R hR radius
      hradius observed term hweight)
  simpa [physlibIteratedA2MismatchLaw] using
    (physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_uniform_globalTransversality
      ensemble site₁ site₂ hsite channel observed term hregular hinjective
        hjacLower hjac)

/-- Grounded fixed-volume qualitative weak-coupling conclusion.  The base
FPUT coefficient `kappa` is fixed and the extracted second-Picard channel is
scaled by the external `g^2` before integration to time `g^-2`. -/
theorem tendsto_actualIteratedA2StaticExternalWeakCoupling_of_uniformGlobalTransversality
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hweight : Measurable
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term))
    (hregular : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term)
    (hinjective : forall rest first, first ∈ massSupport -> InjOn
      (fun second => physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second))
      massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      jacLower <= |physlibIteratedA2PairMismatchVerticalJacobian
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second)|) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualIteratedA2StaticExternalWeakCoupling_qualitativeL1
    ensemble channel kappa radius observed term
      (actualIteratedA2StaticL1Certificate_of_uniformGlobalTransversality
        ensemble site₁ site₂ hsite channel kappa R hR radius hradius observed
          term hweight hregular hinjective hjacLower hjac)

end

end CanonicalIIDCoerciveIteratedA2GroundedQualitativeKineticClosure
end ArchonPhysics
