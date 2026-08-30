import ArchonPhysics.CanonicalIIDCoerciveIteratedA2GroundedQualitativeKineticClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2GroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
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
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    tendsto_actualIteratedA2StaticExternalWeakCoupling_of_uniformGlobalTransversality
      ensemble site₁ site₂ hsite channel kappa R hR radius hradius observed
        term hweight hregular hinjective hjacLower hjac

#print axioms actualIteratedA2StaticL1Certificate_of_uniformGlobalTransversality
#print axioms tendsto_actualIteratedA2StaticExternalWeakCoupling_of_uniformGlobalTransversality

end

end ArchonPhysicsConsumers.Thermalization
