import ArchonPhysics.CanonicalIIDCoerciveIteratedA2MeasurableSignedStaticWeight
import ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
import ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
import ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate

/-!
# Signed-frame grounded qualitative closure for an actual A2 channel

This file removes the legacy eigenvector-sign measurability premise from the
fixed-volume qualitative A2 closure.  The source weight is the globally
measurable first-positive-pivot signed-frame coefficient.  Thus measurable
radius coordinates, their deterministic finite bound, and absolute
continuity of the unweighted mismatch law construct the required weighted
`L1` Radon--Nikodym certificate.

The resulting externally scaled channel is negligible after multiplying by
`g^2` and integrating to `g^-2`.  This remains a fixed-volume qualitative
statement: no uniform-in-volume Fourier rate or microscopic-to-kinetic limit
is asserted.

For comparison with the legacy coefficient, the final section states only
the exact valid relation.  The signed coefficient agrees almost surely with
the legacy coefficient multiplied by its explicit two-tensor orientation
factor.  It is not identified with the unoriented legacy complex weight.
-/

namespace ArchonPhysics
namespace CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2MeasurableSignedStaticWeight
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeakCouplingQualitativeFourierKineticScale
open ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-! ## Radon--Nikodym certificate with no legacy sign-measurability premise -/

/-- Qualitative `L1` Fourier certificate for the measurable signed-frame A2
static weight. -/
abbrev ActualSignedIteratedA2StaticL1FourierCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :=
  WeightedMismatchL1FourierCertificate ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term)
    (actualSignedIteratedA2StaticWeightSample ensemble kappa radius
      observed term)

/-- Main signed-frame RN constructor.  Absolute continuity is required only
for the unweighted actual mismatch law; measurability and integrability of
the weight follow from the radius assumptions. -/
def actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (channel : IteratedA2MismatchChannel)
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
      radius observed term := by
  apply weightedMismatchL1FourierCertificate_of_map_absolutelyContinuous
    ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term)
    (actualSignedIteratedA2StaticWeightSample ensemble kappa radius
      observed term)
  · exact measurable_actualIteratedA2MismatchSample
      ensemble channel observed term
  · exact measurable_actualSignedIteratedA2StaticWeightSample
      ensemble kappa radius hradiusMeasurable observed term
  · exact integrable_actualSignedIteratedA2StaticWeightSample
      ensemble hN kappa R hR radius hradiusMeasurable hradiusBound
      observed term
  · simpa [physlibIteratedA2MismatchLaw] using hmismatchLaw

/-- The existing uniform global two-mass transversality theorem supplies the
unweighted absolute-continuity input for the signed RN constructor. -/
def actualSignedIteratedA2StaticL1Certificate_of_uniformGlobalTransversality
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (site1 site2 : Lattice.Site N) (hsite : site1 ≠ site2)
    (channel : IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradiusMeasurable : forall mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
          site1 site2 channel observed term)
    (hinjective : forall rest first, first ∈ massSupport -> Set.InjOn
      (fun second => physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
        site1 site2 channel observed term (first, second))
      massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      jacLower <= |physlibIteratedA2PairMismatchVerticalJacobian
        (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
        site1 site2 channel observed term (first, second)|) :
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble channel kappa
      radius observed term := by
  apply actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
    ensemble hN channel kappa R hR radius hradiusMeasurable hradiusBound
      observed term
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_uniform_globalTransversality
      ensemble site1 site2 hsite channel observed term hregular hinjective
        hjacLower hjac

/-! ## Signed external weak-coupling accumulation -/

/-- Instantaneous actual A2 channel with the measurable signed-frame static
weight. -/
def actualSignedIteratedA2StaticWeightedChannelExpectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (time : Real) : Complex :=
  actualIteratedA2WeightedChannelExpectation ensemble channel
    (actualSignedIteratedA2StaticWeightSample ensemble kappa radius
      observed term) observed term time

/-- External `g^2` accumulation of the signed-frame A2 channel on the
`g^-2` kinetic window. -/
def actualSignedIteratedA2StaticExternalWeakCouplingAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (g : Real) : Real :=
  ∫ time in 0..weakCouplingKineticTime g,
    ‖(((g ^ 2 : Real) : Complex) *
      actualSignedIteratedA2StaticWeightedChannelExpectation ensemble channel
        kappa radius observed term time)‖

theorem actualSignedIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (g : Real) :
    actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term g =
      weakCouplingKineticAccumulation
        (actualSignedIteratedA2StaticWeightedChannelExpectation ensemble
          channel kappa radius observed term) g := by
  unfold actualSignedIteratedA2StaticExternalWeakCouplingAccumulation
    weakCouplingKineticAccumulation
  rw [show (fun time =>
      ‖(((g ^ 2 : Real) : Complex) *
        actualSignedIteratedA2StaticWeightedChannelExpectation ensemble channel
          kappa radius observed term time)‖) =
      (fun time => g ^ 2 *
        ‖actualSignedIteratedA2StaticWeightedChannelExpectation ensemble channel
          kappa radius observed term time‖) by
    funext time
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg g)]]
  rw [intervalIntegral.integral_const_mul]

/-- An `L1` certificate closes the signed fixed-volume kinetic-window
accumulation qualitatively. -/
theorem tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualSignedIteratedA2StaticL1FourierCertificate
      ensemble channel kappa radius observed term) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [funext fun g =>
    actualSignedIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble channel kappa radius observed term g]
  exact certificate.tendsto_kineticAccumulation

/-- Fixed-volume signed A2 closure directly from mismatch-law absolute
continuity and measurable bounded radii. -/
theorem tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_mismatchLaw_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (channel : IteratedA2MismatchChannel)
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
  tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_certificate
    ensemble channel kappa radius observed term
      (actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
        ensemble hN channel kappa R hR radius hradiusMeasurable hradiusBound
          observed term hmismatchLaw)

/-- Fully grounded fixed-volume signed closure under the displayed uniform
global transversality data.  No legacy weight-measurability hypothesis
appears. -/
theorem tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_uniformGlobalTransversality
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (site1 site2 : Lattice.Site N) (hsite : site1 ≠ site2)
    (channel : IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradiusMeasurable : forall mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
          site1 site2 channel observed term)
    (hinjective : forall rest first, first ∈ massSupport -> Set.InjOn
      (fun second => physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
        site1 site2 channel observed term (first, second))
      massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : forall rest first second,
      first ∈ Ioo massLower massUpper ->
      second ∈ Ioo massLower massUpper ->
      jacLower <= |physlibIteratedA2PairMismatchVerticalJacobian
        (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
        site1 site2 channel observed term (first, second)|) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_certificate
    ensemble channel kappa radius observed term
      (actualSignedIteratedA2StaticL1Certificate_of_uniformGlobalTransversality
        ensemble hN site1 site2 hsite channel kappa R hR radius
          hradiusMeasurable hradiusBound observed term hregular hinjective
          hjacLower hjac)

/-! ## Exact, orientation-aware comparison with the legacy coefficient -/

/-- The two tensor-orientation factors which genuinely remain in the legacy
to signed change of coordinates. -/
def actualIteratedA2TwoTensorOrientationSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) : Real :=
  tensorOrientationProduct
      (ensemble.restrictPositiveMass (N := N) sample)
      (Fin.cons observed (iteratedQuadraticOuterModes term)) *
    tensorOrientationProduct
      (ensemble.restrictPositiveMass (N := N) sample)
      (Fin.cons (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1.1)

/-- The correctly oriented legacy weight.  No measurability is claimed for
this expression because it still exposes Mathlib's legacy basis orientation. -/
def actualOrientedLegacyIteratedA2StaticWeightSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) : Complex :=
  (actualIteratedA2TwoTensorOrientationSample ensemble observed term sample :
      Complex) *
    actualIteratedA2StaticWeightSample ensemble kappa radius observed term sample

theorem actualSignedIteratedA2StaticWeightSample_eq_orientedLegacy_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N) (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ∀ᵐ sample ∂ensemble.probability,
      actualSignedIteratedA2StaticWeightSample ensemble kappa radius
          observed term sample =
        actualOrientedLegacyIteratedA2StaticWeightSample ensemble kappa radius
          observed term sample := by
  filter_upwards
    [actualSignedIteratedA2StaticWeightSample_eq_orientationProducts_mul_ae
      ensemble hN kappa radius observed term] with sample hsample
  simpa [actualOrientedLegacyIteratedA2StaticWeightSample,
    actualIteratedA2TwoTensorOrientationSample] using hsample

/-- Consequently the signed instantaneous expectation equals the explicitly
oriented legacy expectation.  This does not identify it with the unoriented
legacy expectation. -/
theorem actualSignedIteratedA2StaticWeightedChannelExpectation_eq_orientedLegacy
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (time : Real) :
    actualSignedIteratedA2StaticWeightedChannelExpectation ensemble channel
        kappa radius observed term time =
      actualIteratedA2WeightedChannelExpectation ensemble channel
        (actualOrientedLegacyIteratedA2StaticWeightSample ensemble kappa radius
          observed term) observed term time := by
  unfold actualSignedIteratedA2StaticWeightedChannelExpectation
    actualIteratedA2WeightedChannelExpectation weightedMismatchExpectation
  apply integral_congr_ae
  filter_upwards
    [actualSignedIteratedA2StaticWeightSample_eq_orientedLegacy_ae
      ensemble hN kappa radius observed term] with sample hsample
  rw [hsample]

end

end CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
end ArchonPhysics
