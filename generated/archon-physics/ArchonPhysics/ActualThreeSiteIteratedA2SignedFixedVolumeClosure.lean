import ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate
import ArchonPhysics.PhyslibFPUTIteratedA2JacobianOnlySignedClosure

/-!
# End-to-end signed fixed-volume A2 closure on three sites

This module specializes the countable-local absolute-continuity and signed
Radon--Nikodym pipeline to the concrete ordinary outer history on the actual
three-site random-mass chain.  The selected mismatch is exactly the negative
second positive ordered frequency.

On every frozen value of the third mass, the explicit polynomial from
`ActualThreeSiteIteratedA2OuterJacobianFrozenFiber` supplies the only
channel-specific algebraic input.  The general positive-path theorem supplies
spectral nonvanishing, countable local inverse-function patches supply
absolute continuity, and the measurable signed frame supplies the weighted
`L1` certificate.

Consequently the final theorem has no external simple-spectrum, Jacobian,
global injectivity, uniform transversality, or legacy eigenvector-sign
premise.  The concrete channel also proves its own acoustic avoidance.  Only
the genuinely analytic radius measurability and boundedness data remain.
The conclusion is fixed-volume and qualitative; it is not uniform in volume.
-/

namespace ArchonPhysics
namespace ActualThreeSiteIteratedA2SignedFixedVolumeClosure

open ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity
open ArchonPhysics.PhyslibFPUTIteratedA2JacobianOnlySignedClosure
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-! ## The concrete random mismatch and its law -/

/-- The actual random mismatch selected by the concrete ordinary outer
history is pointwise the negative second positive frequency. -/
@[simp]
theorem actualThreeSiteSingleFrequencyOuterMismatchSample_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (sample : Omega) :
    actualIteratedA2MismatchSample ensemble .outer
        firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm
        sample =
      -modeFrequency (ensemble.restrictPositiveMass (N := 3) sample)
        secondPositivePhysicalModeThree := by
  exact threeSiteSingleFrequency_outerMismatch_eq
    (ensemble.restrictPositiveMass (N := 3) sample)

/-- The full three-mass iid law of the concrete outer mismatch is absolutely
continuous with respect to Lebesgue measure.  The arbitrary frozen-third-mass
eliminant is instantiated separately on every complementary environment;
there is no spectrum or transversality premise in this statement. -/
theorem actualThreeSiteSingleFrequencyOuterMismatchLaw_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) :
    physlibIteratedA2MismatchLaw ensemble .outer
        firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm ≪
      (volume : Measure Real) := by
  apply
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair_algebraicCertificates
      ensemble (0 : Lattice.Site 3) (1 : Lattice.Site 3) (by decide)
        .outer firstPositivePhysicalModeThree
        threeSiteSingleFrequencyOuterTerm
  · intro rest
    exact frozenFiberThreeSiteOuterAlgebraicRegularityCertificate
      (finitePairEnvironmentPositiveMassConfig
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest)
  · exact threeSiteSingleFrequencyOuter_avoidsAcoustic

/-- Equivalently, the negative second positive ordered frequency itself has
an absolutely continuous law under the complete three-mass iid ensemble. -/
theorem map_neg_secondPositiveModeFrequency_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) :
    Measure.map
        (fun sample =>
          -modeFrequency (ensemble.restrictPositiveMass (N := 3) sample)
            secondPositivePhysicalModeThree)
        ensemble.probability ≪ (volume : Measure Real) := by
  have hfunction :
      (fun sample =>
        -modeFrequency (ensemble.restrictPositiveMass (N := 3) sample)
          secondPositivePhysicalModeThree) =
        actualIteratedA2MismatchSample ensemble .outer
          firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm := by
    funext sample
    exact (actualThreeSiteSingleFrequencyOuterMismatchSample_eq
      ensemble sample).symm
  rw [hfunction]
  simpa only [physlibIteratedA2MismatchLaw] using
    actualThreeSiteSingleFrequencyOuterMismatchLaw_absolutelyContinuous
      ensemble

/-! ## Signed Radon--Nikodym and weak-coupling endpoints -/

/-- The concrete channel has a signed-frame `L1` Fourier-density certificate
under only measurable uniformly bounded radius coordinates. -/
def actualThreeSiteSingleFrequencyOuterSignedL1Certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer kappa
      radius firstPositivePhysicalModeThree
      threeSiteSingleFrequencyOuterTerm := by
  exact
    actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
      ensemble (by norm_num) .outer kappa R hR radius hradiusMeasurable
        hradiusBound firstPositivePhysicalModeThree
        threeSiteSingleFrequencyOuterTerm
        (actualThreeSiteSingleFrequencyOuterMismatchLaw_absolutelyContinuous
          ensemble)

/-- Strong concrete fixed-volume endpoint: the signed external `g^2`
multiple of this actual A2 channel, accumulated to the `g^-2` kinetic window,
tends to zero.  All spectral and Jacobian hypotheses have been discharged by
the explicit frozen-fiber eliminant and the general local algebraic pipeline.
-/
theorem tendsto_actualThreeSiteSingleFrequencyOuterSignedWeakCoupling
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        .outer kappa radius firstPositivePhysicalModeThree
        threeSiteSingleFrequencyOuterTerm)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply
    tendsto_actualSignedIteratedA2WeakCoupling_of_frozenPair_jacobianCertificates
      ensemble (by norm_num) (0 : Lattice.Site 3) (1 : Lattice.Site 3)
        (by decide) .outer kappa R hR radius hradiusMeasurable hradiusBound
        firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm
        (fun rest => frozenFiberThreeSiteOuterJacobianPolynomial
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest))
  · intro rest
    exact frozenFiberThreeSiteOuterJacobianPolynomial_ne_zero
      (finitePairEnvironmentPositiveMassConfig
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest)
  · intro rest pair hpair hsimple hjacobian
    exact
      frozenFiberThreeSite_outerVerticalJacobian_zero_forces_polynomial_zero
        (finitePairEnvironmentPositiveMassConfig
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest)
        pair hpair hsimple hjacobian
  · exact threeSiteSingleFrequencyOuter_avoidsAcoustic

/-- Packaged end-to-end statement exposing the unweighted absolute
continuity, existence of the signed `L1` certificate, and the kinetic-window
limit simultaneously. -/
theorem actualThreeSiteSingleFrequencyOuterSignedFixedVolume_endToEnd
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    physlibIteratedA2MismatchLaw ensemble .outer
          firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm ≪
        (volume : Measure Real) ∧
      Nonempty
        (ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer
          kappa radius firstPositivePhysicalModeThree
          threeSiteSingleFrequencyOuterTerm) ∧
      Tendsto
        (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeThree
          threeSiteSingleFrequencyOuterTerm)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    ⟨actualThreeSiteSingleFrequencyOuterMismatchLaw_absolutelyContinuous
        ensemble,
      ⟨actualThreeSiteSingleFrequencyOuterSignedL1Certificate ensemble
        kappa R hR radius hradiusMeasurable hradiusBound⟩,
      tendsto_actualThreeSiteSingleFrequencyOuterSignedWeakCoupling ensemble
        kappa R hR radius hradiusMeasurable hradiusBound⟩

end

end ActualThreeSiteIteratedA2SignedFixedVolumeClosure
end ArchonPhysics
