import ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere
import ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory
import ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure

/-!
# Four-site opposite single-frequency signed fixed-volume closure

For the concrete ordinary outer history on four sites, vary the opposite
physical mass coordinates `0,2`.  Its pair-fiber mismatch is exactly `-omega_1`.
The frozen complementary masses at sites `1,3` differ almost everywhere, so
the exact opposite-fiber canonical resultant is nonzero almost everywhere.

The generic single-frequency canonical-resultant closure therefore gives
absolute continuity of the full iid mismatch law and the signed fixed-volume
weak-coupling limit.  No pointwise claim is made on the symmetric frozen
backgrounds where the resultant vanishes.
-/

namespace ArchonPhysics.ActualFourSiteOppositeSingleFrequencySignedFixedVolumeClosure

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere
open ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The concrete four-site pair-fiber single-frequency identity holds on
every frozen complement, hence in particular almost everywhere. -/
theorem fourSiteOpposite_outerMismatchChart_eq_signedFrequency_ae :
    ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement
          (0 : Lattice.Site 4) (2 : Lattice.Site 4))),
      physlibIteratedA2PairMismatchChart
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) .outer
          firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm =
        fun pair => fourSiteSingleFrequencyOuterSign * orderedModeFrequency
          (twoSiteHarmonicHermitian
            (finitePairEnvironmentPositiveMassConfig
              (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
          fourSiteSingleFrequencyOrderedMode := by
  exact Filter.Eventually.of_forall fun rest =>
    fourSiteOpposite_outerMismatchChart_eq_signedFrequency
      (finitePairEnvironmentPositiveMassConfig
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)

/-- The full iid law of the concrete four-site outer mismatch is absolutely
continuous with respect to Lebesgue measure. -/
theorem actualFourSiteOppositeSingleFrequencyOuterMismatchLaw_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) :
    physlibIteratedA2MismatchLaw ensemble .outer
        firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm ≪
      (volume : Measure Real) := by
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble (0 : Lattice.Site 4) (2 : Lattice.Site 4) (by decide)
        .outer firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm
        fourSiteSingleFrequencyOrderedMode
        fourSiteSingleFrequencyOrderedMode_ne_last
        fourSiteSingleFrequencyOuterSign
        fourSiteSingleFrequencyOuterSign_ne_zero
        fourSiteOpposite_outerMismatchChart_eq_signedFrequency_ae
        twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_ae
        fourSiteSingleFrequencyOuter_avoidsAcoustic

/-- Direct specialization of the generic canonical-resultant endpoint:
absolute continuity and signed fixed-volume convergence simultaneously. -/
theorem actualFourSiteOppositeSingleFrequencyOuterCanonicalResultant_endToEnd
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    physlibIteratedA2MismatchLaw ensemble .outer
          firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm ≪
        (volume : Measure Real) ∧
      Tendsto
        (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeFour
          fourSiteSingleFrequencyOuterTerm)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    singleFrequencyCanonicalResultant_signedFixedVolume_endToEnd
      ensemble (by norm_num) (0 : Lattice.Site 4) (2 : Lattice.Site 4)
        (by decide) .outer kappa R hR radius hradiusMeasurable hradiusBound
        firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm
        fourSiteSingleFrequencyOrderedMode
        fourSiteSingleFrequencyOrderedMode_ne_last
        fourSiteSingleFrequencyOuterSign
        fourSiteSingleFrequencyOuterSign_ne_zero
        fourSiteOpposite_outerMismatchChart_eq_signedFrequency_ae
        twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_ae
        fourSiteSingleFrequencyOuter_avoidsAcoustic

/-- Signed `L1` Fourier-density certificate obtained from the concrete full
mismatch-law absolute continuity theorem. -/
def actualFourSiteOppositeSingleFrequencyOuterSignedL1Certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer kappa
      radius firstPositivePhysicalModeFour
      fourSiteSingleFrequencyOuterTerm := by
  exact
    actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
      ensemble (by norm_num) .outer kappa R hR radius hradiusMeasurable
        hradiusBound firstPositivePhysicalModeFour
        fourSiteSingleFrequencyOuterTerm
        (actualFourSiteOppositeSingleFrequencyOuterMismatchLaw_absolutelyContinuous
          ensemble)

/-- The concrete signed external `g^2` contribution, accumulated to the
`g^-2` kinetic window, tends to zero at fixed four-site volume. -/
theorem tendsto_actualFourSiteOppositeSingleFrequencyOuterSignedWeakCoupling
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        .outer kappa radius firstPositivePhysicalModeFour
        fourSiteSingleFrequencyOuterTerm)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  (actualFourSiteOppositeSingleFrequencyOuterCanonicalResultant_endToEnd
    ensemble kappa R hR radius hradiusMeasurable hradiusBound).2

/-- End-to-end fixed-volume package matching the concrete three-site API:
full-law absolute continuity, a signed `L1` certificate, and the signed
weak-coupling limit. -/
theorem actualFourSiteOppositeSingleFrequencyOuterSignedFixedVolume_endToEnd
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    physlibIteratedA2MismatchLaw ensemble .outer
          firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm ≪
        (volume : Measure Real) ∧
      Nonempty
        (ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer
          kappa radius firstPositivePhysicalModeFour
          fourSiteSingleFrequencyOuterTerm) ∧
      Tendsto
        (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeFour
          fourSiteSingleFrequencyOuterTerm)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcanonical :=
    actualFourSiteOppositeSingleFrequencyOuterCanonicalResultant_endToEnd
      ensemble kappa R hR radius hradiusMeasurable hradiusBound
  exact
    ⟨hcanonical.1,
      ⟨actualFourSiteOppositeSingleFrequencyOuterSignedL1Certificate
        ensemble kappa R hR radius hradiusMeasurable hradiusBound⟩,
      hcanonical.2⟩

end

end ArchonPhysics.ActualFourSiteOppositeSingleFrequencySignedFixedVolumeClosure
