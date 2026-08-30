import ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Consumer-facing strongest fixed-volume endpoint.  The ordinary
single-frequency identity is displayed literally, and the only
frozen-environment algebraic premise is nonvanishing of the canonical
positive-spectrum characteristic Jacobian resultant. -/
theorem problem_physlib_fput_iterated_a2_single_frequency_canonical_resultant_signed_fixed_volume
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site N → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample ↦ radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (mode : Fin (Fintype.card (Lattice.Site N)))
    (hmode : mode ≠ lastOrderedIndex)
    (sign : Real) (hsign : sign ≠ 0)
    (hmismatch : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      physlibIteratedA2PairMismatchChart
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term =
        fun pair ↦ sign * orderedModeFrequency
          (twoSiteHarmonicHermitian
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ pair) mode)
    (hresultant : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      twoSitePositiveCharacteristicJacobianResultant
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ ≠ 0)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
        (volume : Measure Real) ∧
      Tendsto
        (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          channel kappa radius observed term)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    singleFrequencyCanonicalResultant_signedFixedVolume_endToEnd
      ensemble hN site₁ site₂ hsite channel kappa R hR radius
        hradiusMeasurable hradiusBound observed term mode hmode sign hsign
        hmismatch hresultant havoid

/-- Consumer-facing thermodynamic diagonal.  Every index may choose its own
finite volume and physical channel data; the positive couplings are selected
existentially, without imposing a volume-coupling scaling law. -/
theorem problem_physlib_fput_iterated_a2_single_frequency_canonical_resultant_thermodynamic_diagonal
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Nat → DependentActualA2ChannelDatum Omega)
    (hvolume : Tendsto (fun n ↦ (datum n).N) atTop atTop)
    (hN : ∀ n, 2 ≤ (datum n).N)
    (site₁ site₂ : ∀ n, Lattice.Site (datum n).N)
    (hsite : ∀ n, site₁ n ≠ site₂ n)
    (mode : ∀ n,
      letI : NeZero (datum n).N := (datum n).neZero
      Fin (Fintype.card (Lattice.Site (datum n).N)))
    (hmode : ∀ n,
      letI : NeZero (datum n).N := (datum n).neZero
      mode n ≠ lastOrderedIndex)
    (sign : Nat → Real) (hsign : ∀ n, sign n ≠ 0)
    (R : Nat → Real) (hR : ∀ n, 0 ≤ R n)
    (hradiusMeasurable : ∀ n mode,
      Measurable fun sample ↦ (datum n).radius sample mode)
    (hradiusBound : ∀ n sample mode,
      |(datum n).radius sample mode| ≤ R n)
    (hmismatch : ∀ n,
      letI : NeZero (datum n).N := (datum n).neZero
      ∀ᵐ rest ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement (site₁ n) (site₂ n))),
        physlibIteratedA2PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig
              (site₁ n) (site₂ n) rest)
            (site₁ n) (site₂ n) (datum n).channel
              (datum n).observed (datum n).term =
          fun pair ↦ sign n * orderedModeFrequency
            (twoSiteHarmonicHermitian
              (finitePairEnvironmentPositiveMassConfig
                (site₁ n) (site₂ n) rest)
              (site₁ n) (site₂ n) pair) (mode n))
    (hresultant : ∀ n,
      letI : NeZero (datum n).N := (datum n).neZero
      ∀ᵐ rest ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement (site₁ n) (site₂ n))),
        twoSitePositiveCharacteristicJacobianResultant
            (finitePairEnvironmentPositiveMassConfig
              (site₁ n) (site₂ n) rest)
            (site₁ n) (site₂ n) ≠ 0)
    (havoid : ∀ n,
      letI : NeZero (datum n).N := (datum n).neZero
      IteratedA2ChannelAvoidsAcoustic
        (datum n).channel (datum n).observed (datum n).term) :
    ∃ coupling : Nat → Real,
      (∀ n, 0 < coupling n) ∧
      Tendsto (fun n ↦ (datum n).N) atTop atTop ∧
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ signedExternalWeakCouplingAccumulation
          (datum n) ensemble (coupling n))
        atTop (nhds 0) := by
  exact
    exists_positive_thermodynamic_diagonal_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble datum hvolume hN site₁ site₂ hsite mode hmode sign hsign
        R hR hradiusMeasurable hradiusBound hmismatch hresultant havoid

#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure.ae_algebraicRegularityCertificates_of_singleFrequencyCanonicalResultant
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure.physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure.tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_ae_frozenPair_singleFrequencyCanonicalResultant
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure.singleFrequencyCanonicalResultant_signedFixedVolume_endToEnd
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure.exists_positive_thermodynamic_diagonal_of_ae_frozenPair_singleFrequencyCanonicalResultant
#print axioms
  problem_physlib_fput_iterated_a2_single_frequency_canonical_resultant_signed_fixed_volume
#print axioms
  problem_physlib_fput_iterated_a2_single_frequency_canonical_resultant_thermodynamic_diagonal

end

end ArchonPhysicsConsumers.Thermalization
