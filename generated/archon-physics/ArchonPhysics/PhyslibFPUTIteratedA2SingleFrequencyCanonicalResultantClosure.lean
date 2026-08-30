import ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal
import ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure
import ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalJacobian

/-!
# Canonical-resultant closure for ordinary single-frequency iterated-A2 channels

Fix two mass coordinates in an arbitrary positive finite volume and freeze the
remaining masses.  Suppose that, for almost every frozen complement, the
ordinary iterated-`A2` mismatch is exactly a nonzero signed multiple of one
fixed non-acoustic ordered frequency,

`pair |-> sign * orderedModeFrequency (twoSiteHarmonicHermitian ... pair) mode`,

and that the canonical positive-spectrum characteristic Jacobian resultant

`twoSitePositiveCharacteristicJacobianResultant fixed site1 site2`

is nonzero.  The single-frequency canonical Jacobian theorem then constructs
the pair-fiber algebraic regularity certificate.  The almost-everywhere
frozen-pair reconstruction gives absolute continuity of the full iid mismatch
law, and measurable bounded signed radii give the fixed-volume weak-coupling
limit.

The final theorem applies this result volume by volume and selects a positive
thermodynamic diagonal.  It assumes only that the volumes tend to infinity;
no rate or prescribed scaling relation between volume and coupling is claimed.
No arbitrary Jacobian polynomial or separate Jacobian-zero implication occurs
in any theorem statement in this file.
-/

namespace ArchonPhysics
namespace PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure

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
open ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereFrozenPairClosure
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalJacobian
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-! ## One arbitrary finite volume -/

/-- For an ordinary single-frequency channel, almost-everywhere nonvanishing
of the canonical characteristic Jacobian resultant supplies the exact
algebraic certificates used by the frozen-pair reconstruction. -/
theorem ae_algebraicRegularityCertificates_of_singleFrequencyCanonicalResultant
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
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
          site₁ site₂ ≠ 0) :
    ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      Nonempty (IteratedA2PairAlgebraicRegularityCertificate
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term) := by
  filter_upwards [hmismatch, hresultant] with rest hmismatchRest hresultantRest
  exact ⟨algebraicRegularityCertificateOfSingleFrequencyCanonicalResultant
    (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest) hsite
    channel observed term mode hmode sign hsign hmismatchRest hresultantRest⟩

/-- Full-iid absolute continuity for an arbitrary finite-volume ordinary
single-frequency channel.  The only frozen-rest algebraic assumption is
nonvanishing of the canonical positive-spectrum characteristic resultant. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
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
      (volume : Measure Real) := by
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_algebraicCertificates
      ensemble site₁ site₂ hsite channel observed term
        (ae_algebraicRegularityCertificates_of_singleFrequencyCanonicalResultant
          site₁ site₂ hsite channel observed term mode hmode sign hsign
            hmismatch hresultant)
        havoid

/-- Signed fixed-volume `g^2`/`g^-2` closure under the explicit
single-frequency identity, non-acoustic mode, canonical-resultant
nonvanishing, acoustic avoidance, and measurable bounded radii. -/
theorem tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_ae_frozenPair_singleFrequencyCanonicalResultant
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
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        channel kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_mismatchLaw_absolutelyContinuous
      ensemble hN channel kappa R hR radius hradiusMeasurable hradiusBound
        observed term
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble site₁ site₂ hsite channel observed term mode hmode sign hsign
        hmismatch hresultant havoid

/-- End-to-end fixed-volume package: the full iid mismatch law is absolutely
continuous and the corresponding signed kinetic-window accumulation tends to
zero. -/
theorem singleFrequencyCanonicalResultant_signedFixedVolume_endToEnd
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
  exact ⟨
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble site₁ site₂ hsite channel observed term mode hmode sign hsign
        hmismatch hresultant havoid,
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble hN site₁ site₂ hsite channel kappa R hR radius
        hradiusMeasurable hradiusBound observed term mode hmode sign hsign
        hmismatch hresultant havoid⟩

/-! ## A genuinely varying thermodynamic family -/

/-- A positive thermodynamic diagonal for arbitrary finite-volume ordinary
single-frequency channels.  Every volume may choose its own pair, ordered
mode, sign, channel, term, and radius bound.  The coupling is selected only
existentially and no `g_N` scaling is prescribed. -/
theorem exists_positive_thermodynamic_diagonal_of_ae_frozenPair_singleFrequencyCanonicalResultant
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
  apply
    exists_positive_thermodynamic_diagonal_of_actualSignedA2_of_mismatchLaw
      ensemble datum hvolume hN R hR hradiusMeasurable hradiusBound
  intro n
  let _ : NeZero (datum n).N := (datum n).neZero
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble (site₁ n) (site₂ n) (hsite n)
        (datum n).channel (datum n).observed (datum n).term
        (mode n) (hmode n) (sign n) (hsign n)
        (hmismatch n) (hresultant n) (havoid n)

end

end PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure
end ArchonPhysics
