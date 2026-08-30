import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Compactness.Lindelof
import ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
import ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
import ArchonPhysics.QuantitativeJacobianPushforward

/-!
# Countable local absolute continuity for actual iterated-A2 mismatches

This module replaces the uniform global fibre-injectivity and uniform
Jacobian hypotheses by their correct qualitative local form.  A generic
measure lemma first glues countably many restricted pushforwards.  Lindelof
extraction then turns pointwise open inverse-function patches on countably
many quantitative good levels into such a cover.

For the actual iterated-`A2` mismatch, almost-everywhere regularity and a
nonzero genuine vertical Jacobian therefore imply absolute continuity of
each frozen pair law.  Fubini lifts this first from one-mass fibres to the iid
pair and then, through exact pair/complement reconstruction, to the complete
finite-volume iid ensemble.  The explicit algebraic regularity certificate
supplies the almost-everywhere premise.

The final theorem feeds this local conclusion to the measurable signed-frame
Radon--Nikodym closure.  No global fibre injectivity, uniform Jacobian lower
bound, or legacy eigenvector-sign measurability is assumed.  The statement is
still fixed-volume and conditional on the displayed finite algebraic
nonvanishing certificates; it supplies neither volume-uniform rates nor the
higher recollision/RPA estimates.
-/

namespace ArchonPhysics
namespace PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-! ## Generic countable local gluing -/

/-- If a source measure is almost everywhere covered by countably many
measurable patches and every restricted pushforward is absolutely continuous,
then the full pushforward is absolutely continuous. -/
theorem map_absolutelyContinuous_of_ae_countable_restrict_cover
    (sourceMeasure targetMeasure : Measure Real)
    (mapFunction : Real → Real) (hmap : Measurable mapFunction)
    (patch : Nat → Set Real) (_hpatch : ∀ n, MeasurableSet (patch n))
    (hcover : ∀ᵐ point ∂sourceMeasure, point ∈ ⋃ n, patch n)
    (hlocal : ∀ n,
      Measure.map mapFunction (sourceMeasure.restrict (patch n)) ≪
        targetMeasure) :
    Measure.map mapFunction sourceMeasure ≪ targetMeasure := by
  apply Measure.AbsolutelyContinuous.mk
  intro nullSet hnullSet htargetNull
  rw [Measure.map_apply hmap hnullSet]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have havoid : ∀ᵐ point ∂sourceMeasure, ∀ n,
      point ∉ mapFunction ⁻¹' nullSet ∩ patch n := by
    apply ae_all_iff.mpr
    intro n
    apply measure_eq_zero_iff_ae_notMem.mp
    have hzero := hlocal n htargetNull
    rw [Measure.map_apply hmap hnullSet,
      Measure.restrict_apply (hnullSet.preimage hmap)] at hzero
    exact hzero
  filter_upwards [hcover, havoid] with point hpointCover hpointAvoid
  intro hpointNull
  rcases mem_iUnion.mp hpointCover with ⟨n, hpointPatch⟩
  exact hpointAvoid n ⟨hpointNull, hpointPatch⟩

/-- Pointwise open local patches on countably many measurable source levels
automatically reduce to the countable restricted cover above.  The open
carriers are countabilized by hereditary Lindelofness; the actual restricted
patch is the carrier intersected with its source level. -/
theorem map_absolutelyContinuous_of_ae_countable_local_open_patches
    (sourceMeasure targetMeasure : Measure Real)
    (mapFunction : Real → Real) (hmap : Measurable mapFunction)
    (source : Nat → Set Real)
    (hsource : ∀ n, MeasurableSet (source n))
    (hcover : ∀ᵐ point ∂sourceMeasure, point ∈ ⋃ n, source n)
    (hlocal : ∀ n point, point ∈ source n →
      ∃ carrier : Set Real,
        point ∈ carrier ∧ IsOpen carrier ∧
        Measure.map mapFunction
            (sourceMeasure.restrict (carrier ∩ source n)) ≪
          targetMeasure) :
    Measure.map mapFunction sourceMeasure ≪ targetMeasure := by
  classical
  have hlocalSubtype : ∀ n (point : source n),
      ∃ carrier : Set Real,
        (point : Real) ∈ carrier ∧ IsOpen carrier ∧
        Measure.map mapFunction
            (sourceMeasure.restrict (carrier ∩ source n)) ≪
          targetMeasure :=
    fun n point => hlocal n point point.property
  choose localCarrier hpoint hopen hac using hlocalSubtype
  let indexedCarrier : (n : Nat) → Option (source n) → Set Real :=
    fun n index =>
      match index with
      | none => ∅
      | some point => localCarrier n point
  have hindexedOpen : ∀ n index, IsOpen (indexedCarrier n index) := by
    intro n index
    cases index with
    | none => exact isOpen_empty
    | some point => exact hopen n point
  have hsourceCover : ∀ n,
      source n ⊆ ⋃ index, indexedCarrier n index := by
    intro n point hpointSource
    exact mem_iUnion.mpr
      ⟨some ⟨point, hpointSource⟩,
        hpoint n ⟨point, hpointSource⟩⟩
  have hexistsEnumeration : ∀ n,
      ∃ enumeration : Nat → Option (source n),
        source n ⊆ ⋃ localIndex, indexedCarrier n (enumeration localIndex) := by
    intro n
    exact
      (HereditarilyLindelofSpace.isLindelof (source n)).indexed_countable_subcover
        (indexedCarrier n) (hindexedOpen n) (hsourceCover n)
  choose enumeration henumeration using hexistsEnumeration
  let countablePatch : Nat → Set Real := fun index =>
    indexedCarrier (Nat.unpair index).1
        (enumeration (Nat.unpair index).1 (Nat.unpair index).2) ∩
      source (Nat.unpair index).1
  have hcountablePatch : ∀ index, MeasurableSet (countablePatch index) := by
    intro index
    exact (hindexedOpen _ _).measurableSet.inter (hsource _)
  have hcountableCover : ∀ᵐ point ∂sourceMeasure,
      point ∈ ⋃ index, countablePatch index := by
    filter_upwards [hcover] with point hpointCover
    rcases mem_iUnion.mp hpointCover with ⟨n, hpointSource⟩
    rcases mem_iUnion.mp (henumeration n hpointSource) with
      ⟨localIndex, hpointCarrier⟩
    refine mem_iUnion.mpr ⟨Nat.pair n localIndex, ?_⟩
    change point ∈
      indexedCarrier (Nat.unpair (Nat.pair n localIndex)).1
          (enumeration (Nat.unpair (Nat.pair n localIndex)).1
            (Nat.unpair (Nat.pair n localIndex)).2) ∩
        source (Nat.unpair (Nat.pair n localIndex)).1
    rw [Nat.unpair_pair]
    exact ⟨hpointCarrier, hpointSource⟩
  have hcountableAC : ∀ index,
      Measure.map mapFunction
          (sourceMeasure.restrict (countablePatch index)) ≪
        targetMeasure := by
    intro index
    cases hindex : enumeration (Nat.unpair index).1 (Nat.unpair index).2 with
    | none => simp [countablePatch, indexedCarrier, hindex]
    | some point =>
        simpa [countablePatch, indexedCarrier, hindex] using
          hac (Nat.unpair index).1 point
  exact map_absolutelyContinuous_of_ae_countable_restrict_cover
    sourceMeasure targetMeasure mapFunction hmap countablePatch
      hcountablePatch hcountableCover hcountableAC

/-! ## Actual one-mass fibre and iid-pair closure -/

/-- Almost-everywhere actual spectral regularity and noncriticality are
enough for absolute continuity of one frozen first-mass fibre.  Reciprocal
natural good levels provide a positive Jacobian lower bound on each patch;
no single lower bound or global injectivity is used. -/
theorem physlibIteratedA2PairMismatchFiberMap_absolutelyContinuous_volume_of_regularNoncritical_ae
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real)
    (hregular : ∀ᵐ second ∂massCoordinateLaw,
      (first, second) ∈
          physlibIteratedA2PairMismatchDifferentiabilitySource
            fixed site₁ site₂ channel observed term ∧
        physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ channel observed term (first, second) ≠ 0) :
    Measure.map
        (fun second => physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term (first, second))
        massCoordinateLaw ≪ (volume : Measure Real) := by
  let fiber : Real → Real := fun second =>
    physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term (first, second)
  let source : Nat → Set Real := fun n =>
    physlibIteratedA2PairFiberGoodLevel
      fixed site₁ site₂ channel observed term first n
  have hfiber : Measurable fiber :=
    (measurable_physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term).comp
        (measurable_const.prodMk measurable_id)
  have hsource : ∀ n, MeasurableSet (source n) := by
    intro n
    exact measurableSet_physlibIteratedA2PairFiberGoodLevel
      fixed site₁ site₂ channel observed term first n
  have hcover : ∀ᵐ second ∂massCoordinateLaw,
      second ∈ ⋃ n, source n := by
    filter_upwards [hregular] with second hsecond
    exact regularNoncriticalIteratedA2Fiber_subset_iUnion_goodLevel
      fixed site₁ site₂ channel observed term first hsecond
  apply map_absolutelyContinuous_of_ae_countable_local_open_patches
    massCoordinateLaw (volume : Measure Real) fiber hfiber source hsource
      hcover
  intro n second hsecond
  have hlevelPositive : 0 < 1 / ((n : Real) + 1) := by positivity
  have hjacNonzero :
      physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second) ≠ 0 := by
    exact abs_pos.mp (hlevelPositive.trans_le hsecond.2)
  obtain ⟨localPatch, hpoint, hopen, _hmeasurable, _hsupport,
      hinjective⟩ :=
    exists_physlibIteratedA2PairFiber_localInjectivePatch
      fixed hsite channel observed term hsecond.1 hjacNonzero
  refine ⟨localPatch, hpoint, hopen, ?_⟩
  let patch : Set Real := localPatch ∩ source n
  let derivative : Real → (Real →L[Real] Real) := fun point =>
    ContinuousLinearMap.toSpanSingleton Real
      (physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, point))
  have hpatch : MeasurableSet patch :=
    hopen.measurableSet.inter (hsource n)
  have hderivative : ∀ point, point ∈ patch →
      HasFDerivWithinAt fiber (derivative point) patch point := by
    intro point hpointPatch
    have hstrict := hasStrictDerivAt_physlibIteratedA2PairMismatchFiber
      fixed hsite channel observed term hpointPatch.2.1
    exact hstrict.hasDerivAt.hasFDerivAt.hasFDerivWithinAt
  have hsourceBound : massCoordinateLaw.restrict patch ≤
      (5 / 2 : ENNReal) • (volume : Measure Real).restrict patch := by
    calc
      massCoordinateLaw.restrict patch ≤
          ((5 / 2 : ENNReal) •
            (volume : Measure Real)).restrict patch :=
        Measure.restrict_mono_measure
          massCoordinateLaw_le_fiveHalves_smul_volume patch
      _ = (5 / 2 : ENNReal) •
          (volume : Measure Real).restrict patch := by
        rw [Measure.restrict_smul]
  have hmapBound :=
    map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure Real) hpatch fiber hfiber derivative hderivative
      (hinjective.mono inter_subset_left) hlevelPositive
      (fun point hpointPatch => by
        simpa [derivative] using hpointPatch.2.2)
      (massCoordinateLaw.restrict patch) (5 / 2 : ENNReal) hsourceBound
  exact hmapBound.absolutelyContinuous.trans
    Measure.smul_absolutelyContinuous

/-- Fubini transfer for qualitative absolute continuity: almost every
first-coordinate fibre being absolutely continuous implies the full product
pushforward is absolutely continuous. -/
theorem pairMap_absolutelyContinuous_of_ae_fiber
    (chart : Real × Real → Real) (hchart : Measurable chart)
    (hfiber : ∀ᵐ first ∂massCoordinateLaw,
      Measure.map (fun second => chart (first, second)) massCoordinateLaw ≪
        (volume : Measure Real)) :
    Measure.map chart iidMassPairLaw ≪ (volume : Measure Real) := by
  apply Measure.AbsolutelyContinuous.mk
  intro target htarget htargetZero
  rw [Measure.map_apply hchart htarget]
  have hevent : MeasurableSet (chart ⁻¹' target) := htarget.preimage hchart
  rw [iidMassPairLaw, MeasureTheory.Measure.prod_apply hevent]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hfiber] with first hfirst
  let fiber : Real → Real := fun second => chart (first, second)
  have hfiberMeasurable : Measurable fiber :=
    hchart.comp (measurable_const.prodMk measurable_id)
  have hzero : Measure.map fiber massCoordinateLaw target = 0 :=
    hfirst htargetZero
  rw [Measure.map_apply hfiberMeasurable htarget] at hzero
  exact hzero

/-- The actual iid-pair mismatch pushforward is absolutely continuous once
the genuine regular/noncritical set has full iid-pair measure. -/
theorem physlibIteratedA2PairMismatchMap_absolutelyContinuous_volume_of_regularNoncritical_ae
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
          fixed site₁ site₂ channel observed term ∧
        physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ channel observed term pair ≠ 0) :
    Measure.map
        (physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term)
        iidMassPairLaw ≪ (volume : Measure Real) := by
  let regularSet : Set (Real × Real) :=
    {pair |
      pair ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
          fixed site₁ site₂ channel observed term ∧
        physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ channel observed term pair ≠ 0}
  have hregularSet : MeasurableSet regularSet := by
    have hjacZero : MeasurableSet
        {pair : Real × Real |
          physlibIteratedA2PairMismatchVerticalJacobian
            fixed site₁ site₂ channel observed term pair = 0} :=
      (measurableSet_singleton (0 : Real)).preimage
        (measurable_physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ channel observed term)
    exact
      (measurableSet_physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term).inter hjacZero.compl
  have hfiberRegular : ∀ᵐ first ∂massCoordinateLaw,
      ∀ᵐ second ∂massCoordinateLaw, (first, second) ∈ regularSet := by
    rw [← Measure.ae_prod_mem_iff_ae_ae_mem hregularSet]
    simpa [iidMassPairLaw, regularSet] using hregular
  apply pairMap_absolutelyContinuous_of_ae_fiber
    (physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term)
    (measurable_physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term)
  filter_upwards [hfiberRegular] with first hfirst
  exact
    physlibIteratedA2PairMismatchFiberMap_absolutelyContinuous_volume_of_regularNoncritical_ae
      fixed hsite channel observed term first hfirst

/-! ## Exact finite-volume reconstruction and algebraic certificates -/

/-- Exact pair/complement reconstruction lifts frozen-pair absolute
continuity to the complete finite-volume iid mismatch law.  No uniform
density ceiling over the frozen environment is required. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hpair : ∀ rest : FiniteMassVector
        (finiteVolumeMassPairComplement site₁ site₂),
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
  filter_upwards with rest
  exact hpair rest htargetZero

/-- Almost-everywhere regular/noncritical actual pair charts in every frozen
environment imply absolute continuity of the complete iid mismatch law. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair_regularNoncritical_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : ∀ rest : FiniteMassVector
        (finiteVolumeMassPairComplement site₁ site₂),
      ∀ᵐ pair ∂iidMassPairLaw,
        pair ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term ∧
          physlibIteratedA2PairMismatchVerticalJacobian
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term pair ≠ 0) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  apply physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair
    ensemble site₁ site₂ hsite channel observed term
  intro rest
  exact
    physlibIteratedA2PairMismatchMap_absolutelyContinuous_volume_of_regularNoncritical_ae
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      hsite channel observed term (hregular rest)

/-- The two explicit finite polynomial nonvanishing obligations in each
frozen environment close the local absolute-continuity chain for an ordinary
channel avoiding the deterministic acoustic mode. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair_algebraicCertificates
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ∀ rest : FiniteMassVector
        (finiteVolumeMassPairComplement site₁ site₂),
      IteratedA2PairAlgebraicRegularityCertificate
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  apply
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair_regularNoncritical_ae
      ensemble site₁ site₂ hsite channel observed term
  intro rest
  simpa [IteratedA2PairAlgebraicRegularityCertificate.regularSet] using
    (certificate rest).regularSet_ae havoid

/-! ## Signed fixed-volume kinetic closure -/

/-- Fully local signed-frame qualitative closure.  Relative to the earlier
global-transversality endpoint, this removes global fibre injectivity and a
uniform positive Jacobian bound.  What remains is exactly the finite
algebraic certificate in every frozen complementary environment. -/
theorem tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_frozenPair_algebraicCertificates
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
    (certificate : ∀ rest : FiniteMassVector
        (finiteVolumeMassPairComplement site₁ site₂),
      IteratedA2PairAlgebraicRegularityCertificate
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
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
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair_algebraicCertificates
      ensemble site₁ site₂ hsite channel observed term certificate havoid

end

end PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity
end ArchonPhysics
