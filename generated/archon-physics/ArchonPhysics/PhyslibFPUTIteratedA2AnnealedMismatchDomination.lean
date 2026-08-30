import ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall

/-!
# Actual iterated-A2 mismatch-law domination

This module strengthens the centered-window estimate to full measure
domination.  Under the same global fiber certificate, the actual two-mass
mismatch law is bounded by

`((5 / 2) * (ENNReal.ofReal jacLower)⁻¹) • volume`.

Exact iid pair/complement reconstruction lifts a bound uniform in the frozen
environment to the finite-volume ensemble.  Hence the mismatch pushforward is
absolutely continuous with an explicit density ceiling, which is the correct
input for later `L1` Fourier certificates.

The hypotheses are not hidden: regularity and a positive Jacobian lower bound
are assumed on the open mass square, and the scalar fiber is assumed injective
on the full compact mass support.  Charge-matched total return channels are
proved to violate injectivity and have a unit atom at zero.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The sharp scalar Jacobian estimate as a domination of the entire
one-coordinate mismatch pushforward, when the good set has full source
measure. -/
theorem oneSiteMismatchMap_le_sharp_smul_volume_of_ae_fullGood
    (chart : Real → Real) (hchart : Measurable chart)
    (good : Set Real) (hgood : MeasurableSet good)
    (hfull : ∀ᵐ point ∂massCoordinateLaw, point ∈ good)
    (derivative : Real → (Real →L[Real] Real))
    (hderivative : ∀ point, point ∈ good →
      HasFDerivWithinAt chart (derivative point) good point)
    (hinjective : InjOn chart good)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ point, point ∈ good →
      jacLower ≤ |(derivative point).det|) :
    Measure.map chart massCoordinateLaw ≤
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) •
        (volume : Measure Real) := by
  have hsource : massCoordinateLaw ≤
      (5 / 2 : ENNReal) • (volume : Measure Real).restrict good := by
    rw [← Measure.restrict_eq_self_of_ae_mem hfull]
    calc
      massCoordinateLaw.restrict good ≤
          ((5 / 2 : ENNReal) • (volume : Measure Real)).restrict good :=
        Measure.restrict_mono_measure
          massCoordinateLaw_le_fiveHalves_smul_volume good
      _ = (5 / 2 : ENNReal) •
          (volume : Measure Real).restrict good := by
        rw [Measure.restrict_smul]
  exact map_le_smul_volume_of_le_volume_restrict_of_det_lower
    (volume : Measure Real) hgood chart hchart derivative hderivative
      hinjective hjacLower hjac massCoordinateLaw (5 / 2 : ENNReal) hsource

/-- Fubini transfer: almost-every frozen first-coordinate fiber dominated by
the same target measure implies domination of the full pair pushforward. -/
theorem pairMismatchMap_le_smul_volume_of_ae_fiberDomination
    (chart : Real × Real → Real) (hchart : Measurable chart)
    (densityCeiling : ENNReal)
    (hfiber : ∀ᵐ first ∂massCoordinateLaw,
      Measure.map (fun second ↦ chart (first, second)) massCoordinateLaw ≤
        densityCeiling • (volume : Measure Real)) :
    Measure.map chart iidMassPairLaw ≤
      densityCeiling • (volume : Measure Real) := by
  rw [Measure.le_iff]
  intro target htarget
  have hevent : MeasurableSet (chart ⁻¹' target) := htarget.preimage hchart
  rw [Measure.map_apply hchart htarget]
  change iidMassPairLaw (chart ⁻¹' target) ≤ _
  rw [iidMassPairLaw, MeasureTheory.Measure.prod_apply hevent]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    (∫⁻ first,
        massCoordinateLaw
          (Prod.mk first ⁻¹' (chart ⁻¹' target))
        ∂massCoordinateLaw) ≤
      ∫⁻ _first, densityCeiling * (volume : Measure Real) target
        ∂massCoordinateLaw := by
      apply lintegral_mono_ae
      filter_upwards [hfiber] with first hfirst
      let fiber : Real → Real := fun second ↦ chart (first, second)
      have hfiberMeas : Measurable fiber :=
        hchart.comp (measurable_const.prodMk measurable_id)
      have hpreimage :
          massCoordinateLaw
              (Prod.mk first ⁻¹' (chart ⁻¹' target)) =
            Measure.map fiber massCoordinateLaw target := by
        rw [Measure.map_apply hfiberMeas htarget]
        rfl
      rw [hpreimage]
      exact hfirst target
    _ = densityCeiling * (volume : Measure Real) target := by simp

/-- Full pair-law domination for one actual iterated-`A2` channel. -/
theorem physlibIteratedA2PairMismatchMap_le_volume_of_globalTransversality
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : ∀ first second,
      first ∈ Ioo massLower massUpper →
      second ∈ Ioo massLower massUpper →
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          fixed site₁ site₂ channel observed term)
    (hinjective : ∀ first, first ∈ massSupport → InjOn
      (fun second ↦ physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term (first, second))
      massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ first second,
      first ∈ Ioo massLower massUpper →
      second ∈ Ioo massLower massUpper →
      jacLower ≤ |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second)|) :
    Measure.map
        (physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term)
        iidMassPairLaw ≤
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) •
        (volume : Measure Real) := by
  apply pairMismatchMap_le_smul_volume_of_ae_fiberDomination
    (physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term)
    (measurable_physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term)
    ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹)
  filter_upwards [massCoordinate_mem_openMassSupport_ae]
    with first hfirst
  let fiber : Real → Real := fun second ↦
    physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term (first, second)
  let derivative : Real → (Real →L[Real] Real) := fun second ↦
    ContinuousLinearMap.toSpanSingleton Real
      (physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second))
  have hfiber : Measurable fiber :=
    (measurable_physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term).comp
        (measurable_const.prodMk measurable_id)
  have hderivative : ∀ second, second ∈ Ioo massLower massUpper →
      HasFDerivWithinAt fiber (derivative second)
        (Ioo massLower massUpper) second := by
    intro second hsecond
    have hstrict := hasStrictDerivAt_physlibIteratedA2PairMismatchFiber
      fixed hsite channel observed term
        (hregular first second hfirst hsecond)
    exact hstrict.hasDerivAt.hasFDerivAt.hasFDerivWithinAt
  have hinjectiveOpen : InjOn fiber (Ioo massLower massUpper) := by
    apply (hinjective first
      ⟨le_of_lt hfirst.1, le_of_lt hfirst.2⟩).mono
    intro second hsecond
    exact ⟨le_of_lt hsecond.1, le_of_lt hsecond.2⟩
  apply oneSiteMismatchMap_le_sharp_smul_volume_of_ae_fullGood
    fiber hfiber (Ioo massLower massUpper) measurableSet_Ioo
      massCoordinate_mem_openMassSupport_ae derivative hderivative
      hinjectiveOpen hjacLower
  intro second hsecond
  simpa [derivative] using hjac first second hfirst hsecond

/-- Pushforward law of one actual iterated-`A2` mismatch under the iid mass
ensemble. -/
def physlibIteratedA2MismatchLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Measure Real :=
  Measure.map
    (actualIteratedA2MismatchSample ensemble channel observed term)
    ensemble.probability

theorem measurable_actualIteratedA2MismatchSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Measurable
      (actualIteratedA2MismatchSample ensemble channel observed term) := by
  exact measurable_iteratedA2MismatchChannelValue_of_mass_coordinates
    (ensemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate ensemble)
    channel observed term

/-- Pair/complement chart whose mass reconstruction is pointwise exact. -/
def physlibIteratedA2ReconstructedMismatchChart
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (state : (Real × Real) ×
      FiniteMassVector (finiteVolumeMassPairComplement site₁ site₂)) : Real :=
  channel.value
    (finiteVolumePositiveMassPairReconstruction site₁ site₂ state)
    observed term

theorem measurable_physlibIteratedA2ReconstructedMismatchChart
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Measurable (physlibIteratedA2ReconstructedMismatchChart
      site₁ site₂ channel observed term) := by
  exact measurable_iteratedA2MismatchChannelValue_of_mass_coordinates
    (finiteVolumePositiveMassPairReconstruction site₁ site₂)
    (measurable_finiteVolumePositiveMassPairReconstruction_mass site₁ site₂)
    channel observed term

theorem physlibIteratedA2ReconstructedMismatchChart_eq_pairMismatchChart
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (state : (Real × Real) ×
      FiniteMassVector (finiteVolumeMassPairComplement site₁ site₂)) :
    physlibIteratedA2ReconstructedMismatchChart
        site₁ site₂ channel observed term state =
      physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ state.2)
        site₁ site₂ channel observed term state.1 := by
  rfl

private theorem physlibIteratedA2MismatchLaw_le_of_frozenPairDomination
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (densityCeiling : ENNReal)
    (hpair : ∀ rest : FiniteMassVector
        (finiteVolumeMassPairComplement site₁ site₂),
      Measure.map
          (physlibIteratedA2PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term)
          iidMassPairLaw ≤
        densityCeiling • (volume : Measure Real)) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≤
      densityCeiling • (volume : Measure Real) := by
  let restIndices := finiteVolumeMassPairComplement site₁ site₂
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure (iidFiniteMassVectorLaw restIndices) := by
    unfold iidFiniteMassVectorLaw
    infer_instance
  let randomState := fun sample ↦
    (ensembleMassPair ensemble site₁.val site₂.val sample,
      ensembleFiniteMassVector ensemble restIndices sample)
  let chart := physlibIteratedA2ReconstructedMismatchChart
    site₁ site₂ channel observed term
  have hchart : Measurable chart :=
    measurable_physlibIteratedA2ReconstructedMismatchChart
      site₁ site₂ channel observed term
  have hval : site₁.val ≠ site₂.val := by
    intro heq
    exact hsite (ZMod.val_injective N heq)
  have hsite₁Rest : site₁.val ∉ restIndices := by
    simp [restIndices, finiteVolumeMassPairComplement,
      selectedMassPairIndices]
  have hsite₂Rest : site₂.val ∉ restIndices := by
    simp [restIndices, finiteVolumeMassPairComplement,
      selectedMassPairIndices]
  have hlaw := ensembleMassPair_prod_finiteEnvironment_hasLaw
    ensemble hval restIndices hsite₁Rest hsite₂Rest
  rw [Measure.le_iff]
  intro target htarget
  let event : Set ((Real × Real) × FiniteMassVector restIndices) :=
    chart ⁻¹' target
  have hevent : MeasurableSet event := htarget.preimage hchart
  have heventProbability :
      ensemble.probability (randomState ⁻¹' event) =
        (iidMassPairLaw.prod (iidFiniteMassVectorLaw restIndices)) event :=
    hlaw.measure_eq hevent
  have hsourceEvent :
      (actualIteratedA2MismatchSample ensemble channel observed term) ⁻¹'
          target = randomState ⁻¹' event := by
    ext sample
    change actualIteratedA2MismatchSample ensemble channel observed term sample
        ∈ target ↔ chart (randomState sample) ∈ target
    have hreconstruction :=
      finiteVolumePositiveMassPairReconstruction_ensemble_eq
        ensemble site₁ site₂ hsite sample
    simp only [actualIteratedA2MismatchSample, chart,
      physlibIteratedA2ReconstructedMismatchChart, randomState]
    rw [hreconstruction]
  unfold physlibIteratedA2MismatchLaw
  rw [Measure.map_apply
    (measurable_actualIteratedA2MismatchSample
      ensemble channel observed term) htarget]
  rw [hsourceEvent, heventProbability,
    MeasureTheory.Measure.prod_apply_symm hevent]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    (∫⁻ rest,
        iidMassPairLaw ((fun pair ↦ (pair, rest)) ⁻¹' event)
        ∂iidFiniteMassVectorLaw restIndices) ≤
      ∫⁻ _rest, densityCeiling * (volume : Measure Real) target
        ∂iidFiniteMassVectorLaw restIndices := by
      apply lintegral_mono
      intro rest
      have hpairMeas : Measurable
          (physlibIteratedA2PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term) :=
        measurable_physlibIteratedA2PairMismatchChart
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term
      have hfiber :
          iidMassPairLaw ((fun pair ↦ (pair, rest)) ⁻¹' event) =
            Measure.map
              (physlibIteratedA2PairMismatchChart
                (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
                site₁ site₂ channel observed term)
              iidMassPairLaw target := by
        rw [Measure.map_apply hpairMeas htarget]
        rfl
      change iidMassPairLaw ((fun pair ↦ (pair, rest)) ⁻¹' event) ≤
        densityCeiling * (volume : Measure Real) target
      rw [hfiber]
      exact (hpair rest) target
    _ = densityCeiling * (volume : Measure Real) target := by simp

/-- Exact finite-volume iid domination endpoint, uniform only over the frozen
complementary environment at the displayed volume. -/
theorem physlibIteratedA2MismatchLaw_le_volume_of_uniform_globalTransversality
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : ∀ rest first second,
      first ∈ Ioo massLower massUpper →
      second ∈ Ioo massLower massUpper →
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term)
    (hinjective : ∀ rest first, first ∈ massSupport → InjOn
      (fun second ↦ physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second))
      massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ rest first second,
      first ∈ Ioo massLower massUpper →
      second ∈ Ioo massLower massUpper →
      jacLower ≤ |physlibIteratedA2PairMismatchVerticalJacobian
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second)|) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≤
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) •
        (volume : Measure Real) := by
  apply physlibIteratedA2MismatchLaw_le_of_frozenPairDomination
    ensemble site₁ site₂ hsite channel observed term
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹)
  intro rest
  exact physlibIteratedA2PairMismatchMap_le_volume_of_globalTransversality
    (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
    hsite channel observed term (hregular rest) (hinjective rest)
      hjacLower (hjac rest)

/-- Absolute-continuity corollary used by qualitative `L1` Fourier
grounding. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_uniform_globalTransversality
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hregular : ∀ rest first second,
      first ∈ Ioo massLower massUpper →
      second ∈ Ioo massLower massUpper →
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term)
    (hinjective : ∀ rest first, first ∈ massSupport → InjOn
      (fun second ↦ physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second))
      massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ rest first second,
      first ∈ Ioo massLower massUpper →
      second ∈ Ioo massLower massUpper →
      jacLower ≤ |physlibIteratedA2PairMismatchVerticalJacobian
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term (first, second)|) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  exact (physlibIteratedA2MismatchLaw_le_volume_of_uniform_globalTransversality
    ensemble site₁ site₂ hsite channel observed term hregular hinjective
      hjacLower hjac).absolutelyContinuous.trans
        Measure.smul_absolutelyContinuous

/-- Exact obstruction: a charge-matched total channel cannot satisfy the
full-support injectivity premise. -/
theorem not_globalFiberInjectivity_chargeMatchedTotal
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) :
    ¬ (∀ first, first ∈ massSupport → InjOn
      (fun second ↦ physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ .total observed term (first, second))
      massSupport) := by
  intro hinjective
  exact
    (not_injOn_physlibIteratedA2ChargeMatchedTotalPairFiber_massSupport
      fixed site₁ site₂ observed term hcharge massLower)
      (hinjective massLower ⟨le_rfl, massLower_le_massUpper⟩)

/-- Every positive centered window has probability one for a charge-matched
total return channel. -/
theorem physlibIteratedA2ChargeMatchedTotalMismatchLaw_Ioo_eq_one
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term)
    {delta : Real} (hdelta : 0 < delta) :
    physlibIteratedA2MismatchLaw ensemble .total observed term
      (Ioo (-delta) delta) = 1 := by
  unfold physlibIteratedA2MismatchLaw
  rw [Measure.map_apply
    (measurable_actualIteratedA2MismatchSample
      ensemble .total observed term) measurableSet_Ioo]
  have hzero : ∀ sample,
      actualIteratedA2MismatchSample ensemble .total observed term sample = 0 := by
    intro sample
    change iteratedQuadraticOuterMismatch
        (ensemble.restrictPositiveMass (N := N) sample) observed term +
      iteratedQuadraticInnerMismatch
        (ensemble.restrictPositiveMass (N := N) sample) term = 0
    rw [iteratedQuadraticOuterMismatch_eq_neg_inner_of_charge_eq_freeInitial
      _ observed term hcharge]
    ring
  have hevent :
      (actualIteratedA2MismatchSample ensemble .total observed term) ⁻¹'
          Ioo (-delta) delta = Set.univ := by
    ext sample
    simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_univ, iff_true]
    rw [hzero sample]
    constructor <;> linarith
  rw [hevent, ensemble.probability_univ]

end

end ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
