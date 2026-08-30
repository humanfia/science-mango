import ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
import ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall
import ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate

/-!
# Annealed and qualitative-L1 closure of compact iterated-A2 fibre atlases

This module integrates the compact one-mass `A2` fibre atlas through the
exact selected-pair/complement reconstruction of a finite iid mass ensemble.
For a compact family `K rest first`, it produces a complete annealed centered
small-ball estimate.  The regular term is the integral of the actual finite
atlas costs, and the exceptional term is exactly the iterated integral of
`massCoordinateLaw (K rest first)ᶜ`.

No measurability of the automatically chosen atlas cardinalities is needed:
the raw conclusion retains their upper integral.  A second endpoint assumes
one transparent uniform ceiling for those regular costs and separates it as
a linear term plus the integrated compact-bad mass.

If the compact-bad mass vanishes on every frozen fibre, the full actual
mismatch law is absolutely continuous with respect to Lebesgue measure even
without a uniform atlas-cardinality bound.  The generic weighted
Radon--Nikodym construction then gives an `L1` Fourier certificate and the
fixed-volume qualitative kinetic closure for every measurable integrable
complex history weight.

Charge-matched total return channels remain an exact counterexample: their
mismatch law is a unit atom at zero and is not absolutely continuous.
Nothing below estimates the compact-bad mass, controls atlas costs uniformly
in volume, or closes higher recollisions/RPA.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Exact selected-pair/complement reconstruction of one actual mismatch law,
evaluated on an arbitrary measurable target.  This is the full-iid Fubini
identity used by both the small-ball and absolute-continuity endpoints. -/
theorem physlibIteratedA2MismatchLaw_apply_eq_lintegral_frozenPair
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    {target : Set Real} (htarget : MeasurableSet target) :
    physlibIteratedA2MismatchLaw ensemble channel observed term target =
      ∫⁻ rest,
        Measure.map
          (physlibIteratedA2PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term)
          iidMassPairLaw target
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂)) := by
  let restIndices := finiteVolumeMassPairComplement site₁ site₂
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure (iidFiniteMassVectorLaw restIndices) := by
    unfold iidFiniteMassVectorLaw
    infer_instance
  let randomState := fun sample =>
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
  apply lintegral_congr
  intro rest
  have hpairMeas : Measurable
      (physlibIteratedA2PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term) :=
    measurable_physlibIteratedA2PairMismatchChart
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      site₁ site₂ channel observed term
  rw [Measure.map_apply hpairMeas htarget]
  rfl

/-- Raw full-iid compact-atlas estimate.  The chosen atlas cardinalities may
depend on both the frozen complementary environment and the first selected
mass.  Keeping their upper integral is the strongest statement available
without an additional uniform-parametric atlas theorem. -/
theorem exists_atlasCard_physlibIteratedA2MismatchLaw_Ioo_le_lintegral_compactFiber
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (K : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) →
        Real → Set Real)
    (hK : ∀ rest first, IsCompact (K rest first))
    (hKregular : ∀ rest first second, second ∈ K rest first →
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
    (j₀ : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) → Real → Real)
    (hj₀ : ∀ rest first, 0 < j₀ rest first)
    (hjac : ∀ rest first second, second ∈ K rest first →
      j₀ rest first ≤
        |physlibIteratedA2PairMismatchVerticalJacobian
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term (first, second)|) :
    ∃ atlasCard : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) → Real → Nat,
      ∀ delta : Real,
        physlibIteratedA2MismatchLaw ensemble channel observed term
            (Ioo (-delta) delta) ≤
          ∫⁻ rest, ∫⁻ first,
            ((atlasCard rest first : ENNReal) *
                ((5 / 2 : ENNReal) *
                  (ENNReal.ofReal (j₀ rest first))⁻¹)) *
                  ENNReal.ofReal (2 * delta) +
              massCoordinateLaw (K rest first)ᶜ
            ∂massCoordinateLaw
          ∂(iidFiniteMassVectorLaw
            (finiteVolumeMassPairComplement site₁ site₂)) := by
  classical
  have hlocal : ∀ rest first, ∃ atlasCard : Nat,
      ∀ delta : Real,
        Measure.map
            (fun second => physlibIteratedA2PairMismatchChart
              (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
              site₁ site₂ channel observed term (first, second))
            massCoordinateLaw (Ioo (-delta) delta) ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) *
              (ENNReal.ofReal (j₀ rest first))⁻¹)) *
                ENNReal.ofReal (2 * delta) +
            massCoordinateLaw (K rest first)ᶜ := by
    intro rest first
    obtain ⟨atlasCard, _hrestrict, hfull⟩ :=
      exists_atlasCard_physlibIteratedA2PairFiberCompact_smallBall
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        hsite channel observed term first (K rest first) (hK rest first)
        (hKregular rest first) (hj₀ rest first) (hjac rest first)
    exact ⟨atlasCard, hfull⟩
  choose atlasCard hsmallBall using hlocal
  refine ⟨atlasCard, ?_⟩
  intro delta
  rw [physlibIteratedA2MismatchLaw_apply_eq_lintegral_frozenPair
    ensemble site₁ site₂ hsite channel observed term measurableSet_Ioo]
  apply lintegral_mono
  intro rest
  let pairChart := physlibIteratedA2PairMismatchChart
    (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
    site₁ site₂ channel observed term
  have hpairChart : Measurable pairChart :=
    measurable_physlibIteratedA2PairMismatchChart
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      site₁ site₂ channel observed term
  let target : Set Real := Ioo (-delta) delta
  let event : Set (Real × Real) := pairChart ⁻¹' target
  have htarget : MeasurableSet target := measurableSet_Ioo
  have hevent : MeasurableSet event := htarget.preimage hpairChart
  change Measure.map pairChart iidMassPairLaw target ≤ _
  rw [Measure.map_apply hpairChart htarget]
  change iidMassPairLaw event ≤ _
  rw [iidMassPairLaw, MeasureTheory.Measure.prod_apply hevent]
  apply lintegral_mono
  intro first
  let fiber : Real → Real := fun second => pairChart (first, second)
  have hfiber : Measurable fiber :=
    hpairChart.comp (measurable_const.prodMk measurable_id)
  have hpreimage :
      massCoordinateLaw (Prod.mk first ⁻¹' event) =
        Measure.map fiber massCoordinateLaw target := by
    rw [Measure.map_apply hfiber htarget]
    rfl
  change massCoordinateLaw (Prod.mk first ⁻¹' event) ≤ _
  rw [hpreimage]
  simpa [fiber, pairChart, target] using hsmallBall rest first delta

/-- Uniform-budget specialization of the raw annealed atlas estimate.  The
only new premise is the displayed ceiling on the automatically selected
finite-atlas regular costs.  The bad mass remains the exact double integral
over the frozen environment and first selected mass. -/
theorem exists_atlasCard_physlibIteratedA2MismatchLaw_Ioo_le_uniformCost_add_lintegral_bad
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (K : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) →
        Real → Set Real)
    (hK : ∀ rest first, IsCompact (K rest first))
    (hKregular : ∀ rest first second, second ∈ K rest first →
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
    (j₀ : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) → Real → Real)
    (hj₀ : ∀ rest first, 0 < j₀ rest first)
    (hjac : ∀ rest first second, second ∈ K rest first →
      j₀ rest first ≤
        |physlibIteratedA2PairMismatchVerticalJacobian
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term (first, second)|) :
    ∃ atlasCard : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) → Real → Nat,
      ∀ {regularCostCeiling : ENNReal},
        (∀ rest first,
          (atlasCard rest first : ENNReal) *
              ((5 / 2 : ENNReal) *
                (ENNReal.ofReal (j₀ rest first))⁻¹) ≤
            regularCostCeiling) →
        ∀ delta : Real,
          physlibIteratedA2MismatchLaw ensemble channel observed term
              (Ioo (-delta) delta) ≤
            regularCostCeiling * ENNReal.ofReal (2 * delta) +
              ∫⁻ rest, ∫⁻ first,
                massCoordinateLaw (K rest first)ᶜ
                ∂massCoordinateLaw
              ∂(iidFiniteMassVectorLaw
                (finiteVolumeMassPairComplement site₁ site₂)) := by
  classical
  obtain ⟨atlasCard, hraw⟩ :=
    exists_atlasCard_physlibIteratedA2MismatchLaw_Ioo_le_lintegral_compactFiber
      ensemble hsite channel observed term K hK hKregular j₀ hj₀ hjac
  refine ⟨atlasCard, ?_⟩
  intro regularCostCeiling hceiling delta
  let window := ENNReal.ofReal (2 * delta)
  calc
    physlibIteratedA2MismatchLaw ensemble channel observed term
        (Ioo (-delta) delta) ≤
      ∫⁻ rest, ∫⁻ first,
        ((atlasCard rest first : ENNReal) *
            ((5 / 2 : ENNReal) *
              (ENNReal.ofReal (j₀ rest first))⁻¹)) * window +
          massCoordinateLaw (K rest first)ᶜ
        ∂massCoordinateLaw
      ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)) := by
      simpa [window] using hraw delta
    _ ≤ ∫⁻ rest, ∫⁻ first,
        regularCostCeiling * window +
          massCoordinateLaw (K rest first)ᶜ
        ∂massCoordinateLaw
      ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)) := by
      apply lintegral_mono
      intro rest
      apply lintegral_mono
      intro first
      have hmul := mul_le_mul_right (hceiling rest first) window
      have hmulRight :
          ((atlasCard rest first : ENNReal) *
              ((5 / 2 : ENNReal) *
                (ENNReal.ofReal (j₀ rest first))⁻¹)) * window ≤
            regularCostCeiling * window := by
        calc
          ((atlasCard rest first : ENNReal) *
              ((5 / 2 : ENNReal) *
                (ENNReal.ofReal (j₀ rest first))⁻¹)) * window =
              window * ((atlasCard rest first : ENNReal) *
                ((5 / 2 : ENNReal) *
                  (ENNReal.ofReal (j₀ rest first))⁻¹)) := mul_comm _ _
          _ ≤ window * regularCostCeiling := hmul
          _ = regularCostCeiling * window := mul_comm _ _
      exact add_le_add hmulRight le_rfl
    _ = regularCostCeiling * ENNReal.ofReal (2 * delta) +
        ∫⁻ rest, ∫⁻ first,
          massCoordinateLaw (K rest first)ᶜ
          ∂massCoordinateLaw
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂)) := by
      simp only [lintegral_add_left measurable_const]
      simp [window, iidFiniteMassVectorLaw]

/-- Vanishing compact-bad mass makes the full actual mismatch law absolutely
continuous.  Unlike the quantitative domination endpoint, this needs no
uniform bound on atlas multiplicities or Jacobian costs across frozen
environments. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_compactFiber_badMass_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (K : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) →
        Real → Set Real)
    (hK : ∀ rest first, IsCompact (K rest first))
    (hKregular : ∀ rest first second, second ∈ K rest first →
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
    (j₀ : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) → Real → Real)
    (hj₀ : ∀ rest first, 0 < j₀ rest first)
    (hjac : ∀ rest first second, second ∈ K rest first →
      j₀ rest first ≤
        |physlibIteratedA2PairMismatchVerticalJacobian
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term (first, second)|)
    (hbad : ∀ rest, ∀ᵐ first ∂massCoordinateLaw,
      massCoordinateLaw (K rest first)ᶜ = 0) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  classical
  apply Measure.AbsolutelyContinuous.mk
  intro target htarget htargetZero
  rw [physlibIteratedA2MismatchLaw_apply_eq_lintegral_frozenPair
    ensemble site₁ site₂ hsite channel observed term htarget]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards with rest
  let pairChart := physlibIteratedA2PairMismatchChart
    (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
    site₁ site₂ channel observed term
  have hpairChart : Measurable pairChart :=
    measurable_physlibIteratedA2PairMismatchChart
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      site₁ site₂ channel observed term
  rw [Measure.map_apply hpairChart htarget]
  let event : Set (Real × Real) := pairChart ⁻¹' target
  have hevent : MeasurableSet event := htarget.preimage hpairChart
  change iidMassPairLaw event = 0
  rw [iidMassPairLaw, MeasureTheory.Measure.prod_apply hevent]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hbad rest] with first hbadFirst
  let fiber : Real → Real := fun second => pairChart (first, second)
  have hfiber : Measurable fiber :=
    hpairChart.comp (measurable_const.prodMk measurable_id)
  have hpreimage :
      massCoordinateLaw (Prod.mk first ⁻¹' event) =
        Measure.map fiber massCoordinateLaw target := by
    rw [Measure.map_apply hfiber htarget]
    rfl
  rw [hpreimage]
  obtain ⟨atlasCard, hrestrict, _hfull⟩ :=
    exists_atlasCard_physlibIteratedA2PairFiberCompact_smallBall
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      hsite channel observed term first (K rest first) (hK rest first)
      (hKregular rest first) (hj₀ rest first) (hjac rest first)
  have haeK : ∀ᵐ second ∂massCoordinateLaw, second ∈ K rest first :=
    MeasureTheory.ae_iff.mpr hbadFirst
  have hrestrictEq : massCoordinateLaw.restrict (K rest first) =
      massCoordinateLaw := Measure.restrict_eq_self_of_ae_mem haeK
  rw [hrestrictEq] at hrestrict
  have hzero :
      Measure.map
          (fun second => physlibIteratedA2PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ channel observed term (first, second))
          massCoordinateLaw target ≤ 0 := by
    simpa [Measure.smul_apply, htargetZero] using hrestrict target
  simpa [fiber, pairChart] using nonpos_iff_eq_zero.mp hzero

/-- Canonical weighted RN `L1` certificate obtained from the compact-atlas
absolute-continuity endpoint.  The source history weight may be arbitrary as
long as it is measurable and integrable. -/
def actualIteratedA2WeightedChannelL1Certificate_of_compactFiber_badMass_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (weight : Omega → Complex)
    (hweightMeasurable : Measurable weight)
    (hweight : Integrable weight ensemble.probability)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (K : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) →
        Real → Set Real)
    (hK : ∀ rest first, IsCompact (K rest first))
    (hKregular : ∀ rest first second, second ∈ K rest first →
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
    (j₀ : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) → Real → Real)
    (hj₀ : ∀ rest first, 0 < j₀ rest first)
    (hjac : ∀ rest first second, second ∈ K rest first →
      j₀ rest first ≤
        |physlibIteratedA2PairMismatchVerticalJacobian
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term (first, second)|)
    (hbad : ∀ rest, ∀ᵐ first ∂massCoordinateLaw,
      massCoordinateLaw (K rest first)ᶜ = 0) :
    ActualIteratedA2WeightedChannelL1FourierCertificate
      ensemble channel weight observed term :=
  weightedMismatchL1FourierCertificate_of_map_absolutelyContinuous
    ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term) weight
    (measurable_actualIteratedA2MismatchSample
      ensemble channel observed term)
    hweightMeasurable hweight
    (physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_compactFiber_badMass_zero
      ensemble hsite channel observed term K hK hKregular j₀ hj₀ hjac hbad)

/-- Fixed-volume qualitative kinetic closure obtained by feeding the RN
certificate above into Riemann--Lebesgue plus continuous Cesaro averaging. -/
theorem tendsto_actualIteratedA2WeightedChannel_of_compactFiber_badMass_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (weight : Omega → Complex)
    (hweightMeasurable : Measurable weight)
    (hweight : Integrable weight ensemble.probability)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (K : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) →
        Real → Set Real)
    (hK : ∀ rest first, IsCompact (K rest first))
    (hKregular : ∀ rest first second, second ∈ K rest first →
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂ channel observed term)
    (j₀ : FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) → Real → Real)
    (hj₀ : ∀ rest first, 0 < j₀ rest first)
    (hjac : ∀ rest first second, second ∈ K rest first →
      j₀ rest first ≤
        |physlibIteratedA2PairMismatchVerticalJacobian
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ channel observed term (first, second)|)
    (hbad : ∀ rest, ∀ᵐ first ∂massCoordinateLaw,
      massCoordinateLaw (K rest first)ᶜ = 0) :
    Tendsto
      (weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualIteratedA2WeightedChannel_qualitativeL1
    ensemble channel weight observed term
      (actualIteratedA2WeightedChannelL1Certificate_of_compactFiber_badMass_zero
        ensemble hsite channel weight hweightMeasurable hweight observed term
          K hK hKregular j₀ hj₀ hjac hbad)

/-- Exact retained-sector counterexample: the charge-matched total mismatch
law has a unit atom at zero and therefore cannot be Lebesgue-absolutely
continuous. -/
theorem not_physlibIteratedA2ChargeMatchedTotalMismatchLaw_absolutelyContinuous_volume
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) :
    ¬ physlibIteratedA2MismatchLaw ensemble .total observed term ≪
      (volume : Measure Real) := by
  intro hac
  have hnull : physlibIteratedA2MismatchLaw ensemble .total observed term
      ({0} : Set Real) = 0 := hac (by simp)
  have hone : physlibIteratedA2MismatchLaw ensemble .total observed term
      ({0} : Set Real) = 1 := by
    unfold physlibIteratedA2MismatchLaw
    rw [Measure.map_apply
      (measurable_actualIteratedA2MismatchSample
        ensemble .total observed term) (measurableSet_singleton (0 : Real))]
    have hevent :
        (actualIteratedA2MismatchSample ensemble .total observed term) ⁻¹'
            ({0} : Set Real) = Set.univ := by
      ext sample
      simp only [mem_preimage, mem_singleton_iff, mem_univ, iff_true]
      change iteratedQuadraticOuterMismatch
          (ensemble.restrictPositiveMass (N := N) sample) observed term +
        iteratedQuadraticInnerMismatch
          (ensemble.restrictPositiveMass (N := N) sample) term = 0
      rw [iteratedQuadraticOuterMismatch_eq_neg_inner_of_charge_eq_freeInitial
        _ observed term hcharge]
      ring
    rw [hevent, ensemble.probability_univ]
  rw [hone] at hnull
  norm_num at hnull

end

end ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1
