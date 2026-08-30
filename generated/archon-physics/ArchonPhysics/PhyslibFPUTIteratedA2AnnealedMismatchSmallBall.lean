import ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas

/-!
# Actual iterated-A2 pair and annealed small-ball bounds

This file turns a genuinely global one-mass transversality certificate for an
actual iterated-`A2` mismatch into the same sharp linear small-ball estimate
available for `A1`.  The hypotheses are deliberately visible:

* the actual spectral differentiability source holds on the open iid mass
  square;
* every frozen first-mass fiber is injective on the full compact
  `massSupport`;
* the genuine vertical Jacobian has one positive lower bound on the open
  square.

The open square is sufficient because the two boundary atoms have zero mass
under the uniform coordinate law.  Exact pair/complement reconstruction then
lifts a certificate uniform in the frozen environment to the original iid
finite-volume ensemble.

None of those global spectral hypotheses is inferred from the local inverse
atlas.  In particular, a charge-matched total channel is identically zero and
cannot satisfy the injectivity premise; it must remain in the resonant return
or feedback sector.  No volume-uniform Jacobian bound, nonlinear RPA estimate,
recollision control, or kinetic limit is asserted.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every actual iterated-`A2` mismatch channel is measurable whenever all
positive-mass coordinates are measurable. -/
theorem measurable_iteratedA2MismatchChannelValue_of_mass_coordinates
    {X : Type*} [MeasurableSpace X]
    {N : Nat} [NeZero N]
    (massSample : X → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun sample ↦ (massSample sample).mass site)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Measurable fun sample ↦ channel.value (massSample sample) observed term := by
  have hmatrix : Measurable fun sample ↦
      harmonicHermitian (massSample sample) := by
    apply Measurable.subtype_mk
    exact MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
      massSample hmass
  have hordered : Measurable fun sample mode ↦
      orderedModeFrequency (harmonicHermitian (massSample sample)) mode :=
    measurable_orderedModeFrequencies_unconditional
      (fun sample ↦ harmonicHermitian (massSample sample)) hmatrix
  have hfrequency : ∀ mode : Lattice.Site N,
      Measurable fun sample ↦ modeFrequency (massSample sample) mode := by
    intro mode
    let ordered := orderedIndexEquiv.symm mode
    have h : Measurable fun sample ↦
        orderedModeFrequency (harmonicHermitian (massSample sample)) ordered :=
      hordered.eval
    simpa [ordered, orderedModeFrequency_harmonicHermitian_eq] using h
  have hcharge (charge : Lattice.Site N → Int) :
      Measurable fun sample ↦
        chargeFrequency charge (modeFrequency (massSample sample)) := by
    unfold chargeFrequency
    apply Finset.measurable_sum
    intro mode _hmode
    exact measurable_const.mul (hfrequency mode)
  have houter
      (active : IteratedQuadraticSecondPicardCharacterTerm N) :
      Measurable fun sample ↦
        iteratedQuadraticOuterMismatch
          (massSample sample) observed active := by
    unfold iteratedQuadraticOuterMismatch
    exact ((hfrequency observed).sub
      (hcharge (iteratedQuadraticFreeCharge active))).sub
        (measurable_const.mul
          (hfrequency (iteratedQuadraticFirstPicardMode active)))
  have hinner
      (active : IteratedQuadraticSecondPicardCharacterTerm N) :
      Measurable fun sample ↦
        iteratedQuadraticInnerMismatch (massSample sample) active := by
    unfold iteratedQuadraticInnerMismatch
      firstPicardCoordinateBranchMismatch
    exact measurable_const.mul
      (measurable_quadraticPhaseMismatch_of_mass_coordinates
        massSample hmass (iteratedQuadraticFirstPicardMode active)
          (iteratedQuadraticInnerEntry active).1)
  cases channel with
  | outer => exact houter term
  | inner => exact hinner term
  | total => exact (houter term).add (hinner term)
  | outerTwist => exact houter (flipIteratedQuadraticInnerBranch term)
  | innerTwist => exact hinner (flipIteratedQuadraticInnerBranch term)

/-- Global measurability of the actual two-mass `A2` mismatch chart. -/
theorem measurable_physlibIteratedA2PairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Measurable (physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term) := by
  exact measurable_iteratedA2MismatchChannelValue_of_mass_coordinates
    (twoSiteMassConfig fixed site₁ site₂)
    (fun site ↦
      (continuous_twoSiteMassConfig_mass fixed site₁ site₂ site).measurable)
    channel observed term

/-- A single uniform mass coordinate lies in the open support interval almost
surely.  This discharges the two clipped boundary points without pretending
that the global strict-derivative theorem covers them. -/
theorem massCoordinate_mem_openMassSupport_ae :
    ∀ᵐ mass ∂massCoordinateLaw, mass ∈ Ioo massLower massUpper := by
  have hlower : massCoordinateLaw ({massLower} : Set Real) = 0 :=
    massCoordinateLaw_absolutelyContinuous_volume (by simp)
  have hupper : massCoordinateLaw ({massUpper} : Set Real) = 0 :=
    massCoordinateLaw_absolutelyContinuous_volume (by simp)
  have hnotLower := measure_eq_zero_iff_ae_notMem.mp hlower
  have hnotUpper := measure_eq_zero_iff_ae_notMem.mp hupper
  filter_upwards [massCoordinate_mem_support_ae, hnotLower, hnotUpper]
    with mass hsupport hneLower hneUpper
  simp only [mem_singleton_iff] at hneLower hneUpper
  exact ⟨lt_of_le_of_ne hsupport.1 (Ne.symm hneLower),
    lt_of_le_of_ne hsupport.2 hneUpper⟩

/-- Generic two-coordinate Fubini wrapper around the sharp one-site
Jacobian pushforward estimate. -/
theorem pairMismatchSmallBall_le_integrated_badMass
    (chart : Real × Real → Real) (hchart : Measurable chart)
    (good : Real → Set Real)
    (hgood : ∀ first, MeasurableSet (good first))
    (derivative : Real → Real → (Real →L[Real] Real))
    (hderivative : ∀ first second, second ∈ good first →
      HasFDerivWithinAt (fun x ↦ chart (first, x))
        (derivative first second) (good first) second)
    (hinjective : ∀ first, InjOn (fun x ↦ chart (first, x)) (good first))
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ first second, second ∈ good first →
      jacLower ≤ |(derivative first second).det|)
    (delta : Real) :
    Measure.map chart iidMassPairLaw (Ioo (-delta) delta) ≤
      ∫⁻ first,
        (((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
            ENNReal.ofReal (2 * delta) +
          massCoordinateLaw (good first)ᶜ) ∂massCoordinateLaw := by
  let target : Set Real := Ioo (-delta) delta
  have htarget : MeasurableSet target := measurableSet_Ioo
  let event : Set (Real × Real) := chart ⁻¹' target
  have hevent : MeasurableSet event := htarget.preimage hchart
  rw [Measure.map_apply hchart htarget]
  change iidMassPairLaw event ≤ _
  rw [iidMassPairLaw, MeasureTheory.Measure.prod_apply hevent]
  apply lintegral_mono
  intro first
  let fiber : Real → Real := fun x ↦ chart (first, x)
  have hfiber : Measurable fiber :=
    hchart.comp (measurable_const.prodMk measurable_id)
  have hpreimage :
      massCoordinateLaw (Prod.mk first ⁻¹' event) =
        Measure.map fiber massCoordinateLaw target := by
    rw [Measure.map_apply hfiber htarget]
    rfl
  change massCoordinateLaw (Prod.mk first ⁻¹' event) ≤ _
  rw [hpreimage]
  simpa [target, fiber] using
    oneSiteMismatchSmallBall_le_sharp_add_badMass
      fiber hfiber (good first) (hgood first) (derivative first)
      (hderivative first) (hinjective first) hjacLower (hjac first) delta

/-- A global actual-fiber transversality certificate gives the sharp linear
pair-law small-ball estimate.  Strict differentiability comes from the
physical ordered-spectrum atlas; only regularity, injectivity, and the
uniform lower bound remain hypotheses. -/
theorem physlibIteratedA2PairMismatchSmallBall_of_globalTransversality
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
        fixed site₁ site₂ channel observed term (first, second)|)
    (delta : Real) :
    Measure.map
        (physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term)
        iidMassPairLaw (Ioo (-delta) delta) ≤
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
        ENNReal.ofReal (2 * delta) := by
  let openSupport : Set Real := Ioo massLower massUpper
  let good : Real → Set Real := fun first ↦
    if first ∈ openSupport then openSupport else ∅
  let derivative : Real → Real → (Real →L[Real] Real) :=
    fun first second ↦ ContinuousLinearMap.toSpanSingleton Real
      (physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second))
  have hgood : ∀ first, MeasurableSet (good first) := by
    intro first
    by_cases hfirst : first ∈ openSupport
    · rw [show good first = openSupport by simp [good, hfirst]]
      exact measurableSet_Ioo
    · simp [good, hfirst]
  have hderivative : ∀ first second, second ∈ good first →
      HasFDerivWithinAt
        (fun x ↦ physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term (first, x))
        (derivative first second) (good first) second := by
    intro first second hsecond
    have hfirst : first ∈ openSupport := by
      by_contra hnot
      simp [good, hnot] at hsecond
    have hsecondOpen : second ∈ openSupport := by
      simpa [good, hfirst] using hsecond
    have hstrict := hasStrictDerivAt_physlibIteratedA2PairMismatchFiber
      fixed hsite channel observed term
        (hregular first second hfirst hsecondOpen)
    exact hstrict.hasDerivAt.hasFDerivAt.hasFDerivWithinAt
  have hinjectiveGood : ∀ first, InjOn
      (fun x ↦ physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term (first, x))
      (good first) := by
    intro first
    by_cases hfirst : first ∈ openSupport
    · have hfirstSupport : first ∈ massSupport :=
        ⟨le_of_lt hfirst.1, le_of_lt hfirst.2⟩
      apply (hinjective first hfirstSupport).mono
      intro second hsecond
      have hsecondOpen : second ∈ openSupport := by
        simpa [good, hfirst] using hsecond
      exact ⟨le_of_lt hsecondOpen.1, le_of_lt hsecondOpen.2⟩
    · simp [good, hfirst]
  have hjacobian : ∀ first second, second ∈ good first →
      jacLower ≤ |(derivative first second).det| := by
    intro first second hsecond
    have hfirst : first ∈ openSupport := by
      by_contra hnot
      simp [good, hnot] at hsecond
    have hsecondOpen : second ∈ openSupport := by
      simpa [good, hfirst] using hsecond
    simpa [derivative] using hjac first second hfirst hsecondOpen
  have hbound := pairMismatchSmallBall_le_integrated_badMass
    (physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term)
    (measurable_physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term)
    good hgood derivative hderivative hinjectiveGood hjacLower hjacobian delta
  have hopenAE : ∀ᵐ mass ∂massCoordinateLaw, mass ∈ openSupport := by
    simpa [openSupport] using massCoordinate_mem_openMassSupport_ae
  have hopenNull : massCoordinateLaw openSupportᶜ = 0 :=
    MeasureTheory.ae_iff.mp hopenAE
  have hbadAE : ∀ᵐ first ∂massCoordinateLaw,
      massCoordinateLaw (good first)ᶜ = 0 := by
    filter_upwards [hopenAE] with first hfirst
    simp [good, hfirst, hopenNull]
  calc
    Measure.map
        (physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term)
        iidMassPairLaw (Ioo (-delta) delta) ≤
      ∫⁻ first,
        (((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
            ENNReal.ofReal (2 * delta) +
          massCoordinateLaw (good first)ᶜ) ∂massCoordinateLaw := hbound
    _ = ∫⁻ _first,
        ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
          ENNReal.ofReal (2 * delta) ∂massCoordinateLaw := by
      apply lintegral_congr_ae
      filter_upwards [hbadAE] with first hzero
      rw [hzero, add_zero]
    _ = ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
        ENNReal.ofReal (2 * delta) := by simp

end

end ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall
