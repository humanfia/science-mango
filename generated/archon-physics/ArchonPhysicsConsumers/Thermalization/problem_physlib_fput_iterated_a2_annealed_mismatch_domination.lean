import ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination

/-!
# Consumer: actual iterated-A2 mismatch domination

This consumer checks the global-transversality conversion at pair and iid
ensemble level.  Its assumptions are the unresolved model-facing content:
regular simple-positive spectrum on the open mass square, full-support fiber
injectivity, and one Jacobian lower bound uniform in the frozen environment.

Charge-matched total return channels are checked separately: their fiber is
not injective and their mismatch law has a unit atom at zero, so they cannot
be fed to the ordinary small-ball/Fourier-decay channel.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Pair-law form of the explicit density ceiling. -/
theorem consumer_iteratedA2_pairMismatchLaw_le_volume
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
        ArchonPhysics.TwoParameterSpectralAveragingAtlas.iidMassPairLaw ≤
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) •
        (volume : Measure Real) := by
  exact physlibIteratedA2PairMismatchMap_le_volume_of_globalTransversality
    fixed hsite channel observed term hregular hinjective hjacLower hjac

/-- Exact iid frozen-rest lift, including the absolute-continuity endpoint
needed by qualitative `L1` Fourier grounding. -/
theorem consumer_iteratedA2_ensembleMismatchLaw_domination_and_ac
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
          (volume : Measure Real) ∧
      physlibIteratedA2MismatchLaw ensemble channel observed term ≪
        (volume : Measure Real) := by
  exact ⟨
    physlibIteratedA2MismatchLaw_le_volume_of_uniform_globalTransversality
      ensemble site₁ site₂ hsite channel observed term hregular
        hinjective hjacLower hjac,
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_uniform_globalTransversality
      ensemble site₁ site₂ hsite channel observed term hregular
        hinjective hjacLower hjac⟩

/-- Consumer form of the exact resonant obstruction. -/
theorem consumer_iteratedA2_chargeMatchedTotal_obstruction
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term)
    {delta : Real} (hdelta : 0 < delta) :
    ¬ (∀ first, first ∈ massSupport → InjOn
        (fun second ↦ physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ .total observed term (first, second))
        massSupport) ∧
      physlibIteratedA2MismatchLaw ensemble .total observed term
        (Ioo (-delta) delta) = 1 := by
  exact ⟨
    not_globalFiberInjectivity_chargeMatchedTotal
      fixed site₁ site₂ observed term hcharge,
    physlibIteratedA2ChargeMatchedTotalMismatchLaw_Ioo_eq_one
      ensemble observed term hcharge hdelta⟩

#print axioms oneSiteMismatchMap_le_sharp_smul_volume_of_ae_fullGood
#print axioms pairMismatchMap_le_smul_volume_of_ae_fiberDomination
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall.physlibIteratedA2PairMismatchSmallBall_of_globalTransversality
#print axioms
  physlibIteratedA2PairMismatchMap_le_volume_of_globalTransversality
#print axioms
  physlibIteratedA2MismatchLaw_le_volume_of_uniform_globalTransversality
#print axioms
  physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_uniform_globalTransversality
#print axioms not_globalFiberInjectivity_chargeMatchedTotal
#print axioms physlibIteratedA2ChargeMatchedTotalMismatchLaw_Ioo_eq_one
#print axioms consumer_iteratedA2_pairMismatchLaw_le_volume
#print axioms consumer_iteratedA2_ensembleMismatchLaw_domination_and_ac
#print axioms consumer_iteratedA2_chargeMatchedTotal_obstruction

end

end ArchonPhysicsConsumers.Thermalization
