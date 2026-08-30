import ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1

/-!
# Consumer: full-iid and qualitative-L1 closure of compact A2 fibre atlases

The consumer exposes three boundaries.  First, exact finite-volume
pair/complement reconstruction integrates every compact one-mass atlas over
the frozen environment and first selected mass.  Second, almost-everywhere
zero compact-bad mass gives an actual weighted RN `L1` certificate and the
fixed-volume qualitative kinetic limit.  Third, charge-matched total return
channels remain singular unit atoms and are retained rather than dispersed.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Consumer form of the raw full-iid compact-atlas estimate. -/
theorem problem_physlibIteratedA2_compactAtlas_fullIID_smallBall
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
  exact
    exists_atlasCard_physlibIteratedA2MismatchLaw_Ioo_le_lintegral_compactFiber
      ensemble hsite channel observed term K hK hKregular j₀ hj₀ hjac

/-- Consumer form of the fixed-volume weighted qualitative closure. -/
theorem problem_physlibIteratedA2_compactAtlas_weighted_qualitativeL1
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
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    tendsto_actualIteratedA2WeightedChannel_of_compactFiber_badMass_zero
      ensemble hsite channel weight hweightMeasurable hweight observed term
        K hK hKregular j₀ hj₀ hjac hbad

/-- Consumer audit of the charge-matched singular retained sector. -/
theorem problem_physlibIteratedA2_chargeMatchedTotal_singular_retained
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) :
    ¬ physlibIteratedA2MismatchLaw ensemble .total observed term ≪
      (volume : Measure Real) := by
  exact
    not_physlibIteratedA2ChargeMatchedTotalMismatchLaw_absolutelyContinuous_volume
      ensemble observed term hcharge

#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1.physlibIteratedA2MismatchLaw_apply_eq_lintegral_frozenPair
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1.exists_atlasCard_physlibIteratedA2MismatchLaw_Ioo_le_lintegral_compactFiber
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1.exists_atlasCard_physlibIteratedA2MismatchLaw_Ioo_le_uniformCost_add_lintegral_bad
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1.physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_compactFiber_badMass_zero
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1.actualIteratedA2WeightedChannelL1Certificate_of_compactFiber_badMass_zero
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1.tendsto_actualIteratedA2WeightedChannel_of_compactFiber_badMass_zero
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2CompactAtlasAnnealedL1.not_physlibIteratedA2ChargeMatchedTotalMismatchLaw_absolutelyContinuous_volume
#print axioms problem_physlibIteratedA2_compactAtlas_fullIID_smallBall
#print axioms problem_physlibIteratedA2_compactAtlas_weighted_qualitativeL1
#print axioms problem_physlibIteratedA2_chargeMatchedTotal_singular_retained

end

end ArchonPhysicsConsumers.Thermalization
