import ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere
import ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure

/-!
# Consumer: four-site opposite canonical resultant almost everywhere

The exact algebraic factorization discharges the canonical-resultant premise
for the opposite pair `0,2` under its actual iid frozen-complement law.  The
last theorem records the resulting application of the generic
single-frequency closure.  Its channel-specific mismatch identity,
non-acoustic mode, nonzero sign, and acoustic-avoidance assumptions remain
explicit; this module does not prove them automatically.
-/

namespace ArchonPhysicsConsumers.Thermalization
namespace FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiber
open ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open Filter MeasureTheory

noncomputable section

/-- The two frozen inverse masses differ almost everywhere under the exact
four-site complement law. -/
example :
    ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement
          (0 : Lattice.Site 4) (2 : Lattice.Site 4))),
      frozenInverseWeightOne
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest) ≠
        frozenInverseWeightThree
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest) :=
  frozenInverseWeights_ne_ae

/-- Hence the canonical positive-characteristic Jacobian resultant is a
nonzero polynomial for almost every frozen complement. -/
example :
    ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement
          (0 : Lattice.Site 4) (2 : Lattice.Site 4))),
      twoSitePositiveCharacteristicJacobianResultant
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) ≠ 0 :=
  twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_ae

/-- Four-site specialization of the generic single-frequency canonical
closure.  Only its frozen-resultant premise is discharged here; the displayed
channel and acoustic hypotheses are genuine remaining assumptions. -/
theorem physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_fourSiteOpposite
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site 4)
    (term : IteratedQuadraticSecondPicardCharacterTerm 4)
    (mode : Fin (Fintype.card (Lattice.Site 4)))
    (hmode : mode ≠ lastOrderedIndex)
    (sign : Real) (hsign : sign ≠ 0)
    (hmismatch : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement
          (0 : Lattice.Site 4) (2 : Lattice.Site 4))),
      physlibIteratedA2PairMismatchChart
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
          (0 : Lattice.Site 4) (2 : Lattice.Site 4)
          channel observed term =
        fun pair ↦ sign * orderedModeFrequency
          (twoSiteHarmonicHermitian
            (finitePairEnvironmentPositiveMassConfig
              (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair) mode)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    physlibIteratedA2MismatchLaw ensemble channel observed term ≪
      (volume : Measure Real) := by
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble (0 : Lattice.Site 4) (2 : Lattice.Site 4) (by decide)
      channel observed term mode hmode sign hsign hmismatch
      twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_ae
      havoid

end

end FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere
end ArchonPhysicsConsumers.Thermalization
