import ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory

/-!
# Consumer: a four-site opposite-pair single-frequency outer history

The concrete ordinary outer history has mismatch equal to the negative second
positive ordered frequency.  Its surviving sign and ordered mode are
nondegenerate, and every participating mode avoids the acoustic index.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

example (m : Lattice.PositiveMassConfig 4) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeFour
        fourSiteSingleFrequencyOuterTerm =
      -modeFrequency m secondPositivePhysicalModeFour :=
  fourSiteSingleFrequency_outerMismatch_eq m

example (fixed : Lattice.PositiveMassConfig 4) :
    physlibIteratedA2PairMismatchChart fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) .outer
        firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm =
      fun pair => fourSiteSingleFrequencyOuterSign * orderedModeFrequency
        (twoSiteHarmonicHermitian fixed
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
        fourSiteSingleFrequencyOrderedMode :=
  fourSiteOpposite_outerMismatchChart_eq_signedFrequency fixed

example : fourSiteSingleFrequencyOuterSign ≠ 0 :=
  fourSiteSingleFrequencyOuterSign_ne_zero

example : fourSiteSingleFrequencyOrderedMode ≠
    lastOrderedIndex (ι := Lattice.Site 4) :=
  fourSiteSingleFrequencyOrderedMode_ne_last

example :
    IteratedA2ChannelAvoidsAcoustic .outer firstPositivePhysicalModeFour
      fourSiteSingleFrequencyOuterTerm :=
  fourSiteSingleFrequencyOuter_avoidsAcoustic

#print axioms fourSiteSingleFrequency_outerMismatch_eq
#print axioms fourSiteOpposite_outerMismatchChart_eq_signedFrequency
#print axioms fourSiteSingleFrequencyOuter_avoidsAcoustic

end

end ArchonPhysicsConsumers.Thermalization
