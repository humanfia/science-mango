import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBall

/-!
# Consumer for the three-site ordinary outer-family nested small ball

This consumer exposes the exact inner mismatch, its deterministic gap, and
the outer/inner nested bad-event estimates.  No `total`-channel or microscopic
RPA conclusion is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization
namespace ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBallConsumer

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory
open scoped ENNReal

noncomputable section

theorem displayedInnerQuadraticPhase_exact
    (m : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    quadraticPhaseMismatch (modeFrequency m)
        (iteratedQuadraticFirstPicardMode
          (threeSiteOrdinaryOuterHistoryTerm index))
        (iteratedQuadraticInnerEntry
          (threeSiteOrdinaryOuterHistoryTerm index)).1 =
      -modeFrequency m firstPositivePhysicalModeThree :=
  threeSiteOrdinaryOuterHistory_innerQuadraticPhaseMismatch_eq m index

theorem displayedInnerMismatch_exact
    (m : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    iteratedQuadraticInnerMismatch m
        (threeSiteOrdinaryOuterHistoryTerm index) =
      threeSiteOuterHistoryMismatchSign
          (threeSiteOrdinaryOuterHistoryTerm index) *
        modeFrequency m firstPositivePhysicalModeThree :=
  threeSiteOrdinaryOuterHistory_innerMismatch_eq m index

theorem displayedInnerMismatch_abs_exact
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (triple : MassTriple) :
    |threeSiteOrdinaryOuterHistoryTripleInnerMismatch index triple| =
      threeSiteFirstPositiveFrequencyGap triple :=
  abs_threeSiteOrdinaryOuterHistoryTripleInnerMismatch_eq index triple

theorem displayedInnerGap_uniformFloor (triple : MassTriple) :
    (1 / 15 : Real) < threeSiteFirstPositiveFrequencyGap triple :=
  one_div_fifteen_lt_threeSiteFirstPositiveFrequencyGap triple

theorem displayedInnerFamily_allWidth
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent epsilon) ≤
      15 * ENNReal.ofReal epsilon :=
  iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_le
    hepsilon

theorem displayedInnerFamily_zeroAtom :
    iidMassTripleLaw
      (threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent 0) = 0 :=
  iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_zero

theorem displayedNestedBadEvent_bound
    {outerEpsilon innerEpsilon : Real}
    (houter : 0 ≤ outerEpsilon) (hinner : 0 ≤ innerEpsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedBadEvent
          outerEpsilon innerEpsilon) ≤
      840 * ENNReal.ofReal (outerEpsilon ^ ((3 : Real)⁻¹)) +
        15 * ENNReal.ofReal innerEpsilon :=
  iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNestedBadEvent_le
    houter hinner

theorem displayedNestedBadEvent_eq_outer_belowInnerFloor
    (outerEpsilon : Real) {innerEpsilon : Real}
    (hinner : innerEpsilon < 1 / 15) :
    threeSiteOrdinaryOuterHistoryNestedBadEvent
        outerEpsilon innerEpsilon =
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent outerEpsilon :=
  threeSiteOrdinaryOuterHistoryNestedBadEvent_eq_outer
    outerEpsilon hinner

theorem displayedNestedSexticBadEvent_sharp
    {g : Real} (hcutoff : sexticCouplingCutoff g < 1 / 15) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedSexticBadEvent g) ≤
      840 * ENNReal.ofReal (squareCouplingCutoff g) :=
  iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_le_sharp
    hcutoff

#print axioms displayedInnerQuadraticPhase_exact
#print axioms displayedInnerMismatch_exact
#print axioms displayedInnerMismatch_abs_exact
#print axioms displayedInnerGap_uniformFloor
#print axioms displayedInnerFamily_allWidth
#print axioms displayedInnerFamily_zeroAtom
#print axioms displayedNestedBadEvent_bound
#print axioms displayedNestedBadEvent_eq_outer_belowInnerFloor
#print axioms displayedNestedSexticBadEvent_sharp

end


end ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBallConsumer
end ArchonPhysicsConsumers.Thermalization
