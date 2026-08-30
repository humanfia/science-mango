import ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterFamilyNestedSmallBallBridge

/-!
# Consumer: canonical three-site outer/inner nested small balls

This consumer exposes the exact event transport and the inherited all-width
and sharp sextic-cutoff probability bounds.  The event uses the actual raw
outer and inner source-slot mismatches, but deliberately excludes the total
mismatch channel and any coefficient, complement, RPA, or kinetic claim.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterFamilyNestedSmallBallBridge
open ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterSmallBallBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Set

noncomputable section

/-- The actual canonical four-history nested bad event is exactly the
`MassTriple` event pulled back along the canonical mass triple. -/
theorem canonical_nested_event_is_mass_triple_preimage
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (outerEpsilon innerEpsilon : Real) :
    canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent
        entry slot outerEpsilon innerEpsilon =
      canonicalThreeSiteMassTriple ⁻¹'
        threeSiteOrdinaryOuterHistoryNestedBadEvent
          outerEpsilon innerEpsilon :=
  canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent_eq_preimage
    entry slot hobserved outerEpsilon innerEpsilon

/-- Exact probability transport to `iidMassTripleLaw`. -/
theorem canonical_nested_event_probability_exact
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (outerEpsilon innerEpsilon : Real) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent
          entry slot outerEpsilon innerEpsilon) =
      iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedBadEvent
          outerEpsilon innerEpsilon) :=
  canonicalProbability_threeSiteOrdinaryOuterHistoryNestedBadEvent_eq
    entry slot hobserved outerEpsilon innerEpsilon

/-- All-width outer cube-root plus inner linear probability bound. -/
theorem canonical_nested_event_probability_full_width
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    {outerEpsilon innerEpsilon : Real}
    (houter : 0 ≤ outerEpsilon) (hinner : 0 ≤ innerEpsilon) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent
          entry slot outerEpsilon innerEpsilon) ≤
      840 * ENNReal.ofReal (outerEpsilon ^ ((3 : Real)⁻¹)) +
        15 * ENNReal.ofReal innerEpsilon :=
  canonicalProbability_threeSiteOrdinaryOuterHistoryNestedBadEvent_le
    entry slot hobserved houter hinner

/-- For a sextic cutoff below `1/15`, the real canonical nested event retains
the sharp bound `840 * |g|^2`. -/
theorem canonical_nested_sextic_event_probability_sharp
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    {g : Real} (hcutoff : sexticCouplingCutoff g < 1 / 15) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryNestedSexticBadEvent
          entry slot g) ≤
      840 * ENNReal.ofReal (|g| ^ 2) :=
  canonicalProbability_threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_le_sharp
    entry slot hobserved hcutoff

#print axioms canonical_nested_event_is_mass_triple_preimage
#print axioms canonical_nested_event_probability_exact
#print axioms canonical_nested_event_probability_full_width
#print axioms canonical_nested_sextic_event_probability_sharp

end

end ArchonPhysicsConsumers.Thermalization
