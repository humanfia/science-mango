import ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterSmallBallBridge

/-!
# Consumer: canonical three-site selected raw-character small balls

This consumer exposes the deterministic identification of each of the four
selected ordinary outer raw-character mismatches, the exact canonical-to-
`MassTriple` probability transport for their union, and the inherited
cube-root small-ball estimate.

The observed source-slot mode is explicitly required to be the first
positive physical mode.  No estimate for the raw-character complement,
character cancellation, kinetic equation, or RPA is asserted here.
-/

open scoped ENNReal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterSmallBallBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- Consumer-facing pointwise identification of a selected raw-character
outer mismatch with its existing `MassTriple` chart. -/
theorem canonical_three_site_selected_raw_character_outer_mismatch_exact
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (omega : CanonicalSample) :
    canonicalQuadraticSecondPicardRawCharacterOuterMismatch entry slot
        (threeSiteOrdinaryOuterHistoryTerm index) omega =
      threeSiteOrdinaryOuterHistoryTripleMismatch index
        (canonicalThreeSiteMassTriple omega) :=
  canonicalRawCharacterOuterMismatch_eq_threeSiteTripleMismatch
    entry slot hobserved index omega

/-- The canonical probability of the selected four-history union is exactly
the established iid `MassTriple` probability. -/
theorem canonical_three_site_ordinary_outer_family_probability_exact
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (epsilon : Real) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
          entry slot epsilon) =
      iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon) :=
  canonicalProbability_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq
    entry slot hobserved epsilon

/-- The selected four-history canonical union inherits constant `840`, with
no fourfold union loss. -/
theorem canonical_three_site_ordinary_outer_family_small_ball
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
          entry slot epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) :=
  canonicalProbability_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_le
    entry slot hobserved hepsilon

#print axioms canonical_three_site_selected_raw_character_outer_mismatch_exact
#print axioms canonical_three_site_ordinary_outer_family_probability_exact
#print axioms canonical_three_site_ordinary_outer_family_small_ball

end
end ArchonPhysicsConsumers.Thermalization
