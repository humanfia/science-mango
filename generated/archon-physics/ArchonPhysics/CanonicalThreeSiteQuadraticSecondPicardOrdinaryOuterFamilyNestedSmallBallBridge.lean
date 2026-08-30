import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBall
import ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterSmallBallBridge

/-!
# Canonical three-site outer/inner nested small balls

For the four selected ordinary source-slot histories, this file defines the
canonical bad event directly from the raw second-Picard outer mismatch and the
actual inner mismatch evaluated at the canonical random mass configuration.
When the observed source-slot mode is the first positive physical mode, this
event is exactly the preimage of the established `MassTriple` nested event.

Consequently its probability is transported exactly to `iidMassTripleLaw`.
It inherits both the all-width outer-plus-inner bound and, below the fixed
inner spectral floor, the sharp sextic-cutoff bound `840 * |g|^2`.

Only the separately displayed outer and inner gaps are controlled.  No total
mismatch, character coefficient, complement estimate, RPA, or kinetic claim
is made here.
-/

namespace ArchonPhysics
namespace CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterFamilyNestedSmallBallBridge

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterSmallBallBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory ProbabilityTheory Set

noncomputable section

/-! ## Pointwise canonical-to-triple inner bridge -/

/-- Reconstructing the canonical three-site mass configuration from its
`MassTriple` leaves the actual inner mismatch unchanged. -/
theorem canonicalInnerMismatch_eq_threeSiteTripleInnerMismatch
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (omega : CanonicalSample) :
    iteratedQuadraticInnerMismatch (canonicalMass (N := 3) omega)
        (threeSiteOrdinaryOuterHistoryTerm index) =
      threeSiteOrdinaryOuterHistoryTripleInnerMismatch index
        (canonicalThreeSiteMassTriple omega) := by
  unfold threeSiteOrdinaryOuterHistoryTripleInnerMismatch
  rw [threeSiteOuterTripleMassConfig_canonicalThreeSiteMassTriple_eq]

/-! ## The real canonical outer/inner event -/

/-- Canonical four-history nested bad event.  Both displayed mismatch
expressions are the actual source-slot quantities at the canonical mass
configuration; the `total` mismatch channel is deliberately absent. -/
def canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I) (outerEpsilon innerEpsilon : Real) : Set CanonicalSample :=
  {omega |
    (∃ index : ThreeSiteOrdinaryOuterHistoryIndex,
      |canonicalQuadraticSecondPicardRawCharacterOuterMismatch
        entry slot (threeSiteOrdinaryOuterHistoryTerm index) omega| ≤
          outerEpsilon) ∨
    ∃ index : ThreeSiteOrdinaryOuterHistoryIndex,
      |iteratedQuadraticInnerMismatch (canonicalMass (N := 3) omega)
        (threeSiteOrdinaryOuterHistoryTerm index)| ≤ innerEpsilon}

/-- Under the observed-mode identification, the real canonical nested event
is exactly the preimage of the established `MassTriple` nested event. -/
theorem canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent_eq_preimage
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (outerEpsilon innerEpsilon : Real) :
    canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent
        entry slot outerEpsilon innerEpsilon =
      canonicalThreeSiteMassTriple ⁻¹'
        threeSiteOrdinaryOuterHistoryNestedBadEvent
          outerEpsilon innerEpsilon := by
  ext omega
  change
    ((∃ index : ThreeSiteOrdinaryOuterHistoryIndex,
        |canonicalQuadraticSecondPicardRawCharacterOuterMismatch
          entry slot (threeSiteOrdinaryOuterHistoryTerm index) omega| ≤
            outerEpsilon) ∨
      ∃ index : ThreeSiteOrdinaryOuterHistoryIndex,
        |iteratedQuadraticInnerMismatch (canonicalMass (N := 3) omega)
          (threeSiteOrdinaryOuterHistoryTerm index)| ≤ innerEpsilon) ↔
      canonicalThreeSiteMassTriple omega ∈
        threeSiteOrdinaryOuterHistoryNestedBadEvent
          outerEpsilon innerEpsilon
  unfold threeSiteOrdinaryOuterHistoryNestedBadEvent
    threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
    threeSiteOrdinaryOuterHistoryNearMismatchEvent
    threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent
    threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent
  simp only [mem_union, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro (⟨index, hindex⟩ | ⟨index, hindex⟩)
    · left
      refine ⟨index, ?_⟩
      rwa [← canonicalRawCharacterOuterMismatch_eq_threeSiteTripleMismatch
        entry slot hobserved index omega]
    · right
      refine ⟨index, ?_⟩
      rwa [← canonicalInnerMismatch_eq_threeSiteTripleInnerMismatch
        index omega]
  · rintro (⟨index, hindex⟩ | ⟨index, hindex⟩)
    · left
      refine ⟨index, ?_⟩
      rwa [canonicalRawCharacterOuterMismatch_eq_threeSiteTripleMismatch
        entry slot hobserved index omega]
    · right
      refine ⟨index, ?_⟩
      rwa [canonicalInnerMismatch_eq_threeSiteTripleInnerMismatch index omega]

theorem measurableSet_canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (outerEpsilon innerEpsilon : Real) :
    MeasurableSet
      (canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent
        entry slot outerEpsilon innerEpsilon) := by
  rw [canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent_eq_preimage
    entry slot hobserved outerEpsilon innerEpsilon]
  exact (measurableSet_threeSiteOrdinaryOuterHistoryNestedBadEvent
    outerEpsilon innerEpsilon).preimage measurable_canonicalThreeSiteMassTriple

/-! ## Exact probability transport and quantitative endpoints -/

/-- Exact transport of the real canonical event to the iid `MassTriple` law. -/
theorem canonicalProbability_threeSiteOrdinaryOuterHistoryNestedBadEvent_eq
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
          outerEpsilon innerEpsilon) := by
  rw [canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent_eq_preimage
    entry slot hobserved outerEpsilon innerEpsilon]
  exact canonicalThreeSiteMassTriple_hasLaw.measure_eq
    (p := fun triple ↦ triple ∈
      threeSiteOrdinaryOuterHistoryNestedBadEvent
        outerEpsilon innerEpsilon)
    (measurableSet_threeSiteOrdinaryOuterHistoryNestedBadEvent
      outerEpsilon innerEpsilon)

/-- The canonical event inherits the all-width outer cube-root plus inner
linear bound. -/
theorem canonicalProbability_threeSiteOrdinaryOuterHistoryNestedBadEvent_le
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
        15 * ENNReal.ofReal innerEpsilon := by
  rw [canonicalProbability_threeSiteOrdinaryOuterHistoryNestedBadEvent_eq
    entry slot hobserved outerEpsilon innerEpsilon]
  exact iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNestedBadEvent_le
    houter hinner

/-- Equal sextic cutoffs for the actual canonical outer and inner gaps. -/
def canonicalThreeSiteOrdinaryOuterHistoryNestedSexticBadEvent
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I) (g : Real) : Set CanonicalSample :=
  canonicalThreeSiteOrdinaryOuterHistoryNestedBadEvent entry slot
    (sexticCouplingCutoff g) (sexticCouplingCutoff g)

/-- Below the deterministic inner gap, the actual canonical nested event has
the sharp outer-family probability bound `840 * |g|^2`. -/
theorem canonicalProbability_threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_le_sharp
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    {g : Real} (hcutoff : sexticCouplingCutoff g < 1 / 15) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryNestedSexticBadEvent
          entry slot g) ≤
      840 * ENNReal.ofReal (|g| ^ 2) := by
  unfold canonicalThreeSiteOrdinaryOuterHistoryNestedSexticBadEvent
  rw [canonicalProbability_threeSiteOrdinaryOuterHistoryNestedBadEvent_eq
    entry slot hobserved (sexticCouplingCutoff g) (sexticCouplingCutoff g)]
  simpa [threeSiteOrdinaryOuterHistoryNestedSexticBadEvent,
    squareCouplingCutoff] using
    iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_le_sharp
      hcutoff

end

end CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterFamilyNestedSmallBallBridge
end ArchonPhysics
