import ArchonPhysics.ActualThreeSiteQuadraticSecondPicardSourceSlotCharacterBridge
import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
import ArchonPhysics.IIDMassTripleMarginal

/-!
# Canonical three-site ordinary outer-character small balls

This module specializes the actual quadratic second-Picard source-slot
character bridge to the observed first positive physical mode.  For each of
the four displayed ordinary outer histories, the outer mismatch appearing in
the raw character carrier is identified pointwise with the corresponding
`MassTriple` mismatch chart.

The canonical iid masses at sites `0`, `1`, and `2` have exactly the existing
`iidMassTripleLaw`.  Hence both each selected-history near event and their
four-history union have exactly the probabilities of the established
`MassTriple` events and inherit the `840 * epsilon^(1/3)` bound.

No assertion is made about the raw-character complement, character
coefficients, cancellation between characters, a kinetic equation, or RPA.
-/

namespace ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterSmallBallBridge

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeSiteQuadraticSecondPicardSourceSlotCharacterBridge
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.IIDMassTripleMarginal
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory ProbabilityTheory Set

noncomputable section

/-! ## The canonical iid mass triple -/

/-- The three physical mass coordinates of the canonical three-site sample,
in the nested convention used by `MassTriple`. -/
noncomputable def canonicalThreeSiteMassTriple
    (omega : CanonicalSample) : MassTriple :=
  ensembleMassTriple canonicalIIDMassPhaseEnsemble 0 1 2 omega

theorem measurable_canonicalThreeSiteMassTriple :
    Measurable canonicalThreeSiteMassTriple := by
  exact measurable_ensembleMassTriple canonicalIIDMassPhaseEnsemble 0 1 2

/-- The canonical three-site mass triple has exactly the iid triple law used
by the quantitative mismatch theorem. -/
theorem canonicalThreeSiteMassTriple_hasLaw :
    HasLaw canonicalThreeSiteMassTriple iidMassTripleLaw
      canonicalIIDMassPhaseEnsemble.probability := by
  exact ensembleMassTriple_hasLaw canonicalIIDMassPhaseEnsemble
    (by norm_num) (by norm_num) (by norm_num)

/-- Reconstructing all three sites from the canonical triple gives the
canonical positive-mass configuration pointwise. -/
theorem threeSiteOuterTripleMassConfig_canonicalThreeSiteMassTriple_eq
    (omega : CanonicalSample) :
    threeSiteOuterTripleMassConfig (canonicalThreeSiteMassTriple omega) =
      canonicalMass (N := 3) omega := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  obtain ⟨index, rfl⟩ := (ZMod.finEquiv 3).surjective site
  change
    (threeSiteOuterTripleMassConfig
      (canonicalThreeSiteMassTriple omega)).mass (ZMod.finEquiv 3 index) =
      canonicalIIDMassPhaseEnsemble.mass index.val omega
  fin_cases index <;>
    simp (config := { decide := true })
      [threeSiteOuterTripleMassConfig, threeMassSiteConfig,
      canonicalThreeSiteMassTriple, ensembleMassTriple,
      clippedMass_eq_self
        (canonicalIIDMassPhaseEnsemble.mass_mem_support _ omega)]

/-! ## The outer mismatch carried by one selected raw character -/

/-- The outer mismatch used in the exponential carrier of one canonical raw
source-slot character. -/
noncomputable def canonicalQuadraticSecondPicardRawCharacterOuterMismatch
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I) (term : IteratedQuadraticSecondPicardCharacterTerm 3)
    (omega : CanonicalSample) : Real :=
  iteratedQuadraticOuterMismatch (canonicalMass (N := 3) omega)
    (orderedPhyslibModeIndex (entry slot).2) term

/-- Once the source-slot observed mode is the first positive physical mode,
each of the four selected raw carrier mismatches is exactly its established
`MassTriple` mismatch, including the original/conjugate branch sign. -/
theorem canonicalRawCharacterOuterMismatch_eq_threeSiteTripleMismatch
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (omega : CanonicalSample) :
    canonicalQuadraticSecondPicardRawCharacterOuterMismatch entry slot
        (threeSiteOrdinaryOuterHistoryTerm index) omega =
      threeSiteOrdinaryOuterHistoryTripleMismatch index
        (canonicalThreeSiteMassTriple omega) := by
  unfold canonicalQuadraticSecondPicardRawCharacterOuterMismatch
  rw [hobserved]
  rw [← threeSiteOuterTripleMassConfig_canonicalThreeSiteMassTriple_eq omega]
  unfold threeSiteOrdinaryOuterHistoryTripleMismatch
    physlibIteratedA2PairMismatchChart
  simp only [IteratedA2MismatchChannel.value]
  have hconfig := frozenFiberThreeSiteMassConfig_outerBackground_eq
    (canonicalThreeSiteMassTriple omega)
  unfold frozenFiberThreeSiteMassConfig at hconfig
  rw [hconfig]

/-! ## Exact event transport and inherited cube-root rates -/

/-- Canonical near event for one selected ordinary raw character. -/
def canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I) (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (epsilon : Real) : Set CanonicalSample :=
  {omega |
    |canonicalQuadraticSecondPicardRawCharacterOuterMismatch
      entry slot (threeSiteOrdinaryOuterHistoryTerm index) omega| ≤ epsilon}

/-- The canonical one-history event is exactly the preimage of the
corresponding `MassTriple` event. -/
theorem canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent_eq_preimage
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent
        entry slot index epsilon =
      canonicalThreeSiteMassTriple ⁻¹'
        threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon := by
  ext omega
  change
    |canonicalQuadraticSecondPicardRawCharacterOuterMismatch entry slot
      (threeSiteOrdinaryOuterHistoryTerm index) omega| ≤ epsilon ↔
    |threeSiteOrdinaryOuterHistoryTripleMismatch index
      (canonicalThreeSiteMassTriple omega)| ≤ epsilon
  rw [canonicalRawCharacterOuterMismatch_eq_threeSiteTripleMismatch
    entry slot hobserved index omega]

theorem measurableSet_canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    MeasurableSet
      (canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent
        entry slot index epsilon) := by
  rw [canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent_eq_preimage
    entry slot hobserved index epsilon]
  exact (measurableSet_threeSiteOrdinaryOuterHistoryNearMismatchEvent
    index epsilon).preimage measurable_canonicalThreeSiteMassTriple

/-- Exact probability transport for each of the four selected histories. -/
theorem canonicalProbability_threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent
          entry slot index epsilon) =
      iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon) := by
  rw [canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent_eq_preimage
    entry slot hobserved index epsilon]
  exact canonicalThreeSiteMassTriple_hasLaw.measure_eq
    (p := fun triple => triple ∈
      threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon)
    (measurableSet_threeSiteOrdinaryOuterHistoryNearMismatchEvent
      index epsilon)

/-- The canonical one-history event inherits the exact displayed cube-root
bound from its `MassTriple` law. -/
theorem canonicalProbability_threeSiteOrdinaryOuterHistoryNearMismatchEvent_le
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent
          entry slot index epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) := by
  rw [canonicalProbability_threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq
    entry slot hobserved index epsilon]
  exact iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNearMismatchEvent_le
    index hepsilon

/-- Canonical union of the four selected ordinary outer-history events. -/
def canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I) (epsilon : Real) : Set CanonicalSample :=
  ⋃ index : ThreeSiteOrdinaryOuterHistoryIndex,
    canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent
      entry slot index epsilon

/-- The four-history canonical union is exactly the preimage of the existing
four-history `MassTriple` union. -/
theorem canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq_preimage
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (epsilon : Real) :
    canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
        entry slot epsilon =
      canonicalThreeSiteMassTriple ⁻¹'
        threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon := by
  ext omega
  constructor
  · intro homega
    obtain ⟨index, hindex⟩ := mem_iUnion.mp homega
    change canonicalThreeSiteMassTriple omega ∈
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon
    apply mem_iUnion.mpr
    refine ⟨index, ?_⟩
    have heq := congrArg (fun event : Set CanonicalSample => omega ∈ event)
      (canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent_eq_preimage
        entry slot hobserved index epsilon)
    exact heq.mp hindex
  · intro homega
    change canonicalThreeSiteMassTriple omega ∈
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon at homega
    obtain ⟨index, hindex⟩ := mem_iUnion.mp homega
    apply mem_iUnion.mpr
    refine ⟨index, ?_⟩
    have heq := congrArg (fun event : Set CanonicalSample => omega ∈ event)
      (canonicalThreeSiteOrdinaryOuterHistoryNearMismatchEvent_eq_preimage
        entry slot hobserved index epsilon)
    exact heq.mpr hindex

/-- Exact probability transport for the union of all four displayed raw
characters. -/
theorem canonicalProbability_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    (epsilon : Real) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
          entry slot epsilon) =
      iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon) := by
  rw [canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq_preimage
    entry slot hobserved epsilon]
  exact canonicalThreeSiteMassTriple_hasLaw.measure_eq
    (p := fun triple => triple ∈
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon)
    (measurableSet_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
      epsilon)

/-- The canonical four-history union retains constant `840`, with no union
factor, because the four absolute events are already equal on `MassTriple`. -/
theorem canonicalProbability_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_le
    {I : Type*} (entry : I → PhaseSign × OrderedModeIndex 3)
    (slot : I)
    (hobserved : orderedPhyslibModeIndex (entry slot).2 =
      firstPositivePhysicalModeThree)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    canonicalIIDMassPhaseEnsemble.probability
        (canonicalThreeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
          entry slot epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) := by
  rw [canonicalProbability_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq
    entry slot hobserved epsilon]
  exact
    iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_le
      hepsilon

end
end ArchonPhysics.CanonicalThreeSiteQuadraticSecondPicardOrdinaryOuterSmallBallBridge
