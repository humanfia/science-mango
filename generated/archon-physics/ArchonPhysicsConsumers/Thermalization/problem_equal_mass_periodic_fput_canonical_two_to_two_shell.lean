import ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell

/-!
# Consumer: canonical two-to-two shell and degenerate actual count

This file records the public contracts used by the four-wave interference
pipeline.  The old presentation is consumed only when explicitly supplied;
the complete degenerate count uses the wider actual `2 ↔ 2` sign sector.
-/

namespace ArchonPhysicsConsumers.Thermalization.EqualMassPeriodicFPUTCanonicalTwoToTwoShell

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
open ArchonPhysics.Lattice

noncomputable section

theorem presentation_forces_actual_twoToTwo_sector_contract
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    IsExternalTwoToTwoSignSector diagram :=
  externalTwoToTwoPresentation_isExternalTwoToTwoSignSector presentation

theorem presentation_canonical_shell_is_choice_independent_contract
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (left right : ExternalTwoToTwoPresentation diagram) :
    externalTwoToTwoPresentationCanonicalMomentumShell left =
      externalTwoToTwoPresentationCanonicalMomentumShell right :=
  externalTwoToTwoPresentationCanonicalMomentumShell_unique left right

theorem old_presentation_excludes_degeneracy_contract
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    Function.Injective (totalFourWaveModes diagram) :=
  externalTwoToTwoPresentation_externalModes_injective presentation

theorem presentation_differs_from_canonical_by_four_pair_swaps_contract
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    IsTwoToTwoLegPermutation
      (canonicalNondegenerateTwoToTwoLegs presentation)
      presentation.legs :=
  canonicalNondegenerateTwoToTwoLegs_isLegPermutation presentation

theorem supported_presentation_reduced_order_is_actual_permutation_contract
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram)
    (hsupported : IsTwoVertexMomentumSupported diagram) :
    reducedTwoToTwoExternalModes (outputMomentum diagram)
        (canonicalTwoToTwoFreePair diagram) =
      canonicalTwoToTwoExternalModes diagram :=
  externalTwoToTwoPresentation_reducedExternalModes_eq_actualPermutation
    presentation hsupported

theorem actual_degeneracy_is_exactly_four_graph_lines_contract
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsExternalTwoToTwoSignSector diagram) :
    ¬ Function.Injective (totalFourWaveModes diagram) ↔
      IsDegenerateTwoToTwoFreePair (outputMomentum diagram)
        (canonicalTwoToTwoFreePair diagram) :=
  externalModes_not_injective_iff_canonicalFreePair_degenerate
    diagram hsupported hsector

theorem complete_actual_degenerate_twoToTwo_count_contract
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputDegenerateTwoToTwoDiagram N output) ≤
      128 * N :=
  card_fixedOutputDegenerateTwoToTwoDiagram_le N output

theorem ambient_and_degenerate_orders_contract
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputSupportedEffectiveFourWaveDiagram N output) ≤
        32 * N ^ 2 ∧
      Fintype.card (FixedOutputDegenerateTwoToTwoDiagram N output) ≤
        128 * N :=
  ⟨card_fixedOutputSupportedEffectiveFourWaveDiagram_le N output,
    card_fixedOutputDegenerateTwoToTwoDiagram_le N output⟩

#print axioms presentation_forces_actual_twoToTwo_sector_contract
#print axioms presentation_canonical_shell_is_choice_independent_contract
#print axioms old_presentation_excludes_degeneracy_contract
#print axioms presentation_differs_from_canonical_by_four_pair_swaps_contract
#print axioms supported_presentation_reduced_order_is_actual_permutation_contract
#print axioms actual_degeneracy_is_exactly_four_graph_lines_contract
#print axioms complete_actual_degenerate_twoToTwo_count_contract
#print axioms ambient_and_degenerate_orders_contract
#print axioms ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell.card_fixedOutputDegenerateTwoToTwoDiagram_le

end


end ArchonPhysicsConsumers.Thermalization.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
