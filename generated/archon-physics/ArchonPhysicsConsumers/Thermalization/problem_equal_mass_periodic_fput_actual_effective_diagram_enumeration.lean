import ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration

/-!
# Consumer endpoints for the actual-to-effective four-wave diagram interface

The endpoints below expose the finite bijection, active-diagram enumeration,
conjugate mismatch identification, and the exact distinction between the two
nested time orderings.  No kinetic or random-phase premise is introduced.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain

noncomputable section

theorem equalMassPeriodicFPUT_actualCubicFeedbackIndexSum_consumer
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ index : ActualCubicFeedbackIndex N,
        actualCubicFeedbackTerm N amplitude tau out index :=
  actualEffectiveCubicFourWaveSource_eq_feedbackIndexSum
    N amplitude tau out

theorem equalMassPeriodicFPUT_feedbackDiagramInjective_consumer
    {N : Nat} (out : ActualInteractionBranchMode N) :
    Function.Injective (feedbackToEffectiveDiagram out) :=
  feedbackToEffectiveDiagram_injective out

theorem equalMassPeriodicFPUT_activeFeedbackMapsToActiveDiagram_consumer
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    IsActiveEffectiveFourWaveDiagram
      (feedbackToEffectiveDiagram out index) :=
  feedbackToEffectiveDiagram_active out index hactive

theorem equalMassPeriodicFPUT_actualCubicActiveDiagramSum_consumer
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ diagram : ActiveFeedbackEffectiveDiagramImage N out,
        actualActiveEffectiveDiagramTerm N amplitude tau out diagram :=
  actualEffectiveCubicFourWaveSource_eq_activeEffectiveDiagramSum
    N amplitude tau out

theorem equalMassPeriodicFPUT_outerMismatchConjugation_consumer
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (houter : ActualQuadraticMomentumSupported out
      (feedbackOuterLeft index) (feedbackOuterRight index)) :
    phaseSignReal (actualBranchSign out) *
        outerThreeWaveMismatch (feedbackToEffectiveDiagram out index) =
      actualQuadraticMismatch N out
        (feedbackOuterLeft index) (feedbackOuterRight index) :=
  outputSign_mul_outerThreeWaveMismatch_eq_actual out index houter

theorem equalMassPeriodicFPUT_innerMismatchConjugation_consumer
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hinner : ActualQuadraticMomentumSupported (feedbackInsertedMode index)
      (feedbackInnerLeft index) (feedbackInnerRight index)) :
    phaseSignReal (actualBranchSign out) *
        innerHomologicalDivisor (feedbackToEffectiveDiagram out index) =
      actualQuadraticMismatch N (feedbackInsertedMode index)
        (feedbackInnerLeft index) (feedbackInnerRight index) :=
  outputSign_mul_innerHomologicalDivisor_eq_actual out index hinner

theorem equalMassPeriodicFPUT_totalMismatchConjugation_consumer
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    actualQuadraticMismatch N out
          (feedbackOuterLeft index) (feedbackOuterRight index) +
        actualQuadraticMismatch N (feedbackInsertedMode index)
          (feedbackInnerLeft index) (feedbackInnerRight index) =
      phaseSignReal (actualBranchSign out) *
        totalFourWaveMismatch (feedbackToEffectiveDiagram out index) :=
  actualOuter_add_innerMismatch_eq_outputSign_mul_totalFourWaveMismatch
    out index hactive

theorem equalMassPeriodicFPUT_rootedKernelSwappedNested_consumer
    {N : Nat} [NeZero N]
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index)
    (tau : Real) :
    HasDerivAt
      (nestedOscillatoryIntegral
        (phaseSignReal (actualBranchSign out) *
          innerHomologicalDivisor (feedbackToEffectiveDiagram out index))
        (phaseSignReal (actualBranchSign out) *
          outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)))
      (actualRootedFeedbackTimeKernel N tau out index) tau :=
  hasDerivAt_swappedNestedDiagramKernel out index hactive tau

theorem equalMassPeriodicFPUT_twoTimeOrderShuffle_consumer
    {N : Nat} [NeZero N] (tau : Real)
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    nestedOscillatoryIntegral
        (phaseSignReal (actualBranchSign out) *
          innerHomologicalDivisor (feedbackToEffectiveDiagram out index))
        (phaseSignReal (actualBranchSign out) *
          outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)) tau +
      nestedOscillatoryIntegral
        (phaseSignReal (actualBranchSign out) *
          outerThreeWaveMismatch (feedbackToEffectiveDiagram out index))
        (phaseSignReal (actualBranchSign out) *
          innerHomologicalDivisor (feedbackToEffectiveDiagram out index)) tau =
      oscillatoryIntegral
          (phaseSignReal (actualBranchSign out) *
            innerHomologicalDivisor (feedbackToEffectiveDiagram out index)) tau *
        oscillatoryIntegral
          (phaseSignReal (actualBranchSign out) *
            outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)) tau :=
  rooted_add_innerFirst_nestedDiagramKernel tau out index

#print axioms equalMassPeriodicFPUT_actualCubicFeedbackIndexSum_consumer
#print axioms equalMassPeriodicFPUT_feedbackDiagramInjective_consumer
#print axioms equalMassPeriodicFPUT_activeFeedbackMapsToActiveDiagram_consumer
#print axioms equalMassPeriodicFPUT_actualCubicActiveDiagramSum_consumer
#print axioms equalMassPeriodicFPUT_outerMismatchConjugation_consumer
#print axioms equalMassPeriodicFPUT_innerMismatchConjugation_consumer
#print axioms equalMassPeriodicFPUT_totalMismatchConjugation_consumer
#print axioms equalMassPeriodicFPUT_rootedKernelSwappedNested_consumer
#print axioms equalMassPeriodicFPUT_twoTimeOrderShuffle_consumer

end

end ArchonPhysicsConsumers.Thermalization
