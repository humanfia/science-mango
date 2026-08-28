import ArchonPhysics.EqualMassPeriodicFPUTActualRootedEffectiveCoefficient

/-!
# Consumer endpoints for the actual normalized rooted coefficient

These endpoints expose the literal coefficient factorization, the reachable
active-diagram sum, the correct swapped time primitive, and the exact
compatibility criterion with the older coefficient.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTActualRootedEffectiveCoefficient
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain

noncomputable section

theorem equalMassPeriodicFPUT_actualRootedCoefficientFactorization_consumer
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    actualCubicFeedbackTerm N amplitude tau out index =
      actualRootedFourWaveCoefficient N 1 tau out index *
        actualFeedbackAmplitudeMonomial amplitude index :=
  actualCubicFeedbackTerm_eq_rootedCoefficient_mul_monomial
    N amplitude tau out index

theorem equalMassPeriodicFPUT_actualSourceReachableCoefficientSum_consumer
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ diagram : ActiveFeedbackEffectiveDiagramImage N out,
        reachableActualRootedFourWaveCoefficient N 1 tau out diagram *
          reachableActualFeedbackAmplitudeMonomial N amplitude out diagram :=
  actualEffectiveCubicFourWaveSource_eq_reachableRootedCoefficientSum
    N amplitude tau out

theorem equalMassPeriodicFPUT_alphaSquaredActualSourceReachableSum_consumer
    (N : Nat) [NeZero N] (alpha : Real)
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    (alpha : Complex) ^ 2 *
        actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ diagram : ActiveFeedbackEffectiveDiagramImage N out,
        reachableActualRootedFourWaveCoefficient N alpha tau out diagram *
          reachableActualFeedbackAmplitudeMonomial N amplitude out diagram :=
  alpha_sq_mul_actualEffectiveCubicFourWaveSource_eq_reachableSum
    N alpha amplitude tau out

theorem equalMassPeriodicFPUT_actualSwappedCoefficientDerivative_consumer
    (N : Nat) [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) (tau : Real) :
    HasDerivAt
      (reachableActualSwappedNestedFourWaveCoefficient N alpha · out diagram)
      (reachableActualRootedFourWaveCoefficient N alpha tau out diagram) tau :=
  hasDerivAt_reachableActualSwappedNestedFourWaveCoefficient
    N alpha out diagram tau

theorem equalMassPeriodicFPUT_actualSwappedDiagramExtraction_consumer
    {N : Nat} [NeZero N] (alpha : Real) (tau : Real)
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    actualSwappedNestedFourWaveCoefficient N alpha tau out index =
      actualSwappedEffectiveFourWaveCoefficient N alpha out index *
          oscillatoryIntegral
            (phaseSignReal (actualBranchSign out) *
              totalFourWaveMismatch
                (feedbackToEffectiveDiagram out index)) tau -
        actualSwappedBoundaryFourWaveCoefficient N alpha out index *
          oscillatoryIntegral
            (phaseSignReal (actualBranchSign out) *
              innerHomologicalDivisor
                (feedbackToEffectiveDiagram out index)) tau :=
  actualSwappedNestedFourWaveCoefficient_eq_diagramEffective_sub_boundary
    alpha tau out index hactive

theorem equalMassPeriodicFPUT_actualOldCoefficientCompatibility_iff_consumer
    (N : Nat) [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (index : ActiveActualCubicFeedback N out) :
    actualSwappedEffectiveFourWaveCoefficient N alpha out index.1 =
        effectiveFourWaveCoefficient N alpha
          (feedbackToEffectiveDiagram out index.1) ↔
      ActualOldEffectiveCoefficientCompatibility N alpha out index :=
  actualSwappedEffectiveFourWaveCoefficient_eq_old_iff
    N alpha out index

theorem equalMassPeriodicFPUT_actualOldCoefficientComponents_consumer
    (N : Nat) [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (index : ActiveActualCubicFeedback N out)
    (hnumerator : actualRootedTwoVertexNumerator N alpha out index.1 =
      twoVertexNumerator N alpha (feedbackToEffectiveDiagram out index.1))
    (hdivisor : actualQuadraticMismatch N out
        (feedbackOuterLeft index.1) (feedbackOuterRight index.1) =
      innerHomologicalDivisor (feedbackToEffectiveDiagram out index.1)) :
    actualSwappedEffectiveFourWaveCoefficient N alpha out index.1 =
      effectiveFourWaveCoefficient N alpha
        (feedbackToEffectiveDiagram out index.1) :=
  actualSwappedEffectiveFourWaveCoefficient_eq_old_of_components
    N alpha out index hnumerator hdivisor

#print axioms equalMassPeriodicFPUT_actualRootedCoefficientFactorization_consumer
#print axioms equalMassPeriodicFPUT_actualSourceReachableCoefficientSum_consumer
#print axioms equalMassPeriodicFPUT_alphaSquaredActualSourceReachableSum_consumer
#print axioms equalMassPeriodicFPUT_actualSwappedCoefficientDerivative_consumer
#print axioms equalMassPeriodicFPUT_actualSwappedDiagramExtraction_consumer
#print axioms equalMassPeriodicFPUT_actualOldCoefficientCompatibility_iff_consumer
#print axioms equalMassPeriodicFPUT_actualOldCoefficientComponents_consumer

end

end ArchonPhysicsConsumers.Thermalization
