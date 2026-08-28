import ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.FiniteNestedNormalFormExtraction
open ArchonPhysics.Lattice
open ArchonPhysics.NonresonantOscillatoryGain

noncomputable section

theorem effectiveFourWaveDiagram_totalMomentum_consumer
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram) :
    totalFourWaveMomentum diagram = 0 :=
  totalFourWaveMomentum_eq_zero_of_supported diagram hsupported

theorem effectiveFourWaveDiagram_totalMismatch_consumer
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    outerThreeWaveMismatch diagram + innerHomologicalDivisor diagram =
      totalFourWaveMismatch diagram :=
  outer_add_innerHomologicalDivisor_eq_totalFourWaveMismatch diagram

theorem activeEffectiveFourWave_innerDivisor_consumer
    {N : Nat} [NeZero N] (diagram : ActiveEffectiveFourWaveDiagram N) :
    innerHomologicalDivisor diagram.1 ≠ 0 ∧
      finiteNonzeroMomentumThreeWaveGap N ≤
        |innerHomologicalDivisor diagram.1| :=
  ⟨innerHomologicalDivisor_ne_zero diagram,
    finiteThreeWaveGap_le_abs_innerHomologicalDivisor diagram⟩

theorem effectiveFourWaveCoefficient_alphaSquare_consumer
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) :
    effectiveFourWaveCoefficient N alpha diagram =
      (alpha : Complex) ^ 2 * effectiveFourWaveCoefficient N 1 diagram :=
  effectiveFourWaveCoefficient_eq_alpha_sq_mul_unit N alpha diagram

theorem effectiveFourWaveCoefficient_zeroMode_consumer
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hzero : ∃ slot : Fin 4, totalFourWaveModes diagram slot = 0) :
    effectiveFourWaveCoefficient N alpha diagram = 0 :=
  effectiveFourWaveCoefficient_eq_zero_of_external_zero
    N alpha diagram hsupported hzero

theorem activeNestedPicard_effectiveFourWave_exactSplit_consumer
    (N : Nat) [NeZero N] (alpha : Real) (time : Real) :
    finiteNestedPicardSum
        (activeTwoVertexNumerator N alpha)
        (activeOuterThreeWaveMismatch N)
        (activeInnerHomologicalDivisor N) time =
      (∑ diagram : ActiveEffectiveFourWaveDiagram N,
        effectiveFourWaveCoefficient N alpha diagram.1 *
          oscillatoryIntegral (totalFourWaveMismatch diagram.1) time) -
        finiteNormalFormBoundarySum
          (activeTwoVertexNumerator N alpha)
          (activeOuterThreeWaveMismatch N)
          (activeInnerHomologicalDivisor N) time :=
  activeNestedPicardSum_eq_fourWaveVertexSum_sub_boundary N alpha time

theorem activeEffectiveFourWave_boundaryGapBound_consumer
    (N : Nat) [NeZero N] (alpha : Real) (time : Real) :
    ‖finiteNormalFormBoundarySum
        (activeTwoVertexNumerator N alpha)
        (activeOuterThreeWaveMismatch N)
        (activeInnerHomologicalDivisor N) time‖ ≤
      (|time| / finiteNonzeroMomentumThreeWaveGap N) *
        ∑ diagram : ActiveEffectiveFourWaveDiagram N,
          ‖activeTwoVertexNumerator N alpha diagram‖ :=
  norm_activeFiniteNormalFormBoundarySum_le_fixedThreeWaveGap N alpha time

#print axioms effectiveFourWaveDiagram_totalMomentum_consumer
#print axioms effectiveFourWaveDiagram_totalMismatch_consumer
#print axioms activeEffectiveFourWave_innerDivisor_consumer
#print axioms effectiveFourWaveCoefficient_alphaSquare_consumer
#print axioms effectiveFourWaveCoefficient_zeroMode_consumer
#print axioms activeNestedPicard_effectiveFourWave_exactSplit_consumer
#print axioms activeEffectiveFourWave_boundaryGapBound_consumer

end

end ArchonPhysicsConsumers.Thermalization
