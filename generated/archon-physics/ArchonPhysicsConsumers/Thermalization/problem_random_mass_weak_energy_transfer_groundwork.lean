import ArchonPhysics.RandomMassWeakEnergyTransferGroundwork

/-!
# Consumer: centered weak-energy random-mass transfer input

This consumer packages the exact centered decomposition, elliptic invariant
form, and first two iid coefficient moments.  It makes no Lyapunov-exponent,
localization, or eigenfunction-correlator conclusion.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassWeakEnergyTransferGroundwork
open MeasureTheory ProbabilityTheory

noncomputable section

theorem frozen_iid_uniform_weakEnergy_transfer_local_input
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (lambda : Real) (hlambda_pos : 0 < lambda) (hlambda_four : lambda < 4)
    (i : Nat) :
    iIndepFun (iidCenteredTransferCoefficient ensemble lambda)
      ensemble.probability ∧
    (∫ omega, iidCenteredTransferCoefficient ensemble lambda i omega
      ∂(ensemble.probability)) = 0 ∧
    (∫ omega, iidCenteredTransferCoefficient ensemble lambda i omega ^ 2
      ∂(ensemble.probability)) = lambda ^ 2 / 75 ∧
    (∀ mass, andersonTransferMatrix lambda mass =
      meanTransferMatrix lambda +
        centeredTransferPerturbation lambda (centeredMass mass)) ∧
    (∀ state, meanInvariantQuadratic lambda
      (Matrix.mulVec (meanTransferMatrix lambda) state) =
        meanInvariantQuadratic lambda state) ∧
    (∀ state, state ≠ 0 → 0 < meanInvariantQuadratic lambda state) := by
  refine ⟨iidCenteredTransferCoefficient_iIndep ensemble lambda,
    ensemble_centeredTransferCoefficient_mean ensemble lambda i,
    ensemble_centeredTransferCoefficient_secondMoment ensemble lambda i,
    andersonTransferMatrix_centered_decomposition lambda,
    meanInvariantQuadratic_meanTransferMatrix_mulVec lambda, ?_⟩
  intro state hstate
  exact meanInvariantQuadratic_pos hlambda_pos hlambda_four hstate

#print axioms andersonTransferMatrix_centered_decomposition
#print axioms meanTransferMatrix_preserves_invariantForm
#print axioms frozen_iid_uniform_weakEnergy_transfer_local_input

end

end ArchonPhysicsConsumers.Thermalization
