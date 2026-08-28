import ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomPhaseMoments

noncomputable section

theorem binaryFPUTTree_leaf_count_consumer
    (tree : BinaryInteractionTree) :
    tree.leafCount = tree.order + 1 :=
  BinaryInteractionTree.leafCount_eq_order_add_one tree

theorem unmatchedBinaryFPUTCouple_haar_cancels_consumer
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (kernel : BinaryTreeCoefficientKernel Mode)
    (couple : BinaryInteractionTreeCouple Mode)
    (hunmatched : ¬ leafPhaseBalanced couple) :
    (∫ phase : UnitAddTorus Mode,
      (binaryTreeCoefficient kernel couple.1 *
          binaryTreeCharacter couple.1 phase) *
        starRingEnd Complex
          (binaryTreeCoefficient kernel couple.2 *
            binaryTreeCharacter couple.2 phase)
      ∂finitePhaseHaarLaw Mode) = 0 :=
  integral_weightedBinaryTreeCouple_eq_zero_of_unmatched
    kernel couple hunmatched

theorem actualFirstPicardTree_charge_mismatch_consumer
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    binaryTreePhaseCharge (quadraticPhaseBinaryTree observed term) =
        quadraticPhaseCharge term ∧
      binaryTreeFrequencyMismatch frequency
          (quadraticPhaseBinaryTree observed term) =
        quadraticPhaseMismatch frequency observed term :=
  ⟨binaryTreePhaseCharge_quadraticPhaseBinaryTree observed term,
    binaryTreeFrequencyMismatch_quadraticPhaseBinaryTree
      frequency observed term⟩

theorem actualSecondPicardTree_charge_mismatch_consumer
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    binaryTreePhaseCharge
        (iteratedQuadraticSecondPicardBinaryTree observed term) =
        iteratedQuadraticSecondPicardCharge term ∧
      phaseSignActReal (binaryPhaseSign (iteratedQuadraticInnerEntry term).2)
          (binaryTreeFrequencyMismatch (modeFrequency m)
            (quadraticPhaseBinaryTree
              (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term).1)) =
        iteratedQuadraticInnerMismatch m term :=
  ⟨binaryTreePhaseCharge_iteratedQuadraticSecondPicardBinaryTree
      observed term,
    signedInnerTreeMismatch_eq_iteratedQuadraticInnerMismatch m term⟩

#print axioms binaryFPUTTree_leaf_count_consumer
#print axioms unmatchedBinaryFPUTCouple_haar_cancels_consumer
#print axioms actualFirstPicardTree_charge_mismatch_consumer
#print axioms actualSecondPicardTree_charge_mismatch_consumer

end

end ArchonPhysicsConsumers.Thermalization
