import ArchonPhysics.PhyslibFPUTHigherOrderSourceDefectDecomposition

/-!
# Slot expansion of higher-order FPUT source-cluster defects

The mixed source/moment defects are still sums over every nonlinear source
slot of a cluster.  This module expands them exactly into ordinary weighted
factorization defects between one source-inserted block observable and the
opposite block observable.  It is the finite hierarchy form used by a garden
expansion: each derivative creates a finite family of higher-order
correlations, none of which is discarded by a pairwise RPA rule.
-/

namespace ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTHigherOrderSourceDefectDecomposition
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Weighted moment of an arbitrary complex observable on a finite ensemble. -/
def finiteWeightedObservableMoment
    (weight : Omega → Real) (observable : Omega → Complex) : Complex :=
  ∑ omega, (weight omega : Complex) * observable omega

/-- Failure of two arbitrary finite-ensemble observables to factorize. -/
def finiteWeightedObservableFactorizationDefect
    (weight : Omega → Real)
    (left right : Omega → Complex) : Complex :=
  finiteWeightedObservableMoment weight (fun omega ↦ left omega * right omega) -
    finiteWeightedObservableMoment weight left *
      finiteWeightedObservableMoment weight right

/-- One block with its displayed slot replaced by the nonlinear source. -/
def sourceInsertedBlockObservable
    (path source : Omega → I → Real → Complex)
    (block : Finset I) (slot : I) (time : Real) (omega : Omega) : Complex :=
  (∏ j ∈ block.erase slot, path omega j time) * source omega slot time

/-- Ordinary path block as an ensemble observable. -/
def pathBlockObservable
    (path : Omega → I → Real → Complex)
    (block : Finset I) (time : Real) (omega : Omega) : Complex :=
  signedBlockMonomial (path omega) block time

/-- A finite weighted block insertion is the sum of the weighted moments of
its individual source-inserted slot observables. -/
theorem finiteWeightedBlockInsertion_eq_sum_slotMoments
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (block : Finset I) (time : Real) :
    finiteWeightedBlockInsertion weight path source block time =
      ∑ slot ∈ block,
        finiteWeightedObservableMoment weight
          (sourceInsertedBlockObservable path source block slot time) := by
  unfold finiteWeightedBlockInsertion finiteWeightedObservableMoment
    sourceInsertedBlockObservable signedBlockSlotInsertion
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The mixed left-source/right-moment correlation is the sum of its
single-source-slot mixed moments. -/
theorem finiteWeightedInsertionMoment_eq_sum_slotMixedMoments
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) :
    finiteWeightedInsertionMoment weight path source left right time =
      ∑ slot ∈ left,
        finiteWeightedObservableMoment weight (fun omega ↦
          sourceInsertedBlockObservable path source left slot time omega *
            pathBlockObservable path right time omega) := by
  unfold finiteWeightedInsertionMoment finiteWeightedObservableMoment
    sourceInsertedBlockObservable pathBlockObservable
    signedBlockSlotInsertion
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The mixed left-moment/right-source correlation is the sum of its
single-source-slot mixed moments. -/
theorem finiteWeightedMomentInsertion_eq_sum_slotMixedMoments
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) :
    finiteWeightedMomentInsertion weight path source left right time =
      ∑ slot ∈ right,
        finiteWeightedObservableMoment weight (fun omega ↦
          pathBlockObservable path left time omega *
            sourceInsertedBlockObservable path source right slot time omega) := by
  unfold finiteWeightedMomentInsertion finiteWeightedObservableMoment
    sourceInsertedBlockObservable pathBlockObservable
    signedBlockSlotInsertion
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The mixed left-source defect is exactly a sum of ordinary
source-slot-versus-block factorization defects. -/
theorem leftSourceMomentFactorizationDefect_eq_sum_slotDefects
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) :
    leftSourceMomentFactorizationDefect
        weight path source left right time =
      ∑ slot ∈ left,
        finiteWeightedObservableFactorizationDefect weight
          (sourceInsertedBlockObservable path source left slot time)
          (pathBlockObservable path right time) := by
  unfold leftSourceMomentFactorizationDefect
    finiteWeightedObservableFactorizationDefect
  rw [finiteWeightedInsertionMoment_eq_sum_slotMixedMoments,
    finiteWeightedBlockInsertion_eq_sum_slotMoments]
  unfold finiteWeightedBlockMoment pathBlockObservable
  rw [Finset.sum_mul]
  exact (Finset.sum_sub_distrib _ _).symm

/-- Norm bound by the sum of all resolved left source-slot defects. -/
theorem norm_leftSourceMomentFactorizationDefect_le_sum_slotDefects
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) :
    ‖leftSourceMomentFactorizationDefect
        weight path source left right time‖ ≤
      ∑ slot ∈ left,
        ‖finiteWeightedObservableFactorizationDefect weight
          (sourceInsertedBlockObservable path source left slot time)
          (pathBlockObservable path right time)‖ := by
  rw [leftSourceMomentFactorizationDefect_eq_sum_slotDefects]
  exact norm_sum_le _ _

/-- The right-moment/source defect has the symmetric single-slot expansion. -/
theorem rightMomentSourceFactorizationDefect_eq_sum_slotDefects
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) :
    rightMomentSourceFactorizationDefect
        weight path source left right time =
      ∑ slot ∈ right,
        finiteWeightedObservableFactorizationDefect weight
          (pathBlockObservable path left time)
          (sourceInsertedBlockObservable path source right slot time) := by
  unfold rightMomentSourceFactorizationDefect
    finiteWeightedObservableFactorizationDefect
  rw [finiteWeightedMomentInsertion_eq_sum_slotMixedMoments,
    finiteWeightedBlockInsertion_eq_sum_slotMoments]
  unfold finiteWeightedBlockMoment pathBlockObservable
  rw [Finset.mul_sum]
  exact (Finset.sum_sub_distrib _ _).symm

/-- Norm bound by the sum of all resolved right source-slot defects. -/
theorem norm_rightMomentSourceFactorizationDefect_le_sum_slotDefects
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) :
    ‖rightMomentSourceFactorizationDefect
        weight path source left right time‖ ≤
      ∑ slot ∈ right,
        ‖finiteWeightedObservableFactorizationDefect weight
          (pathBlockObservable path left time)
          (sourceInsertedBlockObservable path source right slot time)‖ := by
  rw [rightMomentSourceFactorizationDefect_eq_sum_slotDefects]
  exact norm_sum_le _ _

end

end ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion
