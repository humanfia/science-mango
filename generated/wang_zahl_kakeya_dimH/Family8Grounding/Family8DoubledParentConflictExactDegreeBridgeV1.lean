import Family8Grounding.Family8DoubledParentConflictExactDegreeBudgetV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictExactDegreeBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedDef212WitnessV1.ScaleCover
open Family8DoubledParentConflictExactDegreeBudgetV1.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Scalar interface for geometric doubled-parent degree estimates

The quantified `ClosedDoubledParentConflictDegreeBound` callback is exactly
equivalent to one scalar inequality for the literal finite graph maximum.
Thus a future packing argument only has to bound
`doubledParentConflictExactDegreeBudget`; all selection and Definition 2.12
packaging then follows automatically.
-/

namespace ScaleCover

variable {delta rho rho0 Cnn : NNReal}
variable {index : Type} [Fintype index] [DecidableEq index]
variable {fine : UniformTubeFamily delta index}
variable {S : StickyScaleCover fine rho}

theorem ClosedDoubledParentConflictDegreeBound.mono
    {A B : ENNReal}
    (hA : ClosedDoubledParentConflictDegreeBound S A) (hAB : A ≤ B) :
    ClosedDoubledParentConflictDegreeBound S B := by
  intro k hk neighbours hneighbours
  exact (hA k hk neighbours hneighbours).trans hAB

/-- Exact characterization of the public degree predicate by the explicit
finite graph maximum. -/
theorem closedDoubledParentConflictDegreeBound_iff_exactDegreeBudget_le
    (S : StickyScaleCover fine rho) (B : ENNReal) :
    ClosedDoubledParentConflictDegreeBound S B ↔
      doubledParentConflictExactDegreeBudget S ≤ B := by
  constructor
  · exact exactDegreeBudget_le_of_closedDoubledParentConflictDegreeBound S
  · intro hbudget
    exact ClosedDoubledParentConflictDegreeBound.mono
      (closedDoubledParentConflictDegreeBound_exact S) hbudget

variable {weight : Fin S.coarseCard → ENNReal} {B : ENNReal}

/-- A scalar upper bound for the exact graph maximum is sufficient for the
complete selected Definition 2.12 scale endpoint; no quantified neighbour
callback remains in the theorem interface. -/
theorem exists_weightedDef212ScaleEndpoint_of_exactDegreeBudget_le
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B : ENNReal)
    (hbudget : doubledParentConflictExactDegreeBudget S ≤ B)
    (hrho0 : rho0 ≤ rho) (hrhoOne : rho ≤ 1)
    (hrhoWindow : rho < Cnn * rho0)
    (R : UnitRescalingGeometry S)
    (hCWA : R.FibresSatisfyCWA (Cnn : ENNReal))
    (huniform : IsCUniform S (Cnn : ENNReal))
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Nonempty (WeightedDef212ScaleEndpoint S weight B rho0 Cnn) :=
  exists_weightedDef212ScaleEndpoint S weight B
    hrho0 hrhoOne hrhoWindow R hCWA
    (ClosedDoubledParentConflictDegreeBound.mono
      (closedDoubledParentConflictDegreeBound_exact S) hbudget)
    huniform hpaper

#print axioms ClosedDoubledParentConflictDegreeBound.mono
#print axioms closedDoubledParentConflictDegreeBound_iff_exactDegreeBudget_le
#print axioms exists_weightedDef212ScaleEndpoint_of_exactDegreeBudget_le

end ScaleCover
end
end Family8DoubledParentConflictExactDegreeBridgeV1
