import Family8Grounding.Family8DoubledParentConflictWeightedDef212EndpointV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8DoubledParentConflictWeightedDef212ScaleWitnessV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8DoubledParentConflictWeightedDef212EndpointV1.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}
  {S : StickyScaleCover fine rho}
variable {weight : Fin S.coarseCard → ENNReal} {B : ENNReal}
  {C rho0 : NNReal}

/-- A complete quantitative selected endpoint is literally a paper
`Def212ScaleWitness` once its scale lies in the requested multiplicative
window. -/
noncomputable def WeightedDef212ScaleEndpoint.toDef212ScaleWitness
    (E : WeightedDef212ScaleEndpoint S weight B (C : ENNReal))
    (hrho0 : rho0 ≤ rho) (hrhoOne : rho ≤ 1)
    (hrhoWindow : rho < C * rho0) :
    Def212ScaleWitness
      (weightedSelectedAssignedFineFamily E.base.selection) rho0 C :=
  { rho := rho
    rho0_le_rho := hrho0
    rho_le_one := hrhoOne
    rho_lt_C_mul_rho0 := hrhoWindow
    cover := weightedSelectedParentScaleCover E.base.selection
    c_uniform := E.base.c_uniform
    doubled_parent_partitioning := E.base.doubled_parent_partitioning
    unitRescalingGeometry := E.unitRescalingGeometry
    rescaled_fibres_cwa := E.rescaled_fibres_cwa }

/-- Direct existence form combining quantitative selection with the paper
scale-window wrapper. -/
theorem exists_weightedDef212ScaleWitness
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B : ENNReal) (C rho0 : NNReal)
    (hneighbour : ClosedDoubledParentConflictDegreeBound S B)
    (huniform : IsCUniform S (C : ENNReal))
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (R : UnitRescalingGeometry S)
    (hCWA : R.FibresSatisfyCWA (C : ENNReal))
    (hrho0 : rho0 ≤ rho) (hrhoOne : rho ≤ 1)
    (hrhoWindow : rho < C * rho0) :
    ∃ E : WeightedDef212ScaleEndpoint S weight B (C : ENNReal),
      Nonempty (Def212ScaleWitness
        (weightedSelectedAssignedFineFamily E.base.selection) rho0 C) := by
  obtain ⟨E⟩ := exists_weightedDef212ScaleEndpoint
    S weight B (C : ENNReal) hneighbour huniform hpaper R hCWA
  exact ⟨E, ⟨Family8DoubledParentConflictWeightedDef212ScaleWitnessV2.ScaleCover.WeightedDef212ScaleEndpoint.toDef212ScaleWitness E hrho0 hrhoOne hrhoWindow⟩⟩

#print axioms WeightedDef212ScaleEndpoint.toDef212ScaleWitness
#print axioms exists_weightedDef212ScaleWitness

end ScaleCover
end
end Family8DoubledParentConflictWeightedDef212ScaleWitnessV2
