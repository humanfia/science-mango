import Family8Grounding.Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalPatternCatalogueMembershipV2

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalTwoCapLawV2
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3

noncomputable section

variable {source center : Type*}
  [Fintype source] [DecidableEq source]
  [Fintype center] [DecidableEq center]

theorem mem_sampledTwoCapFinset_iff
    (direction : source -> Space) (capCenter : center -> Space)
    (cap : NNReal) {n : Nat}
    (g : OrthogonalPatternSample direction capCenter cap n)
    (q : OrthogonalCapTest source center) :
    g ∈ sampledTwoCapFinset direction capCenter cap n q ↔
      sampledOrthogonal direction capCenter cap g ∈
        orthogonalTwoCapEvent (direction q.1) (capCenter q.2) cap := by
  classical
  unfold sampledTwoCapFinset
  unfold
    Family8FiniteIncidencePatternSamplerV7.MeasurableEventFamily.sampleEventFinset
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

#print axioms mem_sampledTwoCapFinset_iff

end
end Family8FiniteRigidMotionOrthogonalPatternCatalogueMembershipV2
