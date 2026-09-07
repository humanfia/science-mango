import Family8Grounding.Family8FiniteRigidMotionUnitSpherePackingV3
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace
open scoped Matrix.Norms.L2Operator

namespace Family8FiniteRigidMotionOrthogonalHaarV4

noncomputable section

/-!
# The genuine normalized Haar rotation law on O(3)

The paper's random rigid motion samples a rotation and then a bounded
translation.  The rotation component is not replaced by a supplied law here:
the real orthogonal matrix group is proved compact inside the finite
dimensional matrix space, and Haar measure is normalized on its whole
compact carrier.  Thus the resulting measure has total mass exactly one and
is left invariant.
-/

abbrev OrthogonalThree := Matrix.orthogonalGroup (Fin 3) Real

theorem orthogonalThree_norm_eq_one (U : OrthogonalThree) :
    ‖(U.1 : Matrix (Fin 3) (Fin 3) Real)‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary U.2

theorem orthogonalThree_isBounded :
    Bornology.IsBounded
      (Matrix.orthogonalGroup (Fin 3) Real :
        Set (Matrix (Fin 3) (Fin 3) Real)) := by
  apply (Metric.isBounded_iff_subset_closedBall
    (0 : Matrix (Fin 3) (Fin 3) Real)).2
  refine ⟨1, ?_⟩
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarRing.norm_of_mem_unitary hU).le

theorem orthogonalThree_isCompact :
    IsCompact
      (Matrix.orthogonalGroup (Fin 3) Real :
        Set (Matrix (Fin 3) (Fin 3) Real)) := by
  apply Metric.isCompact_iff_isClosed_bounded.2
  exact ⟨isClosed_unitary, orthogonalThree_isBounded⟩

noncomputable instance orthogonalThreeCompactSpace :
    CompactSpace OrthogonalThree :=
  isCompact_iff_compactSpace.mp orthogonalThree_isCompact

noncomputable instance orthogonalThreeMeasurableSpace :
    MeasurableSpace OrthogonalThree := borel OrthogonalThree

instance orthogonalThreeBorelSpace : BorelSpace OrthogonalThree :=
  ⟨rfl⟩

def orthogonalThreePositiveCompact :
    TopologicalSpace.PositiveCompacts OrthogonalThree :=
  ⟨⟨Set.univ, CompactSpace.isCompact_univ⟩, by simp⟩

def orthogonalThreeHaarProbability : Measure OrthogonalThree :=
  Measure.haarMeasure orthogonalThreePositiveCompact

@[simp] theorem orthogonalThreeHaarProbability_univ :
    orthogonalThreeHaarProbability Set.univ = 1 := by
  simpa [orthogonalThreeHaarProbability,
    orthogonalThreePositiveCompact] using
    (Measure.haarMeasure_self
      (K₀ := orthogonalThreePositiveCompact))

theorem orthogonalThreeHaarProbability_map_mul_left
    (U : OrthogonalThree) :
    Measure.map (fun V : OrthogonalThree ↦ U * V)
        orthogonalThreeHaarProbability =
      orthogonalThreeHaarProbability := by
  simpa only [orthogonalThreeHaarProbability] using
    (map_mul_left_eq_self
      (Measure.haarMeasure orthogonalThreePositiveCompact) U)

#print axioms orthogonalThree_norm_eq_one
#print axioms orthogonalThree_isBounded
#print axioms orthogonalThree_isCompact
#print axioms orthogonalThreeHaarProbability_univ
#print axioms orthogonalThreeHaarProbability_map_mul_left

end
end Family8FiniteRigidMotionOrthogonalHaarV4
