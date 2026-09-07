import Family8Grounding.Family8FiniteRigidMotionOrthogonalOrbitLawV2
import Family8Grounding.Family8FiniteRigidMotionUnitSpherePackingLowerV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalCapProbabilityV1

open LeanEval.Analysis.WangZahlKakeya
open Family8SphereDirectionPackingV1
open Family8FiniteRigidMotionUnitSpherePackingV3
open Family8FiniteRigidMotionUnitSpherePackingLowerV3
open Family8FiniteRigidMotionOrthogonalOrbitLawV2

noncomputable section

/-!
# A quadratic cap bound for the genuine orthogonal orbit law

A maximal `2 * mesh`-separated net on the unit sphere has at least a constant
multiple of `mesh⁻²` points.  The radius-`mesh` balls around these points
are pairwise disjoint, while orthogonal invariance gives every such ball the
same orbit-law mass.  Since the orbit law is a probability measure, a single
unit-centred ball consequently has mass at most a constant times `mesh²`.
-/

theorem orthogonalOrbitLaw_unitBall_toReal_le_five_mul_sq
    (u c : Space) (hc : ‖c‖ = 1)
    (mesh : NNReal) (hmesh : 0 < mesh) (hmeshHalf : mesh ≤ 1 / 2) :
    (orthogonalOrbitLaw u
        (Metric.ball c (mesh : Real))).toReal ≤
      5 * (mesh : Real) ^ 2 := by
  let I := UnitDirectionChoice mesh hmesh
  let μ := orthogonalOrbitLaw u
  have hsep : ∀ i ∈ (Finset.univ : Finset I),
      ∀ j ∈ (Finset.univ : Finset I), i ≠ j →
        (((2 * mesh : NNReal) : Real)) ≤
          dist (i.1 : Space) (j.1 : Space) := by
    intro i _hi j _hj hij
    exact (unitDirectionChoice_separated mesh hmesh i j hij).le
  have hdisjoint :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset I) : Set I)
        (fun i ↦ Metric.ball (i.1 : Space) (mesh : Real)) := by
    have hraw := directionSmallBalls_pairwiseDisjoint
      (Finset.univ : Finset I) (fun i : I ↦ (i.1 : Space))
      (2 * mesh) hsep
    simpa using hraw
  have hmeasureUnion :
      μ (⋃ i ∈ (Finset.univ : Finset I),
          Metric.ball (i.1 : Space) (mesh : Real)) =
        ∑ i ∈ (Finset.univ : Finset I),
          μ (Metric.ball (i.1 : Space) (mesh : Real)) := by
    exact measure_biUnion_finset hdisjoint (fun _ _ ↦ measurableSet_ball)
  have hunionLe :
      μ (⋃ i ∈ (Finset.univ : Finset I),
          Metric.ball (i.1 : Space) (mesh : Real)) ≤ 1 := by
    calc
      μ (⋃ i ∈ (Finset.univ : Finset I),
          Metric.ball (i.1 : Space) (mesh : Real)) ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := orthogonalOrbitLaw_univ u
  have hequal : ∀ i : I,
      μ (Metric.ball (i.1 : Space) (mesh : Real)) =
        μ (Metric.ball c (mesh : Real)) := by
    intro i
    exact orthogonalOrbitLaw_ball_eq_of_norm_eq u (i.1 : Space) c
      ((unitDirectionChoice_norm mesh hmesh i).trans hc.symm) (mesh : Real)
  have hcardMassENN :
      (Fintype.card I : ENNReal) *
          μ (Metric.ball c (mesh : Real)) ≤ 1 := by
    rw [hmeasureUnion] at hunionLe
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hequal] using hunionLe
  have hcardMassReal :
      (Fintype.card I : Real) *
          (μ (Metric.ball c (mesh : Real))).toReal ≤ 1 := by
    have hreal := ENNReal.toReal_mono ENNReal.one_ne_top hcardMassENN
    simpa [ENNReal.toReal_mul] using hreal
  have hcardLower :
      2 ≤ 9 * (Fintype.card I : Real) * (mesh : Real) ^ 2 := by
    simpa only [I] using two_le_nine_card_mul_mesh_sq
      mesh hmesh hmeshHalf
  have hmassNonneg :
      0 ≤ (μ (Metric.ball c (mesh : Real))).toReal :=
    ENNReal.toReal_nonneg
  have hmeshSqNonneg : 0 ≤ (mesh : Real) ^ 2 := sq_nonneg _
  have htwice :
      2 * (μ (Metric.ball c (mesh : Real))).toReal ≤
        9 * (mesh : Real) ^ 2 := by
    calc
      2 * (μ (Metric.ball c (mesh : Real))).toReal ≤
          (9 * (Fintype.card I : Real) * (mesh : Real) ^ 2) *
            (μ (Metric.ball c (mesh : Real))).toReal :=
        mul_le_mul_of_nonneg_right hcardLower hmassNonneg
      _ = (9 * (mesh : Real) ^ 2) *
          ((Fintype.card I : Real) *
            (μ (Metric.ball c (mesh : Real))).toReal) := by ring
      _ ≤ (9 * (mesh : Real) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hcardMassReal (by positivity)
      _ = 9 * (mesh : Real) ^ 2 := by ring
  nlinarith

#print axioms orthogonalOrbitLaw_unitBall_toReal_le_five_mul_sq

end
end Family8FiniteRigidMotionOrthogonalCapProbabilityV1
