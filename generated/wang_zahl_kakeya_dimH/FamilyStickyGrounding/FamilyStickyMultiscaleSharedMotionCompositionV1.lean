import FamilyStickyGrounding.FamilyStickyLatticeMotionRadiusV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyMultiscaleSharedMotionCompositionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1

noncomputable section

/-!
# Multiscale composition of shared translations

GWZ `lemmasubsticky`, pinned source lines 1506--1512, chooses one finite
translation family `R_k` at every scale and takes every composition
`R_1 o ... o R_M`.  A final translation index is therefore the dependent
product of the per-scale indices, and its ambient vector is their sum.

This module freezes only that composition geometry.  It records actual
per-scale vectors and norm bounds, proves nonemptiness from `1 <= J_k`, and
controls the total motion radius by `sum rho_k`.  No per-scale probability or
existence conclusion is accepted here.
-/

/-- Actual finite shared translation families at all scales. -/
structure MultiscaleSharedMotionComposition (depth : Nat) where
  repetitions : Fin depth -> Nat
  scaleVector : forall k, Fin (repetitions k) -> Space
  scaleRadius : Fin depth -> NNReal
  scaleVector_norm_le : forall k j,
    ‖scaleVector k j‖ <= (scaleRadius k : Real)

namespace MultiscaleSharedMotionComposition

variable {depth : Nat} (M : MultiscaleSharedMotionComposition depth)

/-- One choice of a translation at every scale. -/
abbrev Path := forall k, Fin (M.repetitions k)

/-- The vector of the composed translation. -/
def composedVector (path : M.Path) : Space :=
  ∑ k, M.scaleVector k (path k)

/-- Sum of all permitted per-scale radii. -/
def totalRadius : NNReal := ∑ k, M.scaleRadius k

/-- Source nondegeneracy `J_k >= 1` constructs an actual multiscale path. -/
theorem path_nonempty
    (hJ : forall k, 1 <= M.repetitions k) : Nonempty M.Path := by
  refine ⟨fun k => ⟨0, ?_⟩⟩
  exact lt_of_lt_of_le Nat.zero_lt_one (hJ k)

/-- Triangle inequality for the composed translation. -/
theorem norm_composedVector_le_totalRadius (path : M.Path) :
    ‖M.composedVector path‖ <= (M.totalRadius : Real) := by
  calc
    ‖M.composedVector path‖ =
        ‖∑ k, M.scaleVector k (path k)‖ := rfl
    _ <= ∑ k, ‖M.scaleVector k (path k)‖ := norm_sum_le _ _
    _ <= ∑ k, (M.scaleRadius k : Real) := by
      exact Finset.sum_le_sum fun k _ => M.scaleVector_norm_le k (path k)
    _ = (M.totalRadius : Real) := by simp [totalRadius]

/-- A source radius budget immediately controls every composed vector. -/
theorem norm_composedVector_le_budget
    (path : M.Path) {budget : NNReal}
    (hbudget : M.totalRadius <= budget) :
    ‖M.composedVector path‖ <= (budget : Real) :=
  (M.norm_composedVector_le_totalRadius path).trans (by exact_mod_cast hbudget)

/-- The composed actual translation keeps every tube inside the thickening by
the sum of the scale radii. -/
theorem composed_translateTube_carrier_subset_cthickening
    {delta : NNReal} (T : Tube delta) (path : M.Path) :
    (translateTube T (M.composedVector path)).carrier ⊆
      Metric.cthickening (M.totalRadius : Real) T.carrier :=
  FamilyStickyLatticeMotionRadiusV1.translateTube_carrier_subset_cthickening_of_norm_le
    T (M.composedVector path) M.totalRadius
      (M.norm_composedVector_le_totalRadius path)

/-- Budgeted version of the actual carrier control. -/
theorem composed_translateTube_carrier_subset_cthickening_budget
    {delta : NNReal} (T : Tube delta) (path : M.Path)
    {budget : NNReal} (hbudget : M.totalRadius <= budget) :
    (translateTube T (M.composedVector path)).carrier ⊆
      Metric.cthickening (budget : Real) T.carrier :=
  FamilyStickyLatticeMotionRadiusV1.translateTube_carrier_subset_cthickening_of_norm_le
    T (M.composedVector path) budget
      (M.norm_composedVector_le_budget path hbudget)

/-- Two actual tube translations compose by vector addition, at the literal
carrier level used downstream. -/
theorem translateTube_translateTube_carrier
    {delta : NNReal} (T : Tube delta) (v w : Space) :
    (translateTube (translateTube T v) w).carrier =
      (translateTube T (w + v)).carrier := by
  rw [translateTube_carrier, translateTube_carrier,
    translateTube_carrier]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by simp [add_assoc]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨v + z, ⟨z, hz, rfl⟩, by simp [add_assoc]⟩

#print axioms path_nonempty
#print axioms norm_composedVector_le_totalRadius
#print axioms norm_composedVector_le_budget
#print axioms composed_translateTube_carrier_subset_cthickening
#print axioms composed_translateTube_carrier_subset_cthickening_budget
#print axioms translateTube_translateTube_carrier

end MultiscaleSharedMotionComposition

end
end FamilyStickyMultiscaleSharedMotionCompositionV1
