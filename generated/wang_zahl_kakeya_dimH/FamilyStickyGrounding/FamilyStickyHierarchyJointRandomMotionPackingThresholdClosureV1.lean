import FamilyStickyGrounding.FamilyStickyHierarchyJointRandomMotionNumericThresholdV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped NNReal

namespace FamilyStickyHierarchyJointRandomMotionPackingThresholdClosureV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyRandomProductCoordinatePackingV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionNumericThresholdV1

noncomputable section

/-!
# Closing the hierarchy packing threshold by an explicit finite grid

The canonical product-coordinate net covers a radius-`1200` ball at mesh
`1/4`.  Its cardinality was previously used only as an upper packing
constant, so its API did not expose the lower bound `10000` needed by the
hierarchy collision numerics.

There is no need to enlarge or redefine that shared constant.  The ball
already contains the explicit `100 x 100` integer grid supported in two
coordinates of its first `Space` factor.  Distinct grid points are at least
one apart, while every point has norm at most `198`.  The existing packing
injection therefore proves that the chosen covering net has at least `10000`
centres and closes the threshold unconditionally.
-/

/-- A two-coordinate integer grid point in the first ambient `Space`. -/
def packingGridSpacePoint (a : Fin 100 × Fin 100) : Space :=
  EuclideanSpace.single (0 : Fin 3) (((a.1 : Nat) : Real)) +
    EuclideanSpace.single (1 : Fin 3) (((a.2 : Nat) : Real))

/-- The corresponding product-coordinate line parameter. -/
def packingGridParameter (a : Fin 100 × Fin 100) : LineParameter :=
  (packingGridSpacePoint a, 0)

@[simp] theorem packingGridSpacePoint_apply_zero
    (a : Fin 100 × Fin 100) :
    packingGridSpacePoint a 0 = ((a.1 : Nat) : Real) := by
  simp [packingGridSpacePoint]

@[simp] theorem packingGridSpacePoint_apply_one
    (a : Fin 100 × Fin 100) :
    packingGridSpacePoint a 1 = ((a.2 : Nat) : Real) := by
  simp [packingGridSpacePoint]

/-- Distinct natural coordinates have real absolute difference at least one. -/
theorem one_le_abs_fin_cast_sub {n : Nat} (a b : Fin n) (hab : a ≠ b) :
    (1 : Real) <= |((a : Nat) : Real) - ((b : Nat) : Real)| := by
  have hval : (a : Nat) ≠ (b : Nat) := by
    intro h
    exact hab (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hstep : (a : Nat) + 1 <= (b : Nat) := Nat.succ_le_iff.mpr hlt
    have hstepReal : (((a : Nat) : Real) + 1) <= ((b : Nat) : Real) := by
      exact_mod_cast hstep
    rw [abs_of_nonpos]
    · linarith
    · linarith
  · have hstep : (b : Nat) + 1 <= (a : Nat) := Nat.succ_le_iff.mpr hgt
    have hstepReal : (((b : Nat) : Real) + 1) <= ((a : Nat) : Real) := by
      exact_mod_cast hstep
    rw [abs_of_nonneg]
    · linarith
    · linarith

/-- Every explicit grid point lies well inside the normalized radius-`1200`
parameter ball. -/
theorem packingGridParameter_rangeBound (a : Fin 100 × Fin 100) :
    ‖packingGridParameter a‖ <=
      (normalizedParameterRadius : Real) := by
  have ha : (((a.1 : Nat) : Real)) <= 99 := by
    exact_mod_cast (Nat.le_pred_of_lt a.1.isLt)
  have hb : (((a.2 : Nat) : Real)) <= 99 := by
    exact_mod_cast (Nat.le_pred_of_lt a.2.isLt)
  have hspace : ‖packingGridSpacePoint a‖ <= 198 := by
    calc
      ‖packingGridSpacePoint a‖ <=
          ‖EuclideanSpace.single (0 : Fin 3) (((a.1 : Nat) : Real))‖ +
            ‖EuclideanSpace.single (1 : Fin 3) (((a.2 : Nat) : Real))‖ :=
        norm_add_le _ _
      _ = (((a.1 : Nat) : Real)) + (((a.2 : Nat) : Real)) := by
        simp [PiLp.norm_single]
      _ <= 198 := by linarith
  simpa [packingGridParameter, Prod.norm_def, normalizedParameterRadius]
    using hspace.trans (by norm_num : (198 : Real) <= 1200)

/-- The explicit product grid is one-separated. -/
theorem packingGridParameter_oneSeparated
    (a b : Fin 100 × Fin 100) (hab : a ≠ b) :
    (1 : Real) <= ‖packingGridParameter a - packingGridParameter b‖ := by
  have hspace :
      (1 : Real) <= ‖packingGridSpacePoint a - packingGridSpacePoint b‖ := by
    by_cases hfirst : a.1 = b.1
    · have hsecond : a.2 ≠ b.2 := by
        intro h
        exact hab (Prod.ext hfirst h)
      have hcoord :
          |(packingGridSpacePoint a - packingGridSpacePoint b) 1| <=
            ‖packingGridSpacePoint a - packingGridSpacePoint b‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le
            (packingGridSpacePoint a - packingGridSpacePoint b) (1 : Fin 3)
      have hgap :
          (1 : Real) <=
            |(packingGridSpacePoint a - packingGridSpacePoint b) 1| := by
        simpa using one_le_abs_fin_cast_sub a.2 b.2 hsecond
      exact hgap.trans hcoord
    · have hcoord :
          |(packingGridSpacePoint a - packingGridSpacePoint b) 0| <=
            ‖packingGridSpacePoint a - packingGridSpacePoint b‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le
            (packingGridSpacePoint a - packingGridSpacePoint b) (0 : Fin 3)
      have hgap :
          (1 : Real) <=
            |(packingGridSpacePoint a - packingGridSpacePoint b) 0| := by
        simpa using one_le_abs_fin_cast_sub a.1 b.1 hfirst
      exact hgap.trans hcoord
  simpa [packingGridParameter, Prod.norm_def] using hspace

/-- The already chosen canonical covering net necessarily has at least
`10000` centres. -/
theorem tenThousand_le_productCoordinatePackingConstant :
    10000 <= productCoordinatePackingConstant := by
  have hcard := card_le_productCoordinatePackingConstant
    packingGridParameter packingGridParameter_rangeBound
      packingGridParameter_oneSeparated
  simpa using hcard

/-- The opaque common-neighbour packing constant automatically exceeds the
numeric hierarchy threshold. -/
theorem commonHundredNeighbourTwentyThousandThreshold :
    CommonHundredNeighbourTwentyThousandThreshold :=
  commonHundredNeighbourTwentyThousandThreshold_iff.mpr
    tenThousand_le_productCoordinatePackingConstant

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- Fully source-generated hierarchy joint certificate, with the former
packing-cardinality premise discharged by the explicit grid. -/
theorem exists_joint_certificate
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (S : HierarchyCollisionTestSourceGeometry H)
    (W : HierarchyLevelWZSeparationData H) :
    Nonempty
      (HierarchyJointRandomMotionCertificate H
        (S.toHierarchyRandomMotionGeometry H)) :=
  exists_joint_certificate_of_threshold H S W
    commonHundredNeighbourTwentyThousandThreshold

#print axioms packingGridParameter_rangeBound
#print axioms packingGridParameter_oneSeparated
#print axioms tenThousand_le_productCoordinatePackingConstant
#print axioms commonHundredNeighbourTwentyThousandThreshold
#print axioms exists_joint_certificate

end
end FamilyStickyHierarchyJointRandomMotionPackingThresholdClosureV1
