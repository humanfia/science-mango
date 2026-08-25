import FamilyStickyGrounding.FamilyStickyHierarchyJointRandomMotionPackingThresholdClosureV1
import FamilyStickyGrounding.FamilyStickyScaleChainDiscreteRefinementTreeV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open scoped NNReal

namespace FamilyStickyHierarchyRadiusBranchingScalarClosureV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionPackingThresholdClosureV1

noncomputable section

/-!
# Endpoint closure for the hierarchy radius and branching scalars

The collision-test producer used to ask separately, at every hierarchy
level, for positivity of the child radius, the cutoff
`100 * childRadius <= 1 / 2`, and the bound `parentRadius <= 1`.  Monotonicity
of the actual buffered radii shows that all of those checks are consequences
of just two endpoint facts: positivity at level zero and an upper bound
`effectiveRadius depth <= 1 / 200` at the top.

The remaining branching comparison is genuinely independent of radius
monotonicity.  We expose both its exact form and a convenient stronger
quadratic budget.  A numerical equal-scale counterexample below proves that
the branching field cannot be silently synthesized from the endpoint radius
checks.  Once this minimal scalar certificate is present, the previously
proved source-derived `20000` estimate and explicit `100 x 100` packing grid
close the joint collision certificate with no further numerical premise.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- The two endpoint radius checks that imply every radius field of
`HierarchyCollisionTestSourceGeometry`. -/
structure EndpointRadiusCertificate
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop where
  bottomRadius_pos : 0 < H.effectiveRadius 0
  topRadius_le_invTwoHundred :
    H.effectiveRadius depth <= (200 : NNReal)⁻¹

namespace EndpointRadiusCertificate

variable (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (R : EndpointRadiusCertificate H)

include R in
/-- Positivity propagates from the bottom through the monotone effective
radius chain. -/
theorem childRadius_pos (k : Fin depth) :
    0 < H.effectiveRadius k.1 := by
  exact R.bottomRadius_pos.trans_le
    (FamilyStickyScaleChainDiscreteRefinementTreeV1.MultiscaleTubeHierarchy.effectiveRadius_mono H
      (Nat.le_of_lt k.2) (Nat.zero_le _))

include R in
/-- The single top-radius cutoff implies `100 * delta <= 1 / 2` at every
child level. -/
theorem hundredRadius_le_half (k : Fin depth) :
    hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹ := by
  calc
    hundredRadius (H.effectiveRadius k.1) <=
        hundredRadius (H.effectiveRadius depth) := by
      unfold hundredRadius
      exact mul_le_mul_of_nonneg_left
        (FamilyStickyScaleChainDiscreteRefinementTreeV1.MultiscaleTubeHierarchy.effectiveRadius_mono H
          le_rfl (Nat.le_of_lt k.2)) (by positivity)
    _ <= hundredRadius ((200 : NNReal)⁻¹) := by
      unfold hundredRadius
      exact mul_le_mul_of_nonneg_left R.topRadius_le_invTwoHundred (by positivity)
    _ = (2 : NNReal)⁻¹ := by
      norm_num [hundredRadius]

include R in
/-- The same top cutoff is much stronger than the old parent-radius-at-most
one field. -/
theorem parentRadius_le_one (k : Fin depth) :
    H.effectiveRadius (k.1 + 1) <= 1 := by
  calc
    H.effectiveRadius (k.1 + 1) <= H.effectiveRadius depth :=
      FamilyStickyScaleChainDiscreteRefinementTreeV1.MultiscaleTubeHierarchy.effectiveRadius_mono H le_rfl
        (Nat.succ_le_iff.mpr k.2)
    _ <= (200 : NNReal)⁻¹ := R.topRadius_le_invTwoHundred
    _ <= 1 :=
      (inv_le_one₀ (by norm_num : (0 : NNReal) < 200)).2 (by norm_num)

/-- A nominal-buffer comparison reduces the two effective-radius endpoint
checks to literal nominal endpoint arithmetic. -/
theorem ofNominalComparison
    (C : H.NominalComparison)
    (hbottom : 0 < nominalRadius 0)
    (htop : (1 + C.factor) * nominalRadius depth <=
      (200 : NNReal)⁻¹) : EndpointRadiusCertificate H where
  bottomRadius_pos := hbottom.trans_le
    (H.nominalRadius_le_effectiveRadius 0)
  topRadius_le_invTwoHundred :=
    (C.effectiveRadius_le depth le_rfl).trans htop

end EndpointRadiusCertificate

/-- A convenient stronger, dimensionless-looking branching budget.  It
separates the quadratic scale gap from the harmless collision longitudinal
factor `1 + 200 * delta`. -/
def HierarchyQuadraticBranchingBudget
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop :=
  forall k : Fin depth,
    1188 * ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
        (H.effectiveRadius k.1 : Real) ^ 2 <=
      (H.effectiveRadius (k.1 + 1) : Real) ^ 2

/-- The quadratic budget implies the exact branching comparison consumed by
the actual collision-test geometry producer. -/
theorem hierarchyCollisionBranchingScale_of_quadraticBudget
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (B : HierarchyQuadraticBranchingBudget H) :
    HierarchyCollisionBranchingScale H := by
  intro k
  calc
    1188 * ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
          (H.effectiveRadius k.1 : Real) ^ 2 <=
        (H.effectiveRadius (k.1 + 1) : Real) ^ 2 := B k
    _ <= (1 + 200 * (H.effectiveRadius k.1 : Real)) *
          (H.effectiveRadius (k.1 + 1) : Real) ^ 2 := by
      have hd : 0 <= (H.effectiveRadius k.1 : Real) := by positivity
      have hR2 : 0 <= (H.effectiveRadius (k.1 + 1) : Real) ^ 2 :=
        sq_nonneg _
      nlinarith

/-- Minimal exact scalar certificate after collapsing all per-level radius
checks to the two endpoints. -/
structure ScalarCertificate
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop where
  radius : EndpointRadiusCertificate H
  branchingScale : HierarchyCollisionBranchingScale H

namespace ScalarCertificate

variable (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : ScalarCertificate H)

/-- Build the older source-geometry record without asking the caller to
repeat any levelwise radius facts. -/
theorem toSourceGeometry (C : ScalarCertificate H) :
    HierarchyCollisionTestSourceGeometry H where
  childRadius_pos := EndpointRadiusCertificate.childRadius_pos H (ScalarCertificate.radius C)
  hundredRadius_le_half := EndpointRadiusCertificate.hundredRadius_le_half H (ScalarCertificate.radius C)
  parentRadius_le_one := EndpointRadiusCertificate.parentRadius_le_one H (ScalarCertificate.radius C)
  branchingScale := ScalarCertificate.branchingScale C

/-- Constructor from the slightly stronger quadratic branching budget. -/
theorem ofQuadraticBudget
    (R : EndpointRadiusCertificate H)
    (B : HierarchyQuadraticBranchingBudget H) : ScalarCertificate H where
  radius := R
  branchingScale :=
    hierarchyCollisionBranchingScale_of_quadraticBudget H B

/-- The collision ratio is automatically at most `20000`; this is included
as a named bridge so downstream code need not reopen the source record. -/
theorem jointCollision_le_twentyThousand (C : ScalarCertificate H) :
    FamilyStickyHierarchyJointRandomMotionNumericThresholdV1.HierarchyJointCollisionTwentyThousandBound H :=
  FamilyStickyHierarchyJointRandomMotionNumericThresholdV1.hierarchyJointCollision_le_twentyThousand
    H (toSourceGeometry H C)

/-- Complete hierarchy joint-collision closure.  The packing threshold is no
longer an input: the explicit `100 x 100` grid has already discharged it. -/
theorem exists_joint_certificate
    (W : HierarchyLevelWZSeparationData H) :
    Nonempty
      (HierarchyJointRandomMotionCertificate H
        ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H)) :=
  FamilyStickyHierarchyJointRandomMotionPackingThresholdClosureV1.exists_joint_certificate
    H (toSourceGeometry H C) W

end ScalarCertificate

/-! ## Sharp audit obstruction -/

/-- Even the smallest possible positive branching factor fails the required
branching comparison at the equal scale `delta = R = 1 / 200`, although all
radius endpoint checks hold.  Thus monotonicity of an actual scale chain and
the small-radius cutoff cannot imply the branching field. -/
theorem equalScale_radiusChecks_hold_but_branchingScale_fails :
    let d : Real := 1 / 200
    0 < d /\ 100 * d <= 1 / 2 /\ d <= 1 /\
      not (1188 * (1 : Real) * d ^ 2 <=
        (1 + 200 * d) * d ^ 2) := by
  norm_num

#print axioms EndpointRadiusCertificate.childRadius_pos
#print axioms EndpointRadiusCertificate.hundredRadius_le_half
#print axioms EndpointRadiusCertificate.parentRadius_le_one
#print axioms EndpointRadiusCertificate.ofNominalComparison
#print axioms hierarchyCollisionBranchingScale_of_quadraticBudget
#print axioms ScalarCertificate.toSourceGeometry
#print axioms ScalarCertificate.jointCollision_le_twentyThousand
#print axioms ScalarCertificate.exists_joint_certificate
#print axioms equalScale_radiusChecks_hold_but_branchingScale_fails

end
end FamilyStickyHierarchyRadiusBranchingScalarClosureV1
