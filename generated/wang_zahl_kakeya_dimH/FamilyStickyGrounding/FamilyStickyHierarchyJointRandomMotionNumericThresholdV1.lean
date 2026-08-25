import FamilyStickyGrounding.FamilyStickyHierarchyJointRandomMotionEndToEndV1

set_option autoImplicit false

open scoped NNReal

namespace FamilyStickyHierarchyJointRandomMotionNumericThresholdV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomProductCoordinatePackingV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyJointRandomMotionEndToEndV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Exact numerical threshold for automatic hierarchy collision closure

The source branching inequality and `100 * delta <= 1 / 2` imply the sharp
uniform upper bound `20000` for the collision-unit ratio.  The currently
chosen common-neighbour constant is not a numeral: it is twice the cardinality
of a noncomputably chosen finite `1 / 4`-net.  Its existing API proves only
positivity, not the lower bound `20000 <= C_WZ` needed to close the endpoint.

This module records both the unconditional `20000` consequence and the exact
missing packing-net threshold.  It never accepts a load, probability estimate,
or target certificate as input.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- Strongest uniform collision ratio supplied by the current source-scale
and small-radius hypotheses. -/
def HierarchyJointCollisionTwentyThousandBound
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop :=
  forall k : Fin depth,
    (297 * ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
        (200 * (H.effectiveRadius k.1 : Real)) *
        (200 * (H.effectiveRadius k.1 : Real))) /
      (H.effectiveRadius (k.1 + 1) : Real) ^ 2 <= 20000

/-- The exact extra lower bound on the opaque packing-net cardinality that
would turn the unconditional `20000` estimate into the existing WZ cap. -/
def CommonHundredNeighbourTwentyThousandThreshold : Prop :=
  20000 <= commonHundredNeighbourPackingConstant

/-- Since `C_WZ = 2 * C_product`, the missing threshold is precisely the
lower bound `10000 <= C_product` on the chosen product-coordinate net. -/
theorem commonHundredNeighbourTwentyThousandThreshold_iff :
    CommonHundredNeighbourTwentyThousandThreshold ↔
      10000 <= productCoordinatePackingConstant := by
  unfold CommonHundredNeighbourTwentyThousandThreshold
    commonHundredNeighbourPackingConstant
  omega

/-- The branching scale contributes a factor `10000`, while
`100 * delta <= 1 / 2` contributes the remaining factor at most two. -/
theorem hierarchyJointCollision_le_twentyThousand
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (S : HierarchyCollisionTestSourceGeometry H) :
    HierarchyJointCollisionTwentyThousandBound H := by
  intro k
  let d : Real := H.effectiveRadius k.1
  let R : Real := H.effectiveRadius (k.1 + 1)
  let B : Real := (H.step k.1 k.2).combinatorics.branchingFactor
  have hdNN : 0 < H.effectiveRadius k.1 := S.childRadius_pos k
  have hRNN : 0 < H.effectiveRadius (k.1 + 1) :=
    lt_of_lt_of_le hdNN (H.effectiveRadius_step_le k.1 k.2)
  have hR : 0 < R := by
    exact_mod_cast hRNN
  have hRsq : 0 < R ^ 2 := by positivity
  have hsmallNN := S.hundredRadius_le_half k
  have hsmall : 200 * d <= 1 := by
    have hsmallReal :
        (hundredRadius (H.effectiveRadius k.1) : Real) <=
          (((2 : NNReal)⁻¹ : NNReal) : Real) := by
      exact_mod_cast hsmallNN
    norm_num [d, hundredRadius, NNReal.coe_mul, NNReal.coe_inv] at hsmallReal
    linarith
  have hscale : 1188 * B * d ^ 2 <= (1 + 200 * d) * R ^ 2 := by
    simpa [B, d, R] using S.branchingScale k
  have hscaled :
      10000 * (1188 * B * d ^ 2) <=
        10000 * ((1 + 200 * d) * R ^ 2) :=
    mul_le_mul_of_nonneg_left hscale (by norm_num)
  have hcap :
      10000 * ((1 + 200 * d) * R ^ 2) <= 20000 * R ^ 2 := by
    have hfactor : 1 + 200 * d <= 2 := by linarith
    nlinarith [sq_nonneg R]
  change (297 * B * (200 * d) * (200 * d)) / R ^ 2 <= 20000
  apply (div_le_iff₀ hRsq).2
  calc
    297 * B * (200 * d) * (200 * d) =
        10000 * (1188 * B * d ^ 2) := by ring
    _ <= 10000 * ((1 + 200 * d) * R ^ 2) := hscaled
    _ <= 20000 * R ^ 2 := hcap

/-- Conditional closure against the present opaque WZ constant. -/
theorem hierarchyJointCollisionUnitNumerics_of_threshold
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (S : HierarchyCollisionTestSourceGeometry H)
    (hpacking : CommonHundredNeighbourTwentyThousandThreshold) :
    HierarchyJointCollisionUnitNumerics H := by
  intro k
  exact (hierarchyJointCollision_le_twentyThousand H S k).trans (by
    exact_mod_cast hpacking)

/-- The fully source-generated endpoint follows once the one missing
packing-net cardinal lower bound is supplied. -/
theorem exists_joint_certificate_of_threshold
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (S : HierarchyCollisionTestSourceGeometry H)
    (W : HierarchyLevelWZSeparationData H)
    (hpacking : CommonHundredNeighbourTwentyThousandThreshold) :
    Nonempty
      (HierarchyJointRandomMotionCertificate H
        (S.toHierarchyRandomMotionGeometry H)) := by
  exact exists_joint_certificate H S W
    (hierarchyJointCollisionUnitNumerics_of_threshold H S hpacking)

#print axioms commonHundredNeighbourTwentyThousandThreshold_iff
#print axioms hierarchyJointCollision_le_twentyThousand
#print axioms hierarchyJointCollisionUnitNumerics_of_threshold
#print axioms exists_joint_certificate_of_threshold

end
end FamilyStickyHierarchyJointRandomMotionNumericThresholdV1
