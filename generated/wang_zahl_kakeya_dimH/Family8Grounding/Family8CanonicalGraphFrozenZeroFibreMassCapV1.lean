import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8UniformTubeZeroFibreMassCapV1

/-!
# The constant fibre-mass cap on the literal frozen graph

This specializes the geometric zero-fibre cap to the graph shading, zero
projection and full windows definitionally fixed by one canonical identity
record.  It supplies the bounded-scale input for a finite two-sided fibre
bucket selection without replacing `Set.univ` by an artificial short window.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenZeroFibreMassCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ShadingAwareProjectedPhysicalV3
open Family8UniformTubeZeroFibreMassCapV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Every fibre mass of the literal zero/full-window graph shading is at most
two at the canonical scale range `tau <= 1/2`. -/
theorem sameGraph_zeroWindow_shadingFiberMass_le_two
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htauHalf : tau <= (2 : NNReal)⁻¹)
    (i : fineIndex) (u : ProjectionSpace) :
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real -> Real := fun _ => 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    shadingFiberMass Yw f0 i u <= 2 := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  simpa only [VS, Z, f0, Yw] using
    shadingFiberMass_zero_le_two VS.family Yw htauHalf i u

#print axioms sameGraph_zeroWindow_shadingFiberMass_le_two

end
end Family8CanonicalGraphFrozenZeroFibreMassCapV1
