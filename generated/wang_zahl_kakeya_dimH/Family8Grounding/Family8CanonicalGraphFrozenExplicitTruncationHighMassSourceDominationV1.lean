import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationFinalRetentionV1
import Mathlib.Tactic

/-!
# The selected explicit-truncation high mass is paid by its frozen source

This is the monotonicity bridge used after the explicit no-`ell` selector.
It does not select any new graph, level, or exact-card band: the set
`E p p` below is literally the multiplicity band of the high-fibre datum
formed from the graph and explicit level stored in the same
`SameAssemblyFullCoefficientGraphIdentity`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenExplicitTruncationHighMassSourceDominationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenExplicitTruncationFinalRetentionV1
open Family8CanonicalGraphFrozenExplicitTruncationHalfRetentionV1
open Family8CanonicalGraphFrozenLowFibreWeightedTailV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

universe u

variable {iota : Type u} {G : ConvexFamily iota}

/-- Every restricted high-fibre weighted mass is bounded by the full
projected active source.  This is pure monotonicity plus the exact
low/high decomposition; no finiteness or positivity hypothesis is needed. -/
theorem highFibreWeightedMass_le_projectedActiveShadingMassMeasure_univ
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (level : ENNReal) (E : Set ProjectionSpace) :
    highFibreWeightedMass Y active f level E ≤
      projectedActiveShadingMassMeasure Y active f Set.univ := by
  calc
    highFibreWeightedMass Y active f level E ≤
        highFibreWeightedMass Y active f level Set.univ := by
      unfold highFibreWeightedMass
      exact lintegral_mono_set (Set.subset_univ E)
    _ ≤ lowFibreWeightedMass Y active f level Set.univ +
        highFibreWeightedMass Y active f level Set.univ :=
      le_add_left le_rfl
    _ = projectedActiveShadingMassMeasure Y active f Set.univ :=
      (projectedActiveShadingMassMeasure_eq_low_add_high
        Y active f hf level Set.univ MeasurableSet.univ).symm

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- On the frozen canonical graph, the literal exact-card high band selected
by the explicit truncation is bounded by the literal projected source. -/
theorem sameGraph_explicitLevel_exactCard_highMass_le_projectedSource
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (p : Nat) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    let densityFloor :=
      ((Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading
          P Y).shadingDensity /
        ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
        R.graphLoss
    let level0 := densityFloor * (tau : ENNReal) / 96
    let highPhysical :=
      positiveLowerFibreProjectedPhysical Yw graph f0
        measurable_const level0
    let E := highPhysical.multiplicityBand
    highFibreWeightedMass Yw graph f0 level0 (E p p) ≤
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ := by
  dsimp only
  exact highFibreWeightedMass_le_projectedActiveShadingMassMeasure_univ
    _ _ _ measurable_const _ _

/-- The same selected high mass is consequently bounded by the literal
graph shading mass, with the intervening projected-source equality retained
in the statement for downstream witness auditing. -/
theorem sameGraph_explicitLevel_exactCard_highMass_le_source_eq_graphShadingMass
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (p : Nat) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    let densityFloor :=
      ((Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading
          P Y).shadingDensity /
        ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
        R.graphLoss
    let level0 := densityFloor * (tau : ENNReal) / 96
    let highPhysical :=
      positiveLowerFibreProjectedPhysical Yw graph f0
        measurable_const level0
    let E := highPhysical.multiplicityBand
    highFibreWeightedMass Yw graph f0 level0 (E p p) ≤
        projectedActiveShadingMassMeasure Yw graph f0 Set.univ ∧
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ =
        Z.shadingMass := by
  dsimp only
  constructor
  · exact sameGraph_explicitLevel_exactCard_highMass_le_projectedSource R p
  · exact sameGraph_zeroWindow_projectedSource_eq_graphShadingMass R

#print axioms highFibreWeightedMass_le_projectedActiveShadingMassMeasure_univ
#print axioms sameGraph_explicitLevel_exactCard_highMass_le_projectedSource
#print axioms sameGraph_explicitLevel_exactCard_highMass_le_source_eq_graphShadingMass

end

end Family8CanonicalGraphFrozenExplicitTruncationHighMassSourceDominationV1
