import Family8Grounding.Family8CanonicalGraphFrozenLowFibreWeightedTailV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenExplicitTruncationHalfRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenLowFibreWeightedTailV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

/-- A low-tail bound at the explicit level
`densityFloor * tau / 96`, together with the half-square source lower
bound, retains at least one half of the genuine weighted mass. -/
theorem highFibreWeightedMass_retains_half_of_explicit_level
    {iota : Type u} [Fintype iota]
    {G : ConvexFamily iota}
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (tau densityFloor : ENNReal)
    (htail :
      lowFibreWeightedMass Y active f
          (densityFloor * tau / 96) Set.univ ≤
        24 * tau * (active.card : ENNReal) *
          (densityFloor * tau / 96))
    (hsource :
      densityFloor *
          ((active.card : ENNReal) * (tau ^ 2 / 2)) ≤
        projectedActiveShadingMassMeasure Y active f Set.univ)
    (hsourceTop :
      projectedActiveShadingMassMeasure Y active f Set.univ ≠ ∞) :
    projectedActiveShadingMassMeasure Y active f Set.univ ≤
      2 * highFibreWeightedMass Y active f
        (densityFloor * tau / 96) Set.univ := by
  let level := densityFloor * tau / 96
  let source :=
    projectedActiveShadingMassMeasure Y active f Set.univ
  let low := lowFibreWeightedMass Y active f level Set.univ
  let high := highFibreWeightedMass Y active f level Set.univ
  have hdecomp : source = low + high := by
    simpa only [source, low, high, level] using
      projectedActiveShadingMassMeasure_eq_low_add_high
        Y active f hf level Set.univ MeasurableSet.univ
  have hcoefficient :
      2 * (24 * tau * (active.card : ENNReal) * level) =
        densityFloor *
          ((active.card : ENNReal) * (tau ^ 2 / 2)) := by
    dsimp only [level]
    have hratio : (48 : ENNReal) / 96 = (1 : ENNReal) / 2 := by
      simp only [ENNReal.div_eq_inv_mul, mul_one]
      calc
        (96 : ENNReal)⁻¹ * 48 =
            ((2 : ENNReal) * 48)⁻¹ * 48 := by norm_num
        _ = ((2 : ENNReal)⁻¹ * (48 : ENNReal)⁻¹) * 48 := by
          rw [ENNReal.mul_inv] <;> norm_num
        _ = (2 : ENNReal)⁻¹ * ((48 : ENNReal)⁻¹ * 48) := by
          rw [mul_assoc]
        _ = (2 : ENNReal)⁻¹ * 1 := by
          rw [ENNReal.inv_mul_cancel] <;> norm_num
        _ = (2 : ENNReal)⁻¹ := mul_one _
    calc
      2 * (24 * tau * (active.card : ENNReal) *
          (densityFloor * tau / 96)) =
          densityFloor * ((active.card : ENNReal) * tau ^ 2) *
            ((48 : ENNReal) / 96) := by
        simp only [ENNReal.div_eq_inv_mul]
        ring
      _ = densityFloor * ((active.card : ENNReal) * tau ^ 2) *
          ((1 : ENNReal) / 2) := by rw [hratio]
      _ = densityFloor *
          ((active.card : ENNReal) * (tau ^ 2 / 2)) := by
        simp only [ENNReal.div_eq_inv_mul]
        ring
  have htwoLow : 2 * low ≤ source := by
    calc
      2 * low ≤
          2 * (24 * tau * (active.card : ENNReal) * level) :=
        mul_le_mul' le_rfl (by
          simpa only [low, level] using htail)
      _ = densityFloor *
          ((active.card : ENNReal) * (tau ^ 2 / 2)) := hcoefficient
      _ ≤ source := by simpa only [source] using hsource
  have hlowSource : low ≤ source := by
    calc
      low ≤ low + high := le_add_right le_rfl
      _ = source := hdecomp.symm
  have hlowTop : low ≠ ∞ :=
    ne_top_of_le_ne_top (by simpa only [source] using hsourceTop)
      hlowSource
  have hlowHigh : low ≤ high := by
    apply (ENNReal.add_le_add_iff_left hlowTop).mp
    calc
      low + low = 2 * low := by simp only [two_mul]
      _ ≤ source := htwoLow
      _ = low + high := hdecomp
  calc
    projectedActiveShadingMassMeasure Y active f Set.univ =
        low + high := hdecomp
    _ ≤ high + high := add_le_add hlowHigh le_rfl
    _ = 2 * high := by simp only [two_mul]
    _ = 2 * highFibreWeightedMass Y active f
        (densityFloor * tau / 96) Set.univ := by
      rfl

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The zero-window projected weighted source on the exact graph is exactly
the literal graph-restricted shading mass. -/
theorem sameGraph_zeroWindow_projectedSource_eq_graphShadingMass
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    projectedActiveShadingMassMeasure Yw graph f0 Set.univ =
      Z.shadingMass := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  have hwindow : ∀ i, Yw.carrier i = Z.carrier i := by
    intro i
    simp [Yw, shadingWindowRestriction, shadingProjectionWindow, f0]
  rw [projectedActiveShadingMassMeasure_apply
    Yw graph f0 measurable_const MeasurableSet.univ]
  have hsumEq :
      (∑ i ∈ graph, volume (Yw.carrier i)) = Z.shadingMass := by
    simp_rw [hwindow]
    change (∑ i ∈ graph,
      volume (((IndexedShadingRefinement.restrictTo
        (firstCrossingFamilyVerticalShading R.axis F P R.A R.k) graph).shading
          ).carrier i)) =
      (IndexedShadingRefinement.restrictTo
        (firstCrossingFamilyVerticalShading R.axis F P R.A R.k) graph).shading.shadingMass
    rw [shadingMass_restrictTo_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hi]
  simpa only [restrictedMass, preimage_univ, inter_univ] using hsumEq

/-- The graph-certificate density quotient pays one half-square volume for
every index of the exact same frozen graph. -/
theorem sameGraph_densityFloor_mul_card_half_sq_le_projectedSource
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    let densityFloor :=
      ((sourceActiveFineShading P Y).shadingDensity /
        ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
        R.graphLoss
    densityFloor *
        ((graph.card : ENNReal) * ((tau : ENNReal) ^ 2 / 2)) ≤
      projectedActiveShadingMassMeasure
        Yw graph f0 Set.univ := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let densityFloor :=
    ((sourceActiveFineShading P Y).shadingDensity /
      ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
      R.graphLoss
  let selected := selectedCoarseShading Z graph
  let Q := Classical.choice R.graphCertificate
  have hdensity : densityFloor ≤ selected.shadingDensity := by
    simpa only [densityFloor,
      SameAssemblyFullCoefficientGraphIdentity.graphLoss,
      selected, Z, graph, VS] using Q.graph_density
  have hfamily :
      (graph.card : ENNReal) * ((tau : ENNReal) ^ 2 / 2) ≤
        familyVolume (selectedCoarseFamily VS.family.bodyFamily graph) := by
    rw [selectedCoarseFamily_volume]
    calc
      (graph.card : ENNReal) * ((tau : ENNReal) ^ 2 / 2) =
          ∑ _i ∈ graph, ((tau : ENNReal) ^ 2 / 2) := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ graph, volume (VS.family.tubes i).carrier := by
        exact Finset.sum_le_sum fun i _hi ↦
          (VS.family.tubes i).half_sq_le_volume_of_le_half htauHalf
  have hselected :
      densityFloor *
          ((graph.card : ENNReal) * ((tau : ENNReal) ^ 2 / 2)) ≤
        selected.shadingMass := by
    calc
      densityFloor *
          ((graph.card : ENNReal) * ((tau : ENNReal) ^ 2 / 2)) ≤
          selected.shadingDensity *
            familyVolume (selectedCoarseFamily VS.family.bodyFamily graph) :=
        mul_le_mul' hdensity hfamily
      _ = selected.shadingMass := by
        exact shadingDensity_mul_familyVolume selected
  have hsource :
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ =
        selected.shadingMass := by
    rw [projectedActiveShadingMassMeasure_apply
      Yw graph f0 measurable_const MeasurableSet.univ]
    rw [selectedCoarseShading_mass]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [restrictedMass, Yw, shadingWindowRestriction,
      shadingProjectionWindow]
  exact hselected.trans_eq hsource.symm

/-- At the explicit level `(d / graphLoss) * tau / 96`, the positive-high
fibres of the exact frozen graph retain at least half of its genuine
projected weighted mass. -/
theorem sameGraph_zeroWindow_explicitLevel_highFibreWeightedMass_retains_half
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    let densityFloor :=
      ((sourceActiveFineShading P Y).shadingDensity /
        ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
        R.graphLoss
    let level0 := densityFloor * (tau : ENNReal) / 96
    projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
      2 * highFibreWeightedMass Yw graph f0 level0 Set.univ := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let densityFloor :=
    ((sourceActiveFineShading P Y).shadingDensity /
      ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
      R.graphLoss
  let level0 := densityFloor * (tau : ENNReal) / 96
  have htail :
      lowFibreWeightedMass Yw graph f0 level0 Set.univ ≤
        24 * (tau : ENNReal) * (graph.card : ENNReal) * level0 := by
    simpa only [VS, graph, Z, f0, Yw, level0] using
      sameGraph_zeroWindow_lowFibreWeightedMass_le R level0
  have hsource :
      densityFloor *
          ((graph.card : ENNReal) * ((tau : ENNReal) ^ 2 / 2)) ≤
        projectedActiveShadingMassMeasure Yw graph f0 Set.univ := by
    simpa only [VS, graph, Z, f0, Yw, densityFloor] using
      sameGraph_densityFloor_mul_card_half_sq_le_projectedSource
        R htauHalf
  have hsourceEq :
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ =
        Z.shadingMass := by
    simpa only [VS, graph, Z, f0, Yw] using
      sameGraph_zeroWindow_projectedSource_eq_graphShadingMass R
  have hsourceTop :
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≠ ∞ := by
    rw [hsourceEq]
    exact Z.shadingMass_lt_top.ne
  simpa only [level0] using
    highFibreWeightedMass_retains_half_of_explicit_level
      Yw graph f0 measurable_const (tau : ENNReal) densityFloor
        htail hsource hsourceTop

end
end Family8CanonicalGraphFrozenExplicitTruncationHalfRetentionV1
