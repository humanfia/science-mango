import Family8Grounding.Family8DensityAwareShadingFrostmanRestrictionV3
import Family8Grounding.Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3
import Family8Grounding.Family8Family7CoordinateToVerticalTubeTransportV1
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketV12
import Family8Grounding.Family8SelectedCoarseShadingDensityRetentionV3
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

/-!
# Clean family-only graph-bucket Frostman certificate, V12

V11 is frozen after direct validation exposed three remaining direct transport
and order-normalization issues.  This ADD-only successor keeps the same literal
assembly, fibre, axis, label, graph, density, and Frostman witness.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFamilyGraphBucketFrostmanV12

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6AffineConvexVolumeCoreV1
open Family8DensityAwareShadingFrostmanRestrictionV3
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalSelectedSubtypeDensityV3
open Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenAssemblyMassPopularFiberDensityV2
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8SelectedCoarseShadingDensityRetentionV3
open Family8StickyShadingAwareLogBucketSelectionV1

noncomputable section

universe u v

/-- One mass-popular actual fibre and one genuine graph bucket carry the
literal mass-retention witness, density floor, same-assembly product, and
Frostman certificate simultaneously. -/
theorem exists_massPopular_familyGraphBucket_frostman_sameProduct_retained
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r)
    (K : kappa → ConvexBody Space) (C : ENNReal)
    (hfull : ∀ k ∈ P.index.coarse,
      IsFrostmanOn C F.bodyFamily (P.index.fiber k) (K k))
    (hradius : 0 < radius)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass ≠ 0) :
    ∃ k ∈ P.index.coarse, ∃ axis : Fin 3, ∃ label : Int,
      let VS := firstCrossingFamilyVerticalSource axis F P k
      let graph := verticalSourceGraphCBucketFiber
        ((radius : Real) / 2) VS label
      let baseLoss : ENNReal :=
        (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
      let d : ENNReal :=
        (sourceActiveFineShading P Y).shadingDensity / baseLoss
      let graphLoss : ENNReal :=
        ((3 * verticalGraphCBucketLoss
          ((radius : Real) / 2) : Nat) : ENNReal)
      let verticalAmbient : ConvexBody Space :=
        affineImageConvexBody
          (coordinateToVerticalRigidMotion axis).toAffineEquiv (K k)
      graph.Nonempty ∧
      WithinFactor
        (3 * verticalGraphCBucketLoss ((radius : Real) / 2))
        (finalFiberShading A k).shadingMass
        (firstCrossingFamilyGraphBucketShading
          axis label F P A k).shadingMass ∧
      d / graphLoss ≤
        (selectedCoarseShading
          (firstCrossingFamilyGraphBucketShading
            axis label F P A k) graph).shadingDensity ∧
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).shadingMass ≠ 0 ∧
      0 < volume (finalFiberShading A k).shadedUnion ∧
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) ∧
      IsFrostmanOn (C * (d⁻¹ * graphLoss))
        VS.family.bodyFamily graph verticalAmbient := by
  obtain ⟨k, hk, hpopularDensity, hfinalPositive, hproduct⟩ :=
    exists_massPopular_finalFiber_density_sameProduct A hsource
  have hsourceMass :
      (sourceActiveFineShading P Y).shadingMass ≠ 0 := by
    rw [sourceActiveFineShading_shadingMass]
    exact hsource
  have hsourceVolume :
      familyVolume (sourceActiveFineFamily P) ≠ 0 := by
    intro hzero
    apply hsourceMass
    exact le_antisymm
      ((sourceActiveFineShading P Y).shadingMass_le_familyVolume.trans_eq
        hzero)
      bot_le
  have hsourceDensity0 :
      (sourceActiveFineShading P Y).shadingDensity ≠ 0 := by
    unfold Shading.shadingDensity
    exact ENNReal.div_ne_zero.mpr
      ⟨hsourceMass, familyVolume_ne_top (sourceActiveFineFamily P)⟩
  have hsourceDensityTop :
      (sourceActiveFineShading P Y).shadingDensity ≠ ∞ := by
    unfold Shading.shadingDensity
    exact ENNReal.div_ne_top
      (ne_of_lt (sourceActiveFineShading P Y).shadingMass_lt_top)
      hsourceVolume
  have hloss0 : (A.loss : ENNReal) ≠ 0 := by
    intro hzero
    apply hsourceMass
    apply le_antisymm
    · have hretained :=
        sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
      simpa only [hzero, zero_mul] using hretained
    · exact bot_le
  have hcard0 : (P.index.coarse.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨k, hk⟩
  let baseLoss : ENNReal :=
    (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  have hbase0 : baseLoss ≠ 0 := mul_ne_zero hloss0 hcard0
  have hbaseTop : baseLoss ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top A.loss)
      (ENNReal.natCast_ne_top P.index.coarse.card)
  let d : ENNReal :=
    (sourceActiveFineShading P Y).shadingDensity / baseLoss
  have hd0 : d ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hsourceDensity0, hbaseTop⟩
  have hdTop : d ≠ ∞ :=
    ENNReal.div_ne_top hsourceDensityTop hbase0
  have hfinalMass : (finalFiberShading A k).shadingMass ≠ 0 := by
    apply ne_of_gt
    have hle : volume (finalFiberShading A k).shadedUnion ≤
        (finalFiberShading A k).shadingMass := by
      have hpoint :=
        natCast_mul_volume_le_shadingMass_of_pointMultiplicity_lower
          (finalFiberShading A k) 1
          (fun x hx ↦ Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt
              (((finalFiberShading A k).pointMultiplicity_pos_iff_mem_shadedUnion x).mpr hx)))
      simpa only [Nat.cast_one, one_mul] using hpoint
    exact hfinalPositive.trans_le hle
  obtain ⟨axis, label, hgraphNonempty, hretained,
      _hbucket, _hgraphGap⟩ :=
    exists_firstCrossingFamilyGraphBucket_mass_retention
      F P A k hradius hfinalMass
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let graph := verticalSourceGraphCBucketFiber
    ((radius : Real) / 2) VS label
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss
      ((radius : Real) / 2) : Nat) : ENNReal)
  let verticalAmbient : ConvexBody Space :=
    affineImageConvexBody
      (coordinateToVerticalRigidMotion axis).toAffineEquiv (K k)
  have hgraphMass :
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).shadingMass ≠ 0 := by
    intro hzero
    apply hfinalMass
    have hle : (finalFiberShading A k).shadingMass ≤ 0 := by
      simpa only [WithinFactor, hzero, nsmul_zero] using hretained
    exact le_antisymm hle bot_le
  have hgraphSubset : graph ⊆ P.index.fiber k := by
    simpa only [graph, VS] using
      firstCrossingFamilyGraphBucket_subset_fiber axis label F P k
  have hretainedOn :
      shadingMassOn (firstCrossingFamilyCoordinateShading axis F P A k)
          (P.index.fiber k) ≤
        graphLoss * shadingMassOn
          (firstCrossingFamilyCoordinateShading axis F P A k) graph := by
    rw [firstCrossingFamilyCoordinateShading_shadingMassOn_fiber,
      firstCrossingFamilyCoordinateShading_shadingMassOn_graph]
    simpa only [graphLoss, WithinFactor, nsmul_eq_mul] using hretained
  have hpopularCoordinate :
      d ≤ (selectedCoarseShading
        (firstCrossingFamilyCoordinateShading axis F P A k)
        (P.index.fiber k)).shadingDensity := by
    change
      (sourceActiveFineShading P Y).shadingDensity /
          ((A.loss : ENNReal) * (P.index.coarse.card : ENNReal)) ≤
        (selectedCoarseShading
          (coordinateToVerticalShading axis F (finalFiberShading A k))
          (P.index.fiber k)).shadingDensity
    rw [coordinateToVertical_selectedCoarseShading_shadingDensity]
    exact hpopularDensity
  have hgraphDensity :=
    selectedCoarseShading_density_div_loss_le
      (firstCrossingFamilyCoordinateShading axis F P A k)
      graphLoss hgraphSubset hretainedOn
  have hgraphFloorCoordinate :
      d / graphLoss ≤
        (selectedCoarseShading
          (firstCrossingFamilyCoordinateShading axis F P A k)
          graph).shadingDensity :=
    (ENNReal.div_le_div_right hpopularCoordinate graphLoss).trans
      hgraphDensity
  have hgraphFloor :
      d / graphLoss ≤
        (selectedCoarseShading
          (firstCrossingFamilyGraphBucketShading
            axis label F P A k) graph).shadingDensity := by
    rw [← firstCrossingFamilyCoordinateShading_selectedGraph_density
      axis label F P A k]
    exact hgraphFloorCoordinate
  have hfullCoordinate :
      IsFrostmanOn C VS.family.bodyFamily (P.index.fiber k)
        verticalAmbient := by
    change IsFrostmanOn C
      (coordinateToVerticalFamily axis F).bodyFamily
      (P.index.fiber k)
      (affineImageConvexBody
        (coordinateToVerticalRigidMotion axis).toAffineEquiv (K k))
    exact IsFrostmanOn.coordinateToVertical axis F
      (P.index.fiber k) (K k) (hfull k hk)
  have hdensityMass :
      d * containedMassOn VS.family.bodyFamily
          (P.index.fiber k) verticalAmbient ≤
        shadingMassOn
          (firstCrossingFamilyCoordinateShading axis F P A k)
          (P.index.fiber k) := by
    calc
      d * containedMassOn VS.family.bodyFamily
          (P.index.fiber k) verticalAmbient ≤
        (selectedCoarseShading
          (firstCrossingFamilyCoordinateShading axis F P A k)
          (P.index.fiber k)).shadingDensity *
            containedMassOn VS.family.bodyFamily
              (P.index.fiber k) verticalAmbient := by
        simpa only [mul_comm] using
          (mul_le_mul_right hpopularCoordinate
            (containedMassOn VS.family.bodyFamily
              (P.index.fiber k) verticalAmbient))
      _ = shadingMassOn
          (firstCrossingFamilyCoordinateShading axis F P A k)
          (P.index.fiber k) := by
        exact selectedCoarseShading_density_mul_containedMassOn
          (firstCrossingFamilyCoordinateShading axis F P A k)
          (P.index.fiber k) verticalAmbient hfullCoordinate.1
  have hgraphFrostman :
      IsFrostmanOn (C * (d⁻¹ * graphLoss))
        VS.family.bodyFamily graph verticalAmbient := by
    exact isFrostmanOn_subset_of_density_shading_retention
      (firstCrossingFamilyCoordinateShading axis F P A k)
      hgraphSubset hfullCoordinate hd0 hdTop hdensityMass hretainedOn
  refine ⟨k, hk, axis, label, ?_⟩
  dsimp only
  exact ⟨by simpa only [graph, VS] using hgraphNonempty,
    hretained, hgraphFloor, hgraphMass, hfinalPositive, hproduct,
    hgraphFrostman⟩

#print axioms
  exists_massPopular_familyGraphBucket_frostman_sameProduct_retained

end
end Family8Family7FirstCrossingFamilyGraphBucketFrostmanV12
