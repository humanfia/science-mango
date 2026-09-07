import Family8Grounding.Family8EighthNormalizedWZL3SourceV3
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketV12
import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizationCoreV1
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Family8Grounding.Family8FullCoefficientActualMassProxyAverageV10
import Family8Grounding.Family8StickyGraphContractedJohnProxyDatumV2
import FamilyStickyCinematicL32WZL3UniformTubeSourceV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

/-!
# Exact Family7 graph density after eighth normalization, V12

V10 still opened the duplicate official Assembly namespace.  This clean
successor resolves every bare Assembly through the built Family8 owner and
otherwise preserves the literal graph proof.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFullCoefficientEighthDensityV12

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8EighthNormalizedWZL3SourceV3
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8FrozenNeighborhoodAssemblyV1
open Family8FullCoefficientActualMassProxyAverageV10
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8StickyGraphContractedJohnProxyDatumV2
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe v

/-- Restricting an actual datum and selecting its shading by the same finite
subtype give definitionally identical densities. -/
theorem stickyGraphSourceDatum_shadingDensity_eq_selectedCoarseShading
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {F : UniformTubeFamily radius iota}
    (Y : Shading F.bodyFamily) (active : Finset iota) :
    (stickyGraphSourceDatum Y active).shading.shadingDensity =
      (selectedCoarseShading Y active).shadingDensity := by
  rfl

/-- On the literal graph subtype, the Family7 graph-bucket shading and the
vertical source shading define the same density. -/
theorem firstCrossingGraphBucket_selectedDensity_eq_graphSource
    {radius : NNReal} {iota : Type} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarseFamily : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarseFamily)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let VY := firstCrossingFamilyVerticalShading axis F P A k
    let graph := verticalSourceGraphCBucketFiber
      ((radius : Real) / 2) VS label
    (selectedCoarseShading
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k) graph).shadingDensity =
      (stickyGraphSourceDatum VY graph).shading.shadingDensity := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let VY := firstCrossingFamilyVerticalShading axis F P A k
  let graph := verticalSourceGraphCBucketFiber
    ((radius : Real) / 2) VS label
  unfold Shading.shadingDensity
  congr 1
  rw [selectedCoarseShading_mass,
    stickyGraphSourceDatum, restrictActualTubeDatum_shadingMass]
  apply Finset.sum_congr rfl
  intro i hi
  rw [firstCrossingFamilyGraphBucketShading,
    IndexedShadingRefinement.restrictTo_carrier, if_pos hi]

/-- The active whole-window shading used by the full-coefficient branch is
the eighth normalization of the exact graph-subtype source datum. -/
theorem eighthNormalized_activeRestricted_univ_shadingDensity_eq
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota) :
    (activeRestrictedShading
      (eighthNormalizedWZL3Source S)
      (eighthNormalizedShading S.family Y) active Set.univ
      MeasurableSet.univ).shadingDensity =
    (eighthNormalizedDatum
      (stickyGraphSourceDatum Y active)).shading.shadingDensity := by
  let D := stickyGraphSourceDatum Y active
  let lhs := activeRestrictedShading
    (eighthNormalizedWZL3Source S)
    (eighthNormalizedShading S.family Y) active Set.univ
    MeasurableSet.univ
  let rhs := (eighthNormalizedDatum D).shading
  have hcarrier : ∀ i, lhs.carrier i = rhs.carrier i := by
    intro i
    change
      (eighthDilationPoint '' Y.carrier i.1) ∩ Set.univ =
        eighthDilationPoint '' Y.carrier i.1
    exact Set.inter_univ _
  have hmass : lhs.shadingMass = rhs.shadingMass := by
    unfold Shading.shadingMass
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hcarrier i]
  have hfamily :
      familyVolume
          ((eighthNormalizedWZL3Source S).family.restrictTo active).bodyFamily =
        familyVolume (eighthNormalizedDatum D).family.bodyFamily := by
    unfold familyVolume
    apply Finset.sum_congr rfl
    intro i _hi
    rfl
  change lhs.shadingMass /
      familyVolume
        ((eighthNormalizedWZL3Source S).family.restrictTo active).bodyFamily =
    rhs.shadingMass /
      familyVolume (eighthNormalizedDatum D).family.bodyFamily
  rw [hmass, hfamily]

/-- The exact Family7 graph density loses only the honest factor 128 under
the eighth normalization used by the full-coefficient critical scale. -/
theorem firstCrossingGraphBucket_density_div_128_le_eighthNormalized
    {radius : NNReal} {iota : Type} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarseFamily : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarseFamily)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hgraphNonempty :
      (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label).Nonempty)
    (hradius : 0 < radius)
    (hradiusHalf : radius ≤ (2 : NNReal)⁻¹) :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let VY := firstCrossingFamilyVerticalShading axis F P A k
    let graph := verticalSourceGraphCBucketFiber
      ((radius : Real) / 2) VS label
    (selectedCoarseShading
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k) graph).shadingDensity / 128 ≤
      (activeRestrictedShading
        (eighthNormalizedWZL3Source VS)
        (eighthNormalizedShading VS.family VY) graph Set.univ
        MeasurableSet.univ).shadingDensity := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let VY := firstCrossingFamilyVerticalShading axis F P A k
  let graph := verticalSourceGraphCBucketFiber
    ((radius : Real) / 2) VS label
  let _ : Nonempty {i // i ∈ graph} :=
    Finset.nonempty_coe_sort.mpr hgraphNonempty
  let D := stickyGraphSourceDatum VY graph
  have htransport : D.shading.shadingDensity / 128 ≤
      (eighthNormalizedDatum D).shading.shadingDensity :=
    source_shadingDensity_div_128_le_eighthNormalized_of_scale
      D hradius hradiusHalf
  rw [firstCrossingGraphBucket_selectedDensity_eq_graphSource
    axis label F P A k]
  rw [eighthNormalized_activeRestricted_univ_shadingDensity_eq]
  exact htransport

#print axioms
  stickyGraphSourceDatum_shadingDensity_eq_selectedCoarseShading
#print axioms
  firstCrossingGraphBucket_selectedDensity_eq_graphSource
#print axioms
  eighthNormalized_activeRestricted_univ_shadingDensity_eq
#print axioms
  firstCrossingGraphBucket_density_div_128_le_eighthNormalized

end
end Family8Family7FirstCrossingFullCoefficientEighthDensityV12
