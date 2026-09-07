import Family8Grounding.Family8Family7NativeHighNearSaturatedNormSplitV1
import Family8Grounding.Family8Family7NativeHighAmbientPackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighCriticalBallDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open Family8Family7NativeHighNearSaturatedNormSplitV1

noncomputable section

universe u

/-!
# Literal critical-ball datum for the unresolved native-high branch

The near-saturated split produces a genuinely rich canonical critical ball,
but the recursive consumer needs its object-level geometry rather than only
its cardinality.  This file exposes that geometry directly:

* the critical ball is a nonempty literal subfamily of the physical ambient;
* its selected centre belongs to it;
* every member lies within the actual critical scale of that centre, and its
  coefficient diameter is at most twice that scale;
* pairwise essential distinctness and unit-ball containment restrict from the
  upstream ambient family without any conclusion-valued callback.

The final package deliberately does not assert a rescaling or induction
conclusion.  Those require an actual affine/restriction consumer upstream.
-/

/-- The canonical critical ball lies in the physical ambient finset. -/
theorem nativeHighCriticalBall_subset_physicalAmbient
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall ⊆ D.physical.ambient := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  intro i hi
  have hiFamily : i ∈ N.family :=
    finiteNormCriticalBall_subset N.family N.distance N.delta N.ceiling
      N.exponent N.family_nonempty hi
  rw [positiveCenterHighPayloadGlobalNormData_family] at hiFamily
  exact (mem_actualGlobalNormIndexFamily_iff D.S.family D.physical
    D.globalScale c.1.1).mp hiFamily |>.1

/-- The literal critical ball is nonempty. -/
theorem nativeHighCriticalBall_nonempty
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall.Nonempty := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  exact finiteNormCriticalBall_nonempty N.family N.distance N.family_nonempty
    N.self_le_delta N.delta_le_ceiling

/-- The canonical maximizer centre belongs to the literal critical ball. -/
theorem nativeHighCriticalCenter_mem_criticalBall
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalCenter ∈
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalBall := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  exact finiteCriticalMaximizerCenter_mem_finiteNormCriticalBall
    N.family N.distance N.family_nonempty N.self_le_delta N.delta_le_ceiling

/-- Every critical-ball member is within the selected critical scale of the
actual maximizer centre. -/
theorem nativeHighCriticalBall_distance_to_center_le_scale
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    {i : iota}
    (hi : i ∈ (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall) :
    (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).distance i
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)).criticalCenter ≤
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale := by
  exact (Finset.mem_filter.mp hi).2

/-- The literal coefficient diameter is at most twice the actual selected
critical scale. -/
theorem nativeHighCriticalBall_distance_le_two_scale
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    {i j : iota}
    (hi : i ∈ (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall)
    (hj : j ∈ (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall) :
    (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).distance i j ≤
      2 * (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  exact finiteNormCriticalBall_distance_le_two_scale N.family N.distance
    N.delta N.ceiling N.exponent N.family_nonempty
    (fun i j => projectedTubePairCoefficientDistance_comm
      (D.S.family.tubes i) (D.S.family.tubes j))
    (fun i center j => projectedTubePairCoefficientDistance_triangle
      (D.S.family.tubes i) (D.S.family.tubes center)
        (D.S.family.tubes j)) hi hj

/-- Pairwise essential distinctness restricts from any ambient finset
containing the physical ambient. -/
theorem nativeHighCriticalBall_pairwise_essentiallyDistinct
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (hphysicalAmbient : D.physical.ambient ⊆ D.ambient)
    (hpairwise : Set.Pairwise (D.ambient : Set iota) (fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j))) :
    Set.Pairwise
      ((positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalBall : Set iota)
      (fun i j =>
        EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)) := by
  intro i hi j hj hij
  exact hpairwise
    (hphysicalAmbient (nativeHighCriticalBall_subset_physicalAmbient D c hi))
    (hphysicalAmbient (nativeHighCriticalBall_subset_physicalAmbient D c hj))
    hij

/-- Unit-ball containment likewise restricts to the literal critical ball. -/
theorem nativeHighCriticalBall_contained_in_unit_ball
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (hphysicalAmbient : D.physical.ambient ⊆ D.ambient)
    (hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    ∀ i, i ∈ (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalBall →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
  intro i hi
  exact hcontained i
    (hphysicalAmbient (nativeHighCriticalBall_subset_physicalAmbient D c hi))

/-- The complete object-level datum needed by a genuine critical-scale
restart consumer.  Every field below is inherited from the literal canonical
maximizer and the upstream extremal geometry. -/
structure NativeHighCriticalBallDatum
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) : Prop where
  nonempty : (positiveCenterHighPayloadGlobalNormData
    (D.chosenHighPayloadAt c)).criticalBall.Nonempty
  center_mem : (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalCenter ∈
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall
  subset_physicalAmbient : (positiveCenterHighPayloadGlobalNormData
    (D.chosenHighPayloadAt c)).criticalBall ⊆ D.physical.ambient
  scale_bounds : (radius : Real) ≤
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale ∧
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalScale ≤ 16
  distance_to_center : ∀ i, i ∈ (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall →
    (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).distance i
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)).criticalCenter ≤
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
  diameter : ∀ i, i ∈ (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall →
    ∀ j, j ∈ (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall →
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).distance i j ≤
      2 * (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
  pairwise_essentiallyDistinct : Set.Pairwise
    ((positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall : Set iota)
      (fun i j =>
        EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j))
  contained_in_unit_ball : ∀ i, i ∈
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalBall →
    (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1

/-- The critical-ball datum is constructed without a rescaling or conclusion
callback once the actual upstream extremal geometry is supplied. -/
theorem nativeHighCriticalBallDatum_of_upstream_extremal
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (hphysicalAmbient : D.physical.ambient ⊆ D.ambient)
    (hpairwise : Set.Pairwise (D.ambient : Set iota) (fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)))
    (hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    NativeHighCriticalBallDatum D c := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  refine {
    nonempty := nativeHighCriticalBall_nonempty D c
    center_mem := nativeHighCriticalCenter_mem_criticalBall D c
    subset_physicalAmbient := nativeHighCriticalBall_subset_physicalAmbient D c
    scale_bounds := ?_
    distance_to_center := ?_
    diameter := ?_
    pairwise_essentiallyDistinct :=
      nativeHighCriticalBall_pairwise_essentiallyDistinct D c
        hphysicalAmbient hpairwise
    contained_in_unit_ball :=
      nativeHighCriticalBall_contained_in_unit_ball D c
        hphysicalAmbient hcontained }
  · change N.delta ≤ N.criticalScale ∧ N.criticalScale ≤ N.ceiling
    exact finiteCriticalMaximizerScale_bounds N.family N.distance
      N.family_nonempty N.delta_le_ceiling
  · intro i hi
    exact nativeHighCriticalBall_distance_to_center_le_scale D c hi
  · intro i hi j hj
    exact nativeHighCriticalBall_distance_le_two_scale D c hi hj

/-- On the unresolved rich branch, the same literal datum carries the actual
logarithmic cardinal lower bound. -/
theorem exists_nativeHighCriticalBallDatum_of_richCenter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter}
    (hc : c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G)
    (hphysicalAmbient : D.physical.ambient ⊆ D.ambient)
    (hpairwise : Set.Pairwise (D.ambient : Set iota) (fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)))
    (hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    NativeHighCriticalBallDatum D c ∧
      12 * D.logCount <
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall.card := by
  exact ⟨nativeHighCriticalBallDatum_of_upstream_extremal D c
      hphysicalAmbient hpairwise hcontained,
    nativeHighNearSaturatedCriticalBallRich_card_gt_twelve_logCount
      D G hc⟩

/-- The equalities returned by the actual native-core producer connect its
literal extremal input directly to the critical-ball datum.  No geometric
field has to be copied into `NativeBranchCore`. -/
theorem nativeHighCriticalBallDatum_of_extremal_core_equalities
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : FamilyStickyCinematicL32WZL3UniformTubeSourceV1.WZL3UniformTubeSource
      radius iota)
    (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (outerA outerB : Real)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (E : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (D : NativeBranchCore radius iota)
    (hS : D.S = S) (hambient : D.ambient = ambient)
    (_hphysical : D.physical =
      actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB)
    (c : D.HighCenter) : NativeHighCriticalBallDatum D c := by
  have hphysicalAmbient : D.physical.ambient ⊆ D.ambient := by
    intro i hi
    exact hi
  have hpairwise : Set.Pairwise (D.ambient : Set iota) (fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)) := by
    rw [hambient, hS]
    exact E.essentially_distinct
  have hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
    rw [hambient, hS]
    exact E.contained_in_unit_ball
  exact nativeHighCriticalBallDatum_of_upstream_extremal D c
    hphysicalAmbient hpairwise hcontained

/-- Produced-core specialization of the rich branch: the same literal
critical ball has its complete inherited geometry and its logarithmic lower
cardinality bound. -/
theorem exists_nativeHighCriticalBallDatum_of_extremal_richCenter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : FamilyStickyCinematicL32WZL3UniformTubeSourceV1.WZL3UniformTubeSource
      radius iota)
    (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (outerA outerB : Real)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (E : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hS : D.S = S) (hambient : D.ambient = ambient)
    (hphysical : D.physical =
      actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB)
    {c : D.HighCenter}
    (hc : c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G) :
    NativeHighCriticalBallDatum D c ∧
      12 * D.logCount <
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall.card := by
  refine ⟨nativeHighCriticalBallDatum_of_extremal_core_equalities
      S ambient physicalBase hphysicalBase f hfContinuous outerA outerB E D
        hS hambient hphysical c, ?_⟩
  exact nativeHighNearSaturatedCriticalBallRich_card_gt_twelve_logCount
    D G hc

#print axioms nativeHighCriticalBall_subset_physicalAmbient
#print axioms nativeHighCriticalBall_nonempty
#print axioms nativeHighCriticalCenter_mem_criticalBall
#print axioms nativeHighCriticalBall_distance_to_center_le_scale
#print axioms nativeHighCriticalBall_distance_le_two_scale
#print axioms nativeHighCriticalBall_pairwise_essentiallyDistinct
#print axioms nativeHighCriticalBall_contained_in_unit_ball
#print axioms nativeHighCriticalBallDatum_of_upstream_extremal
#print axioms exists_nativeHighCriticalBallDatum_of_richCenter
#print axioms nativeHighCriticalBallDatum_of_extremal_core_equalities
#print axioms exists_nativeHighCriticalBallDatum_of_extremal_richCenter

end

end Family8Family7NativeHighCriticalBallDatumV1
