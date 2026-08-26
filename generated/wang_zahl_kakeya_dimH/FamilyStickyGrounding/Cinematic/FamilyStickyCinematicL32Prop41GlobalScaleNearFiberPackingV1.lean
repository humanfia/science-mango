import FamilyStickyCinematicL32ProjectedCoverCenterFloorGridOverlapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPositiveCenterGlobalScaleFarTubeV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ProjectedCoverCenterFloorGridOverlapV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterGlobalScaleFarTubeV1
open FamilyStickyCinematicL32Prop41GlobalScaleSelectedHighPairBridgeV1
open FamilyStickyRandomFiniteFloorParameterNetV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyPyzActualPositiveCenterHighPairCarrierV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Explicit three-coordinate packing of a global-scale coefficient fibre

The reduced tube coefficient distance is the `l1` distance of the three
actual projected coefficients `(a,b,d)`.  A family separated by
`separation` therefore injects into the floor grid of mesh
`separation / 3`.  Restricting the family to a coefficient ball of radius
`bound` gives the explicit finite cap below.  The ratio `bound / separation`
is retained in the cap; it is not replaced by a dimension-only constant.
-/

/-- A deliberately one-larger-than-exact three-dimensional floor-grid cap.
The final `+ 1` makes positivity immediate even before simplifying the
integer interval length. -/
noncomputable def projectedCoefficientPackingCap
    (separation bound : Real) : Nat :=
  ((Int.floor (bound / (separation / 3)) + 1 -
      Int.floor (-bound / (separation / 3))).toNat) ^ 3 + 1

theorem projectedCoefficientPackingCap_pos
    (separation bound : Real) :
    0 < projectedCoefficientPackingCap separation bound := by
  unfold projectedCoefficientPackingCap
  omega

/-- A finite family which is pairwise `separation`-apart in the genuine
projected coefficient metric has at most the displayed floor-grid cap inside
any open coefficient ball of radius `bound`. -/
theorem projectedCoefficientBall_card_lt_packingCap
    {radius : NNReal} (family : Finset (Tube radius))
    {separation bound : Real} (hseparation : 0 < separation)
    (hpairwise : forall T, T ∈ family -> forall U, U ∈ family -> T ≠ U ->
      separation <= projectedTubePairCoefficientDistance T U)
    (center : Tube radius) :
    (family.filter fun T =>
      projectedTubePairCoefficientDistance T center < bound).card <
        projectedCoefficientPackingCap separation bound := by
  classical
  let near := family.filter fun T =>
    projectedTubePairCoefficientDistance T center < bound
  let NearTube := {T // T ∈ near}
  let coord : NearTube -> Fin 3 -> Real := fun T i =>
    projectedCoefficientOffsetCoordinate center T.1 i
  have hmesh : 0 < separation / 3 := by positivity
  have hcoordBound : forall T : NearTube, forall i : Fin 3,
      |coord T i| <= bound := by
    intro T i
    have hnear : projectedTubePairCoefficientDistance center T.1 < bound := by
      have hnear' := (Finset.mem_filter.mp T.2).2
      rwa [projectedTubePairCoefficientDistance_comm] at hnear'
    exact (abs_projectedCoefficientOffsetCoordinate_le_distance
      center T.1 i).trans hnear.le
  let code : NearTube -> BoundedCode (Fin 3) (separation / 3) bound :=
    fun T => boundedFloorCode (separation / 3) bound hmesh coord
      hcoordBound T
  have hcodeInjective : Function.Injective code := by
    intro T U hcode
    apply Subtype.ext
    by_contra hne
    have hTFamily : T.1 ∈ family := (Finset.mem_filter.mp T.2).1
    have hUFamily : U.1 ∈ family := (Finset.mem_filter.mp U.2).1
    have hsep : separation <=
        projectedTubePairCoefficientDistance T.1 U.1 :=
      hpairwise T.1 hTFamily U.1 hUFamily hne
    have hfloor : floorCode (separation / 3) coord T =
        floorCode (separation / 3) coord U := by
      funext i
      exact congrArg Subtype.val (congrFun hcode i)
    have hA := abs_coord_sub_lt_of_floorCode_eq hmesh coord hfloor
      (0 : Fin 3)
    have hB := abs_coord_sub_lt_of_floorCode_eq hmesh coord hfloor
      (1 : Fin 3)
    have hD := abs_coord_sub_lt_of_floorCode_eq hmesh coord hfloor
      (2 : Fin 3)
    have hA' :
        |projectedTubeGraphA T.1 - projectedTubeGraphA U.1| <
          separation / 3 := by
      simpa [coord, projectedCoefficientOffsetCoordinate] using hA
    have hB' :
        |projectedTubeGraphB T.1 - projectedTubeGraphB U.1| <
          separation / 3 := by
      simpa [coord, projectedCoefficientOffsetCoordinate] using hB
    have hD' :
        |projectedTubeGraphD T.1 - projectedTubeGraphD U.1| <
          separation / 3 := by
      simpa [coord, projectedCoefficientOffsetCoordinate] using hD
    have hdistanceLt :
        projectedTubePairCoefficientDistance T.1 U.1 < separation := by
      simp only [projectedTubePairCoefficientDistance, coefficientDistance,
        projectedTubePairDeltaA, projectedTubePairDeltaB,
        projectedTubePairDeltaD]
      linarith
    exact (not_lt_of_ge hsep) hdistanceLt
  calc
    (family.filter fun T =>
        projectedTubePairCoefficientDistance T center < bound).card =
        Fintype.card NearTube := by simp [near, NearTube]
    _ <= Fintype.card
        (BoundedCode (Fin 3) (separation / 3) bound) :=
      Fintype.card_le_of_injective code hcodeInjective
    _ = ((Int.floor (bound / (separation / 3)) + 1 -
          Int.floor (-bound / (separation / 3))).toNat) ^
          Fintype.card (Fin 3) := by
      rw [Fintype.card_fun, Fintype.card_coe]
      unfold codeInterval
      rw [Int.card_Icc]
    _ = ((Int.floor (bound / (separation / 3)) + 1 -
          Int.floor (-bound / (separation / 3))).toNat) ^ 3 := by
      norm_num
    _ < projectedCoefficientPackingCap separation bound := by
      unfold projectedCoefficientPackingCap
      omega

/-- Indexed form of the packing bound.  Essential distinctness is used only
to identify active indices with their concrete tube image; the quantitative
packing uses the separately displayed radius separation of that image. -/
theorem activeNearCoefficientIndices_card_lt_radiusPackingCap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (active : Finset iota)
    (hradius : 0 < radius)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (himageSeparated : forall T, T ∈ activeTubeImage fine active ->
      forall U, U ∈ activeTubeImage fine active -> T ≠ U ->
        (radius : Real) <= projectedTubePairCoefficientDistance T U)
    (center : Tube radius) (bound : Real) :
    (activeNearCoefficientIndices fine active center bound).card <
      projectedCoefficientPackingCap (radius : Real) bound := by
  rw [← card_activeTubeImage_filter_near_eq_activeNearCoefficientIndices
    fine active hradius hpair center bound]
  exact projectedCoefficientBall_card_lt_packingCap
    (activeTubeImage fine active) (by exact_mod_cast hradius)
      himageSeparated center

/-- Consequently the positive-centre global-scale far-tube theorem no longer
needs an abstract same-scale near-fibre cap.  It is enough that the E2 degree
lower bound exceeds twice the explicit three-dimensional packing number.
The radius separation of the literal active image remains visible. -/
theorem exists_payload_active_halfFar_from_center_of_radiusPacking
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (hradius : 0 < radius) (hglobalScale : 0 < globalScale)
    (hdegree :
      2 * projectedCoefficientPackingCap (radius : Real) globalScale <=
        pyzE2DegreeLower payload.finalLabel)
    (hpair :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      Set.Pairwise (Y1.activeAtPoint payload.q : Set iota) (fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j)))
    (himageSeparated :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      forall T, T ∈ activeTubeImage fine (Y1.activeAtPoint payload.q) ->
        forall U, U ∈ activeTubeImage fine (Y1.activeAtPoint payload.q) ->
          T ≠ U -> (radius : Real) <=
            projectedTubePairCoefficientDistance T U)
    (center : Tube radius) :
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
    exists i, i ∈ Y1.activeAtPoint payload.q ∧
      globalScale / 2 <=
        tubePairCoefficientDistance (fine.tubes i) center := by
  dsimp only
  let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
    outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
  let active := Y1.activeAtPoint payload.q
  have hpair' : Set.Pairwise (active : Set iota) (fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j)) := by
    simpa only [Y1, active] using hpair
  have himageSeparated' : forall T, T ∈ activeTubeImage fine active ->
      forall U, U ∈ activeTubeImage fine active -> T ≠ U ->
        (radius : Real) <= projectedTubePairCoefficientDistance T U := by
    simpa only [Y1, active] using himageSeparated
  have hactiveCap : forall selectedCenter,
      selectedCenter ∈ selectedTubes (activeTubeImage fine active)
        globalScale ->
      (activeNearCoefficientIndices fine active selectedCenter
        globalScale).card <=
          projectedCoefficientPackingCap (radius : Real) globalScale := by
    intro selectedCenter _hselected
    exact (activeNearCoefficientIndices_card_lt_radiusPackingCap fine active
      hradius hpair' himageSeparated' selectedCenter globalScale).le
  simpa only [Y1, active] using
    (exists_payload_active_halfFar_from_center_of_sameScaleCap mu base hbase
      fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter tangencyExponent payload hradius hglobalScale
      (projectedCoefficientPackingCap_pos (radius : Real) globalScale)
      hdegree hpair hactiveCap center)

#print axioms projectedCoefficientPackingCap
#print axioms projectedCoefficientPackingCap_pos
#print axioms projectedCoefficientBall_card_lt_packingCap
#print axioms activeNearCoefficientIndices_card_lt_radiusPackingCap
#print axioms exists_payload_active_halfFar_from_center_of_radiusPacking

end

end FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
